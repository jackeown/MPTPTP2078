%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:11 EST 2020

% Result     : Theorem 8.02s
% Output     : CNFRefutation 8.02s
% Verified   : 
% Statistics : Number of formulae       :  329 (2512 expanded)
%              Number of clauses        :  206 ( 483 expanded)
%              Number of leaves         :   30 (1068 expanded)
%              Depth                    :   29
%              Number of atoms          : 2235 (50916 expanded)
%              Number of equality atoms :  646 (3581 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   50 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f136,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f83])).

fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f69,plain,(
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
    inference(nnf_transformation,[],[f52])).

fof(f70,plain,(
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
    inference(flattening,[],[f69])).

fof(f78,plain,(
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
     => ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK10)
          | ~ r1_tmap_1(X3,X0,X4,X6) )
        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK10)
          | r1_tmap_1(X3,X0,X4,X6) )
        & sK10 = X6
        & r1_tarski(X5,u1_struct_0(X2))
        & r2_hidden(X6,X5)
        & v3_pre_topc(X5,X1)
        & m1_subset_1(sK10,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
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
              | ~ r1_tmap_1(X3,X0,X4,sK9) )
            & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
              | r1_tmap_1(X3,X0,X4,sK9) )
            & sK9 = X7
            & r1_tarski(X5,u1_struct_0(X2))
            & r2_hidden(sK9,X5)
            & v3_pre_topc(X5,X1)
            & m1_subset_1(X7,u1_struct_0(X2)) )
        & m1_subset_1(sK9,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
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
                & r1_tarski(sK8,u1_struct_0(X2))
                & r2_hidden(X6,sK8)
                & v3_pre_topc(sK8,X1)
                & m1_subset_1(X7,u1_struct_0(X2)) )
            & m1_subset_1(X6,u1_struct_0(X3)) )
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
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
                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK7),X7)
                      | ~ r1_tmap_1(X3,X0,sK7,X6) )
                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK7),X7)
                      | r1_tmap_1(X3,X0,sK7,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(X2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,X1)
                    & m1_subset_1(X7,u1_struct_0(X2)) )
                & m1_subset_1(X6,u1_struct_0(X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(X2,X3)
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X0))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
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
                        ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK6,X2,X4),X7)
                          | ~ r1_tmap_1(sK6,X0,X4,X6) )
                        & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK6,X2,X4),X7)
                          | r1_tmap_1(sK6,X0,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(X2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,X1)
                        & m1_subset_1(X7,u1_struct_0(X2)) )
                    & m1_subset_1(X6,u1_struct_0(sK6)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X2,sK6)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK6,X1)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
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
                            ( ( ~ r1_tmap_1(sK5,X0,k3_tmap_1(X1,X0,X3,sK5,X4),X7)
                              | ~ r1_tmap_1(X3,X0,X4,X6) )
                            & ( r1_tmap_1(sK5,X0,k3_tmap_1(X1,X0,X3,sK5,X4),X7)
                              | r1_tmap_1(X3,X0,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(sK5))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,X1)
                            & m1_subset_1(X7,u1_struct_0(sK5)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_pre_topc(sK5,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK5,X1)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
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
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(sK4,X0,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,X0,X4,X6) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(sK4,X0,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,X0,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,sK4)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK4))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK4)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK4)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK4)
        & v2_pre_topc(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
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
                                  ( ( ~ r1_tmap_1(X2,sK3,k3_tmap_1(X1,sK3,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,sK3,X4,X6) )
                                  & ( r1_tmap_1(X2,sK3,k3_tmap_1(X1,sK3,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,sK3,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,
    ( ( ~ r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10)
      | ~ r1_tmap_1(sK6,sK3,sK7,sK9) )
    & ( r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10)
      | r1_tmap_1(sK6,sK3,sK7,sK9) )
    & sK9 = sK10
    & r1_tarski(sK8,u1_struct_0(sK5))
    & r2_hidden(sK9,sK8)
    & v3_pre_topc(sK8,sK4)
    & m1_subset_1(sK10,u1_struct_0(sK5))
    & m1_subset_1(sK9,u1_struct_0(sK6))
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4)))
    & m1_pre_topc(sK5,sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_pre_topc(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK4)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f70,f78,f77,f76,f75,f74,f73,f72,f71])).

fof(f121,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f79])).

fof(f125,plain,(
    m1_pre_topc(sK5,sK6) ),
    inference(cnf_transformation,[],[f79])).

fof(f15,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f105,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f123,plain,(
    v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f79])).

fof(f122,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f79])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f112,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f79])).

fof(f113,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f79])).

fof(f114,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f79])).

fof(f124,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f79])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f104,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f117,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f79])).

fof(f120,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f79])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f94,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f116,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f79])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f115,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f79])).

fof(f133,plain,
    ( r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10)
    | r1_tmap_1(sK6,sK3,sK7,sK9) ),
    inference(cnf_transformation,[],[f79])).

fof(f132,plain,(
    sK9 = sK10 ),
    inference(cnf_transformation,[],[f79])).

fof(f18,axiom,(
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

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f110,plain,(
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
    inference(cnf_transformation,[],[f68])).

fof(f141,plain,(
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
    inference(equality_resolution,[],[f110])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f118,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f79])).

fof(f128,plain,(
    m1_subset_1(sK10,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f79])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f60,f61])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f137,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f109,plain,(
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
    inference(cnf_transformation,[],[f68])).

fof(f142,plain,(
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
    inference(equality_resolution,[],[f109])).

fof(f17,axiom,(
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

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f108,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f140,plain,(
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
    inference(equality_resolution,[],[f108])).

fof(f134,plain,
    ( ~ r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10)
    | ~ r1_tmap_1(sK6,sK3,sK7,sK9) ),
    inference(cnf_transformation,[],[f79])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f119,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f79])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f54,f55])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f138,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f86])).

fof(f127,plain,(
    m1_subset_1(sK9,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f79])).

fof(f126,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f79])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( r2_hidden(X1,X3)
                      & r1_tarski(X3,X2)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f63])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK2(X0,X1,X2))
        & r1_tarski(sK2(X0,X1,X2),X2)
        & v3_pre_topc(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK2(X0,X1,X2))
                    & r1_tarski(sK2(X0,X1,X2),X2)
                    & v3_pre_topc(sK2(X0,X1,X2),X0)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f64,f65])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,X3)
      | ~ r1_tarski(X3,X2)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f129,plain,(
    v3_pre_topc(sK8,sK4) ),
    inference(cnf_transformation,[],[f79])).

fof(f11,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f139,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f131,plain,(
    r1_tarski(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f79])).

fof(f130,plain,(
    r2_hidden(sK9,sK8) ),
    inference(cnf_transformation,[],[f79])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_3082,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_45,negated_conjecture,
    ( m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_3054,plain,
    ( m1_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_41,negated_conjecture,
    ( m1_pre_topc(sK5,sK6) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_3056,plain,
    ( m1_pre_topc(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X4)) = k3_tmap_1(X3,X2,X1,X4,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_703,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X4))))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X4),X3,u1_struct_0(X2)) = k3_tmap_1(X1,X4,X0,X2,X3)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(X4) != u1_struct_0(sK3)
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_43])).

cnf(c_704,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
    | ~ v1_funct_1(sK7)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK7,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_703])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_31,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_708,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK7,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_704,c_44,c_31])).

cnf(c_709,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK7,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_708])).

cnf(c_3040,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK7,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK7)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_4454,plain,
    ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(X0),sK7,u1_struct_0(X1)) = k3_tmap_1(X2,X0,sK6,X1,sK7)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(X1,sK6) != iProver_top
    | m1_pre_topc(sK6,X2) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3040])).

cnf(c_4502,plain,
    ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK6,X0,sK7)
    | m1_pre_topc(X0,sK6) != iProver_top
    | m1_pre_topc(sK6,X1) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4454])).

cnf(c_54,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_55,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_53,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_56,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_52,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_57,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_67,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_5087,plain,
    ( v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK6,X0,sK7)
    | m1_pre_topc(X0,sK6) != iProver_top
    | m1_pre_topc(sK6,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4502,c_55,c_56,c_57,c_67])).

cnf(c_5088,plain,
    ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK6,X0,sK7)
    | m1_pre_topc(X0,sK6) != iProver_top
    | m1_pre_topc(sK6,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5087])).

cnf(c_5093,plain,
    ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(sK5)) = k3_tmap_1(X0,sK3,sK6,sK5,sK7)
    | m1_pre_topc(sK6,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3056,c_5088])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f104])).

cnf(c_751,plain,
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
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_43])).

cnf(c_752,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(sK7)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK7,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK7,X0)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X2) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_751])).

cnf(c_756,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK7,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK7,X0)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X2) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_752,c_44])).

cnf(c_757,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK7,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK7,X0)
    | u1_struct_0(X1) != u1_struct_0(sK6)
    | u1_struct_0(X2) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_756])).

cnf(c_3039,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK7,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK7,X2)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_4449,plain,
    ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(X0),sK7,u1_struct_0(X1)) = k2_tmap_1(sK6,X0,sK7,X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(X1,sK6) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3039])).

cnf(c_49,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_60,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_63,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_64,plain,
    ( m1_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_3542,plain,
    ( ~ m1_pre_topc(X0,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK6)
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(X1),sK7,u1_struct_0(X0)) = k2_tmap_1(sK6,X1,sK7,X0)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_757])).

cnf(c_3543,plain,
    ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(X0),sK7,u1_struct_0(X1)) = k2_tmap_1(sK6,X0,sK7,X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | m1_pre_topc(X1,sK6) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3542])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3360,plain,
    ( ~ m1_pre_topc(sK6,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3625,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_3360])).

cnf(c_3626,plain,
    ( m1_pre_topc(sK6,sK4) != iProver_top
    | l1_pre_topc(sK6) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3625])).

cnf(c_1906,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4188,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1906])).

cnf(c_4491,plain,
    ( l1_pre_topc(X0) != iProver_top
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(X0),sK7,u1_struct_0(X1)) = k2_tmap_1(sK6,X0,sK7,X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(X1,sK6) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4449,c_60,c_63,c_64,c_3543,c_3626,c_4188])).

cnf(c_4492,plain,
    ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(X0),sK7,u1_struct_0(X1)) = k2_tmap_1(sK6,X0,sK7,X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(X1,sK6) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_4491])).

cnf(c_4497,plain,
    ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(X0)) = k2_tmap_1(sK6,sK3,sK7,X0)
    | m1_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4492])).

cnf(c_50,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_59,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3745,plain,
    ( ~ m1_pre_topc(sK6,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4522,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | v2_pre_topc(sK6)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_3745])).

cnf(c_4523,plain,
    ( m1_pre_topc(sK6,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK6) = iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4522])).

cnf(c_4546,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(X0)) = k2_tmap_1(sK6,sK3,sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4497,c_55,c_56,c_57,c_59,c_60,c_64,c_67,c_4523])).

cnf(c_4547,plain,
    ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(X0)) = k2_tmap_1(sK6,sK3,sK7,X0)
    | m1_pre_topc(X0,sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_4546])).

cnf(c_4552,plain,
    ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(sK5)) = k2_tmap_1(sK6,sK3,sK7,sK5) ),
    inference(superposition,[status(thm)],[c_3056,c_4547])).

cnf(c_5094,plain,
    ( k3_tmap_1(X0,sK3,sK6,sK5,sK7) = k2_tmap_1(sK6,sK3,sK7,sK5)
    | m1_pre_topc(sK6,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5093,c_4552])).

cnf(c_5195,plain,
    ( k3_tmap_1(sK4,sK3,sK6,sK5,sK7) = k2_tmap_1(sK6,sK3,sK7,sK5)
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3054,c_5094])).

cnf(c_51,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_58,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_5198,plain,
    ( k3_tmap_1(sK4,sK3,sK6,sK5,sK7) = k2_tmap_1(sK6,sK3,sK7,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5195,c_58,c_59,c_60])).

cnf(c_33,negated_conjecture,
    ( r1_tmap_1(sK6,sK3,sK7,sK9)
    | r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_3063,plain,
    ( r1_tmap_1(sK6,sK3,sK7,sK9) = iProver_top
    | r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_34,negated_conjecture,
    ( sK9 = sK10 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_3089,plain,
    ( r1_tmap_1(sK6,sK3,sK7,sK10) = iProver_top
    | r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3063,c_34])).

cnf(c_5200,plain,
    ( r1_tmap_1(sK6,sK3,sK7,sK10) = iProver_top
    | r1_tmap_1(sK5,sK3,k2_tmap_1(sK6,sK3,sK7,sK5),sK10) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5198,c_3089])).

cnf(c_29,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_853,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_43])).

cnf(c_854,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
    | r1_tmap_1(X2,X1,sK7,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v1_funct_1(sK7)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_853])).

cnf(c_858,plain,
    ( ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK7,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_854,c_44])).

cnf(c_859,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
    | r1_tmap_1(X2,X1,sK7,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_858])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_900,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
    | r1_tmap_1(X2,X1,sK7,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_859,c_16])).

cnf(c_3037,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,sK7,X2),X3) != iProver_top
    | r1_tmap_1(X0,X1,sK7,X3) = iProver_top
    | m1_connsp_2(X4,X0,X3) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | r1_tarski(X4,u1_struct_0(X2)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_900])).

cnf(c_3507,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK6,X0,sK7,X1),X2) != iProver_top
    | r1_tmap_1(sK6,X0,sK7,X2) = iProver_top
    | m1_connsp_2(X3,sK6,X2) != iProver_top
    | m1_pre_topc(X1,sK6) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(X3,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3037])).

cnf(c_8419,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r1_tarski(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X1,sK6) != iProver_top
    | m1_connsp_2(X3,sK6,X2) != iProver_top
    | r1_tmap_1(sK6,X0,sK7,X2) = iProver_top
    | r1_tmap_1(X1,X0,k2_tmap_1(sK6,X0,sK7,X1),X2) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3507,c_59,c_60,c_63,c_64,c_3626,c_4523])).

cnf(c_8420,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK6,X0,sK7,X1),X2) != iProver_top
    | r1_tmap_1(sK6,X0,sK7,X2) = iProver_top
    | m1_connsp_2(X3,sK6,X2) != iProver_top
    | m1_pre_topc(X1,sK6) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | r1_tarski(X3,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8419])).

cnf(c_8425,plain,
    ( r1_tmap_1(X0,sK3,k2_tmap_1(sK6,sK3,sK7,X0),X1) != iProver_top
    | r1_tmap_1(sK6,sK3,sK7,X1) = iProver_top
    | m1_connsp_2(X2,sK6,X1) != iProver_top
    | m1_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | r1_tarski(X2,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_8420])).

cnf(c_31566,plain,
    ( v2_struct_0(X0) = iProver_top
    | r1_tarski(X2,u1_struct_0(X0)) != iProver_top
    | r1_tmap_1(X0,sK3,k2_tmap_1(sK6,sK3,sK7,X0),X1) != iProver_top
    | r1_tmap_1(sK6,sK3,sK7,X1) = iProver_top
    | m1_connsp_2(X2,sK6,X1) != iProver_top
    | m1_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8425,c_55,c_56,c_57,c_67])).

cnf(c_31567,plain,
    ( r1_tmap_1(X0,sK3,k2_tmap_1(sK6,sK3,sK7,X0),X1) != iProver_top
    | r1_tmap_1(sK6,sK3,sK7,X1) = iProver_top
    | m1_connsp_2(X2,sK6,X1) != iProver_top
    | m1_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r1_tarski(X2,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_31566])).

cnf(c_31572,plain,
    ( r1_tmap_1(sK6,sK3,sK7,sK10) = iProver_top
    | m1_connsp_2(X0,sK6,sK10) != iProver_top
    | m1_pre_topc(sK5,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5200,c_31567])).

cnf(c_48,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_61,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_68,plain,
    ( m1_pre_topc(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_71,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_4044,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4045,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4044])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_4838,plain,
    ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4839,plain,
    ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4838])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_4033,plain,
    ( ~ m1_pre_topc(X0,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5225,plain,
    ( ~ m1_pre_topc(sK5,sK6)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_4033])).

cnf(c_5226,plain,
    ( m1_pre_topc(sK5,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5225])).

cnf(c_30,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_28,plain,
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
    inference(cnf_transformation,[],[f140])).

cnf(c_283,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_28])).

cnf(c_284,plain,
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
    inference(renaming,[status(thm)],[c_283])).

cnf(c_796,plain,
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
    | u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_284,c_43])).

cnf(c_797,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK7,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK7)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_796])).

cnf(c_801,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK7,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_797,c_44])).

cnf(c_802,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK7,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_801])).

cnf(c_837,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK7,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_802,c_16])).

cnf(c_3038,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,sK7,X2),X3) = iProver_top
    | r1_tmap_1(X0,X1,sK7,X3) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_837])).

cnf(c_4116,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK6,X0,sK7,X1),X2) = iProver_top
    | r1_tmap_1(sK6,X0,sK7,X2) != iProver_top
    | m1_pre_topc(X1,sK6) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3038])).

cnf(c_3560,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(sK6,X1,sK7,X0),X2)
    | ~ r1_tmap_1(sK6,X1,sK7,X2)
    | ~ m1_pre_topc(X0,sK6)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK6)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | u1_struct_0(sK6) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_3561,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK6,X0,sK7,X1),X2) = iProver_top
    | r1_tmap_1(sK6,X0,sK7,X2) != iProver_top
    | m1_pre_topc(X1,sK6) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3560])).

cnf(c_5963,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X1,sK6) != iProver_top
    | r1_tmap_1(sK6,X0,sK7,X2) != iProver_top
    | r1_tmap_1(X1,X0,k2_tmap_1(sK6,X0,sK7,X1),X2) = iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4116,c_59,c_60,c_63,c_64,c_3561,c_3626,c_4188,c_4523])).

cnf(c_5964,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK6,X0,sK7,X1),X2) = iProver_top
    | r1_tmap_1(sK6,X0,sK7,X2) != iProver_top
    | m1_pre_topc(X1,sK6) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5963])).

cnf(c_5969,plain,
    ( r1_tmap_1(X0,sK3,k2_tmap_1(sK6,sK3,sK7,X0),X1) = iProver_top
    | r1_tmap_1(sK6,sK3,sK7,X1) != iProver_top
    | m1_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5964])).

cnf(c_14677,plain,
    ( v2_struct_0(X0) = iProver_top
    | r1_tmap_1(X0,sK3,k2_tmap_1(sK6,sK3,sK7,X0),X1) = iProver_top
    | r1_tmap_1(sK6,sK3,sK7,X1) != iProver_top
    | m1_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5969,c_55,c_56,c_57,c_67])).

cnf(c_14678,plain,
    ( r1_tmap_1(X0,sK3,k2_tmap_1(sK6,sK3,sK7,X0),X1) = iProver_top
    | r1_tmap_1(sK6,sK3,sK7,X1) != iProver_top
    | m1_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_14677])).

cnf(c_32,negated_conjecture,
    ( ~ r1_tmap_1(sK6,sK3,sK7,sK9)
    | ~ r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_3064,plain,
    ( r1_tmap_1(sK6,sK3,sK7,sK9) != iProver_top
    | r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3090,plain,
    ( r1_tmap_1(sK6,sK3,sK7,sK10) != iProver_top
    | r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3064,c_34])).

cnf(c_5201,plain,
    ( r1_tmap_1(sK6,sK3,sK7,sK10) != iProver_top
    | r1_tmap_1(sK5,sK3,k2_tmap_1(sK6,sK3,sK7,sK5),sK10) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5198,c_3090])).

cnf(c_14683,plain,
    ( r1_tmap_1(sK6,sK3,sK7,sK10) != iProver_top
    | m1_pre_topc(sK5,sK6) != iProver_top
    | m1_subset_1(sK10,u1_struct_0(sK5)) != iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_14678,c_5201])).

cnf(c_33042,plain,
    ( r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
    | m1_connsp_2(X0,sK6,sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31572,c_60,c_61,c_64,c_68,c_71,c_3626,c_4045,c_4839,c_5226,c_14683])).

cnf(c_33043,plain,
    ( m1_connsp_2(X0,sK6,sK10) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_33042])).

cnf(c_33048,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK6,sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_3082,c_33043])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_3067,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6667,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK6,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK6),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3054,c_3067])).

cnf(c_6765,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK6,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK6),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6667,c_59,c_60])).

cnf(c_47,negated_conjecture,
    ( m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3052,plain,
    ( m1_pre_topc(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_6668,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK5,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK5),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3052,c_3067])).

cnf(c_6777,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK5,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK5),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6668,c_59,c_60])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3077,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3079,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3084,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5355,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_zfmisc_1(X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3079,c_3084])).

cnf(c_10050,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3077,c_5355])).

cnf(c_10890,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK5,X0) != iProver_top
    | r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(u1_struct_0(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6777,c_10050])).

cnf(c_11436,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK6,X0) != iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top
    | m1_pre_topc(sK5,sK6) != iProver_top
    | r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6765,c_10890])).

cnf(c_12381,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK6,X0) != iProver_top
    | r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11436,c_64,c_68])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_3078,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12391,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK6,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK5),u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12381,c_3078])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_3058,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3088,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3058,c_34])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_3057,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_3072,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6200,plain,
    ( m1_pre_topc(sK4,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3057,c_3072])).

cnf(c_6397,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6200,c_3072])).

cnf(c_118,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9484,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6397,c_118])).

cnf(c_9485,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK4,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9484])).

cnf(c_9488,plain,
    ( m1_pre_topc(sK4,sK5) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3056,c_9485])).

cnf(c_9630,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_pre_topc(sK4,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9488,c_60,c_64,c_3626])).

cnf(c_9631,plain,
    ( m1_pre_topc(sK4,sK5) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(renaming,[status(thm)],[c_9630])).

cnf(c_3076,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4254,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3079,c_3076])).

cnf(c_19,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3068,plain,
    ( m1_connsp_2(X0,X1,X2) = iProver_top
    | v3_pre_topc(X3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r1_tarski(X3,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7539,plain,
    ( m1_connsp_2(X0,X1,X2) = iProver_top
    | v3_pre_topc(X3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r1_tarski(X3,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4254,c_3068])).

cnf(c_26042,plain,
    ( m1_connsp_2(X0,sK6,X1) = iProver_top
    | v3_pre_topc(sK8,sK6) != iProver_top
    | m1_pre_topc(sK4,sK5) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
    | r1_tarski(sK8,X0) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9631,c_7539])).

cnf(c_69,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_37,negated_conjecture,
    ( v3_pre_topc(sK8,sK4) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_72,plain,
    ( v3_pre_topc(sK8,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4024,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4025,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4024])).

cnf(c_4823,plain,
    ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r1_tarski(X0,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4824,plain,
    ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4823])).

cnf(c_17,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_4697,plain,
    ( v3_pre_topc(sK8,X0)
    | ~ v3_pre_topc(sK8,sK4)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_6056,plain,
    ( v3_pre_topc(sK8,sK6)
    | ~ v3_pre_topc(sK8,sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_4697])).

cnf(c_6057,plain,
    ( v3_pre_topc(sK8,sK6) = iProver_top
    | v3_pre_topc(sK8,sK4) != iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6056])).

cnf(c_9548,plain,
    ( ~ m1_pre_topc(sK5,sK6)
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_5225])).

cnf(c_9549,plain,
    ( m1_pre_topc(sK5,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9548])).

cnf(c_10549,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK8,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_4044])).

cnf(c_10554,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | r2_hidden(sK8,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10549])).

cnf(c_35,negated_conjecture,
    ( r1_tarski(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_3062,plain,
    ( r1_tarski(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_10888,plain,
    ( r2_hidden(sK8,k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(u1_struct_0(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3062,c_10050])).

cnf(c_11045,plain,
    ( r2_hidden(sK8,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3082,c_10888])).

cnf(c_3171,plain,
    ( m1_connsp_2(X0,sK6,X1)
    | ~ v3_pre_topc(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_18927,plain,
    ( m1_connsp_2(X0,sK6,X1)
    | ~ v3_pre_topc(sK8,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X1,sK8)
    | ~ r1_tarski(sK8,X0)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_3171])).

cnf(c_18928,plain,
    ( m1_connsp_2(X0,sK6,X1) = iProver_top
    | v3_pre_topc(sK8,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r1_tarski(sK8,X0) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18927])).

cnf(c_28947,plain,
    ( r1_tarski(sK8,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | m1_connsp_2(X0,sK6,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26042,c_59,c_60,c_63,c_64,c_68,c_69,c_72,c_3626,c_4025,c_4523,c_4824,c_6057,c_9549,c_10554,c_11045,c_18928])).

cnf(c_28948,plain,
    ( m1_connsp_2(X0,sK6,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
    | r1_tarski(sK8,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_28947])).

cnf(c_28955,plain,
    ( m1_connsp_2(X0,sK6,sK10) = iProver_top
    | r2_hidden(sK10,sK8) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
    | r1_tarski(sK8,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3088,c_28948])).

cnf(c_36,negated_conjecture,
    ( r2_hidden(sK9,sK8) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_3061,plain,
    ( r2_hidden(sK9,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3087,plain,
    ( r2_hidden(sK10,sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3061,c_34])).

cnf(c_29669,plain,
    ( m1_connsp_2(X0,sK6,sK10) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
    | r1_tarski(sK8,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28955,c_3087])).

cnf(c_29683,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK6,sK10) = iProver_top
    | m1_pre_topc(sK6,sK6) != iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top
    | r1_tarski(sK8,u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12391,c_29669])).

cnf(c_6026,plain,
    ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6027,plain,
    ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6026])).

cnf(c_27,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3636,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK6,X1)
    | m1_pre_topc(sK6,X0)
    | ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_4247,plain,
    ( ~ m1_pre_topc(X0,sK4)
    | m1_pre_topc(sK6,X0)
    | ~ m1_pre_topc(sK6,sK4)
    | ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(X0))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_3636])).

cnf(c_4435,plain,
    ( m1_pre_topc(sK6,sK6)
    | ~ m1_pre_topc(sK6,sK4)
    | ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_4247])).

cnf(c_4436,plain,
    ( m1_pre_topc(sK6,sK6) = iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top
    | r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4435])).

cnf(c_74,plain,
    ( r1_tarski(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33048,c_29683,c_6027,c_4436,c_74,c_64,c_60,c_59])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.02/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.02/1.49  
% 8.02/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.02/1.49  
% 8.02/1.49  ------  iProver source info
% 8.02/1.49  
% 8.02/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.02/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.02/1.49  git: non_committed_changes: false
% 8.02/1.49  git: last_make_outside_of_git: false
% 8.02/1.49  
% 8.02/1.49  ------ 
% 8.02/1.49  
% 8.02/1.49  ------ Input Options
% 8.02/1.49  
% 8.02/1.49  --out_options                           all
% 8.02/1.49  --tptp_safe_out                         true
% 8.02/1.49  --problem_path                          ""
% 8.02/1.49  --include_path                          ""
% 8.02/1.49  --clausifier                            res/vclausify_rel
% 8.02/1.49  --clausifier_options                    ""
% 8.02/1.49  --stdin                                 false
% 8.02/1.49  --stats_out                             all
% 8.02/1.49  
% 8.02/1.49  ------ General Options
% 8.02/1.49  
% 8.02/1.49  --fof                                   false
% 8.02/1.49  --time_out_real                         305.
% 8.02/1.49  --time_out_virtual                      -1.
% 8.02/1.49  --symbol_type_check                     false
% 8.02/1.49  --clausify_out                          false
% 8.02/1.49  --sig_cnt_out                           false
% 8.02/1.49  --trig_cnt_out                          false
% 8.02/1.49  --trig_cnt_out_tolerance                1.
% 8.02/1.49  --trig_cnt_out_sk_spl                   false
% 8.02/1.49  --abstr_cl_out                          false
% 8.02/1.49  
% 8.02/1.49  ------ Global Options
% 8.02/1.49  
% 8.02/1.49  --schedule                              default
% 8.02/1.49  --add_important_lit                     false
% 8.02/1.49  --prop_solver_per_cl                    1000
% 8.02/1.49  --min_unsat_core                        false
% 8.02/1.49  --soft_assumptions                      false
% 8.02/1.49  --soft_lemma_size                       3
% 8.02/1.49  --prop_impl_unit_size                   0
% 8.02/1.49  --prop_impl_unit                        []
% 8.02/1.49  --share_sel_clauses                     true
% 8.02/1.49  --reset_solvers                         false
% 8.02/1.49  --bc_imp_inh                            [conj_cone]
% 8.02/1.49  --conj_cone_tolerance                   3.
% 8.02/1.49  --extra_neg_conj                        none
% 8.02/1.49  --large_theory_mode                     true
% 8.02/1.49  --prolific_symb_bound                   200
% 8.02/1.49  --lt_threshold                          2000
% 8.02/1.49  --clause_weak_htbl                      true
% 8.02/1.49  --gc_record_bc_elim                     false
% 8.02/1.49  
% 8.02/1.49  ------ Preprocessing Options
% 8.02/1.49  
% 8.02/1.49  --preprocessing_flag                    true
% 8.02/1.49  --time_out_prep_mult                    0.1
% 8.02/1.49  --splitting_mode                        input
% 8.02/1.49  --splitting_grd                         true
% 8.02/1.49  --splitting_cvd                         false
% 8.02/1.49  --splitting_cvd_svl                     false
% 8.02/1.49  --splitting_nvd                         32
% 8.02/1.49  --sub_typing                            true
% 8.02/1.49  --prep_gs_sim                           true
% 8.02/1.49  --prep_unflatten                        true
% 8.02/1.49  --prep_res_sim                          true
% 8.02/1.49  --prep_upred                            true
% 8.02/1.49  --prep_sem_filter                       exhaustive
% 8.02/1.49  --prep_sem_filter_out                   false
% 8.02/1.49  --pred_elim                             true
% 8.02/1.49  --res_sim_input                         true
% 8.02/1.49  --eq_ax_congr_red                       true
% 8.02/1.49  --pure_diseq_elim                       true
% 8.02/1.49  --brand_transform                       false
% 8.02/1.49  --non_eq_to_eq                          false
% 8.02/1.49  --prep_def_merge                        true
% 8.02/1.49  --prep_def_merge_prop_impl              false
% 8.02/1.49  --prep_def_merge_mbd                    true
% 8.02/1.49  --prep_def_merge_tr_red                 false
% 8.02/1.49  --prep_def_merge_tr_cl                  false
% 8.02/1.49  --smt_preprocessing                     true
% 8.02/1.49  --smt_ac_axioms                         fast
% 8.02/1.49  --preprocessed_out                      false
% 8.02/1.49  --preprocessed_stats                    false
% 8.02/1.49  
% 8.02/1.49  ------ Abstraction refinement Options
% 8.02/1.49  
% 8.02/1.49  --abstr_ref                             []
% 8.02/1.49  --abstr_ref_prep                        false
% 8.02/1.49  --abstr_ref_until_sat                   false
% 8.02/1.49  --abstr_ref_sig_restrict                funpre
% 8.02/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.02/1.49  --abstr_ref_under                       []
% 8.02/1.49  
% 8.02/1.49  ------ SAT Options
% 8.02/1.49  
% 8.02/1.49  --sat_mode                              false
% 8.02/1.49  --sat_fm_restart_options                ""
% 8.02/1.49  --sat_gr_def                            false
% 8.02/1.49  --sat_epr_types                         true
% 8.02/1.49  --sat_non_cyclic_types                  false
% 8.02/1.49  --sat_finite_models                     false
% 8.02/1.49  --sat_fm_lemmas                         false
% 8.02/1.49  --sat_fm_prep                           false
% 8.02/1.49  --sat_fm_uc_incr                        true
% 8.02/1.49  --sat_out_model                         small
% 8.02/1.49  --sat_out_clauses                       false
% 8.02/1.49  
% 8.02/1.49  ------ QBF Options
% 8.02/1.49  
% 8.02/1.49  --qbf_mode                              false
% 8.02/1.49  --qbf_elim_univ                         false
% 8.02/1.49  --qbf_dom_inst                          none
% 8.02/1.49  --qbf_dom_pre_inst                      false
% 8.02/1.49  --qbf_sk_in                             false
% 8.02/1.49  --qbf_pred_elim                         true
% 8.02/1.49  --qbf_split                             512
% 8.02/1.49  
% 8.02/1.49  ------ BMC1 Options
% 8.02/1.49  
% 8.02/1.49  --bmc1_incremental                      false
% 8.02/1.49  --bmc1_axioms                           reachable_all
% 8.02/1.49  --bmc1_min_bound                        0
% 8.02/1.49  --bmc1_max_bound                        -1
% 8.02/1.49  --bmc1_max_bound_default                -1
% 8.02/1.49  --bmc1_symbol_reachability              true
% 8.02/1.49  --bmc1_property_lemmas                  false
% 8.02/1.49  --bmc1_k_induction                      false
% 8.02/1.49  --bmc1_non_equiv_states                 false
% 8.02/1.49  --bmc1_deadlock                         false
% 8.02/1.49  --bmc1_ucm                              false
% 8.02/1.49  --bmc1_add_unsat_core                   none
% 8.02/1.49  --bmc1_unsat_core_children              false
% 8.02/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.02/1.49  --bmc1_out_stat                         full
% 8.02/1.49  --bmc1_ground_init                      false
% 8.02/1.49  --bmc1_pre_inst_next_state              false
% 8.02/1.49  --bmc1_pre_inst_state                   false
% 8.02/1.49  --bmc1_pre_inst_reach_state             false
% 8.02/1.49  --bmc1_out_unsat_core                   false
% 8.02/1.49  --bmc1_aig_witness_out                  false
% 8.02/1.49  --bmc1_verbose                          false
% 8.02/1.49  --bmc1_dump_clauses_tptp                false
% 8.02/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.02/1.49  --bmc1_dump_file                        -
% 8.02/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.02/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.02/1.49  --bmc1_ucm_extend_mode                  1
% 8.02/1.49  --bmc1_ucm_init_mode                    2
% 8.02/1.49  --bmc1_ucm_cone_mode                    none
% 8.02/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.02/1.49  --bmc1_ucm_relax_model                  4
% 8.02/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.02/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.02/1.49  --bmc1_ucm_layered_model                none
% 8.02/1.49  --bmc1_ucm_max_lemma_size               10
% 8.02/1.49  
% 8.02/1.49  ------ AIG Options
% 8.02/1.49  
% 8.02/1.49  --aig_mode                              false
% 8.02/1.49  
% 8.02/1.49  ------ Instantiation Options
% 8.02/1.49  
% 8.02/1.49  --instantiation_flag                    true
% 8.02/1.49  --inst_sos_flag                         true
% 8.02/1.49  --inst_sos_phase                        true
% 8.02/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.02/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.02/1.49  --inst_lit_sel_side                     num_symb
% 8.02/1.49  --inst_solver_per_active                1400
% 8.02/1.49  --inst_solver_calls_frac                1.
% 8.02/1.49  --inst_passive_queue_type               priority_queues
% 8.02/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.02/1.49  --inst_passive_queues_freq              [25;2]
% 8.02/1.49  --inst_dismatching                      true
% 8.02/1.49  --inst_eager_unprocessed_to_passive     true
% 8.02/1.49  --inst_prop_sim_given                   true
% 8.02/1.49  --inst_prop_sim_new                     false
% 8.02/1.49  --inst_subs_new                         false
% 8.02/1.49  --inst_eq_res_simp                      false
% 8.02/1.49  --inst_subs_given                       false
% 8.02/1.49  --inst_orphan_elimination               true
% 8.02/1.49  --inst_learning_loop_flag               true
% 8.02/1.49  --inst_learning_start                   3000
% 8.02/1.49  --inst_learning_factor                  2
% 8.02/1.49  --inst_start_prop_sim_after_learn       3
% 8.02/1.49  --inst_sel_renew                        solver
% 8.02/1.49  --inst_lit_activity_flag                true
% 8.02/1.49  --inst_restr_to_given                   false
% 8.02/1.49  --inst_activity_threshold               500
% 8.02/1.49  --inst_out_proof                        true
% 8.02/1.49  
% 8.02/1.49  ------ Resolution Options
% 8.02/1.49  
% 8.02/1.49  --resolution_flag                       true
% 8.02/1.49  --res_lit_sel                           adaptive
% 8.02/1.49  --res_lit_sel_side                      none
% 8.02/1.49  --res_ordering                          kbo
% 8.02/1.49  --res_to_prop_solver                    active
% 8.02/1.49  --res_prop_simpl_new                    false
% 8.02/1.49  --res_prop_simpl_given                  true
% 8.02/1.49  --res_passive_queue_type                priority_queues
% 8.02/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.02/1.49  --res_passive_queues_freq               [15;5]
% 8.02/1.49  --res_forward_subs                      full
% 8.02/1.49  --res_backward_subs                     full
% 8.02/1.49  --res_forward_subs_resolution           true
% 8.02/1.49  --res_backward_subs_resolution          true
% 8.02/1.49  --res_orphan_elimination                true
% 8.02/1.49  --res_time_limit                        2.
% 8.02/1.49  --res_out_proof                         true
% 8.02/1.49  
% 8.02/1.49  ------ Superposition Options
% 8.02/1.49  
% 8.02/1.49  --superposition_flag                    true
% 8.02/1.49  --sup_passive_queue_type                priority_queues
% 8.02/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.02/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.02/1.49  --demod_completeness_check              fast
% 8.02/1.49  --demod_use_ground                      true
% 8.02/1.49  --sup_to_prop_solver                    passive
% 8.02/1.49  --sup_prop_simpl_new                    true
% 8.02/1.49  --sup_prop_simpl_given                  true
% 8.02/1.49  --sup_fun_splitting                     true
% 8.02/1.49  --sup_smt_interval                      50000
% 8.02/1.49  
% 8.02/1.49  ------ Superposition Simplification Setup
% 8.02/1.49  
% 8.02/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.02/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.02/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.02/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.02/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.02/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.02/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.02/1.49  --sup_immed_triv                        [TrivRules]
% 8.02/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.02/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.02/1.49  --sup_immed_bw_main                     []
% 8.02/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.02/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.02/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.02/1.49  --sup_input_bw                          []
% 8.02/1.49  
% 8.02/1.49  ------ Combination Options
% 8.02/1.49  
% 8.02/1.49  --comb_res_mult                         3
% 8.02/1.49  --comb_sup_mult                         2
% 8.02/1.49  --comb_inst_mult                        10
% 8.02/1.49  
% 8.02/1.49  ------ Debug Options
% 8.02/1.49  
% 8.02/1.49  --dbg_backtrace                         false
% 8.02/1.49  --dbg_dump_prop_clauses                 false
% 8.02/1.49  --dbg_dump_prop_clauses_file            -
% 8.02/1.49  --dbg_out_stat                          false
% 8.02/1.49  ------ Parsing...
% 8.02/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.02/1.49  
% 8.02/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 8.02/1.49  
% 8.02/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.02/1.49  
% 8.02/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.02/1.49  ------ Proving...
% 8.02/1.49  ------ Problem Properties 
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  clauses                                 51
% 8.02/1.49  conjectures                             21
% 8.02/1.49  EPR                                     21
% 8.02/1.49  Horn                                    37
% 8.02/1.49  unary                                   20
% 8.02/1.49  binary                                  8
% 8.02/1.49  lits                                    185
% 8.02/1.49  lits eq                                 14
% 8.02/1.49  fd_pure                                 0
% 8.02/1.49  fd_pseudo                               0
% 8.02/1.49  fd_cond                                 0
% 8.02/1.49  fd_pseudo_cond                          3
% 8.02/1.49  AC symbols                              0
% 8.02/1.49  
% 8.02/1.49  ------ Schedule dynamic 5 is on 
% 8.02/1.49  
% 8.02/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  ------ 
% 8.02/1.49  Current options:
% 8.02/1.49  ------ 
% 8.02/1.49  
% 8.02/1.49  ------ Input Options
% 8.02/1.49  
% 8.02/1.49  --out_options                           all
% 8.02/1.49  --tptp_safe_out                         true
% 8.02/1.49  --problem_path                          ""
% 8.02/1.49  --include_path                          ""
% 8.02/1.49  --clausifier                            res/vclausify_rel
% 8.02/1.49  --clausifier_options                    ""
% 8.02/1.49  --stdin                                 false
% 8.02/1.49  --stats_out                             all
% 8.02/1.49  
% 8.02/1.49  ------ General Options
% 8.02/1.49  
% 8.02/1.49  --fof                                   false
% 8.02/1.49  --time_out_real                         305.
% 8.02/1.49  --time_out_virtual                      -1.
% 8.02/1.49  --symbol_type_check                     false
% 8.02/1.49  --clausify_out                          false
% 8.02/1.49  --sig_cnt_out                           false
% 8.02/1.49  --trig_cnt_out                          false
% 8.02/1.49  --trig_cnt_out_tolerance                1.
% 8.02/1.49  --trig_cnt_out_sk_spl                   false
% 8.02/1.49  --abstr_cl_out                          false
% 8.02/1.49  
% 8.02/1.49  ------ Global Options
% 8.02/1.49  
% 8.02/1.49  --schedule                              default
% 8.02/1.49  --add_important_lit                     false
% 8.02/1.49  --prop_solver_per_cl                    1000
% 8.02/1.49  --min_unsat_core                        false
% 8.02/1.49  --soft_assumptions                      false
% 8.02/1.49  --soft_lemma_size                       3
% 8.02/1.49  --prop_impl_unit_size                   0
% 8.02/1.49  --prop_impl_unit                        []
% 8.02/1.49  --share_sel_clauses                     true
% 8.02/1.49  --reset_solvers                         false
% 8.02/1.49  --bc_imp_inh                            [conj_cone]
% 8.02/1.49  --conj_cone_tolerance                   3.
% 8.02/1.49  --extra_neg_conj                        none
% 8.02/1.49  --large_theory_mode                     true
% 8.02/1.49  --prolific_symb_bound                   200
% 8.02/1.49  --lt_threshold                          2000
% 8.02/1.49  --clause_weak_htbl                      true
% 8.02/1.49  --gc_record_bc_elim                     false
% 8.02/1.49  
% 8.02/1.49  ------ Preprocessing Options
% 8.02/1.49  
% 8.02/1.49  --preprocessing_flag                    true
% 8.02/1.49  --time_out_prep_mult                    0.1
% 8.02/1.49  --splitting_mode                        input
% 8.02/1.49  --splitting_grd                         true
% 8.02/1.49  --splitting_cvd                         false
% 8.02/1.49  --splitting_cvd_svl                     false
% 8.02/1.49  --splitting_nvd                         32
% 8.02/1.49  --sub_typing                            true
% 8.02/1.49  --prep_gs_sim                           true
% 8.02/1.49  --prep_unflatten                        true
% 8.02/1.49  --prep_res_sim                          true
% 8.02/1.49  --prep_upred                            true
% 8.02/1.49  --prep_sem_filter                       exhaustive
% 8.02/1.49  --prep_sem_filter_out                   false
% 8.02/1.49  --pred_elim                             true
% 8.02/1.49  --res_sim_input                         true
% 8.02/1.49  --eq_ax_congr_red                       true
% 8.02/1.49  --pure_diseq_elim                       true
% 8.02/1.49  --brand_transform                       false
% 8.02/1.49  --non_eq_to_eq                          false
% 8.02/1.49  --prep_def_merge                        true
% 8.02/1.49  --prep_def_merge_prop_impl              false
% 8.02/1.49  --prep_def_merge_mbd                    true
% 8.02/1.49  --prep_def_merge_tr_red                 false
% 8.02/1.49  --prep_def_merge_tr_cl                  false
% 8.02/1.49  --smt_preprocessing                     true
% 8.02/1.49  --smt_ac_axioms                         fast
% 8.02/1.49  --preprocessed_out                      false
% 8.02/1.49  --preprocessed_stats                    false
% 8.02/1.49  
% 8.02/1.49  ------ Abstraction refinement Options
% 8.02/1.49  
% 8.02/1.49  --abstr_ref                             []
% 8.02/1.49  --abstr_ref_prep                        false
% 8.02/1.49  --abstr_ref_until_sat                   false
% 8.02/1.49  --abstr_ref_sig_restrict                funpre
% 8.02/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.02/1.49  --abstr_ref_under                       []
% 8.02/1.49  
% 8.02/1.49  ------ SAT Options
% 8.02/1.49  
% 8.02/1.49  --sat_mode                              false
% 8.02/1.49  --sat_fm_restart_options                ""
% 8.02/1.49  --sat_gr_def                            false
% 8.02/1.49  --sat_epr_types                         true
% 8.02/1.49  --sat_non_cyclic_types                  false
% 8.02/1.49  --sat_finite_models                     false
% 8.02/1.49  --sat_fm_lemmas                         false
% 8.02/1.49  --sat_fm_prep                           false
% 8.02/1.49  --sat_fm_uc_incr                        true
% 8.02/1.49  --sat_out_model                         small
% 8.02/1.49  --sat_out_clauses                       false
% 8.02/1.49  
% 8.02/1.49  ------ QBF Options
% 8.02/1.49  
% 8.02/1.49  --qbf_mode                              false
% 8.02/1.49  --qbf_elim_univ                         false
% 8.02/1.49  --qbf_dom_inst                          none
% 8.02/1.49  --qbf_dom_pre_inst                      false
% 8.02/1.49  --qbf_sk_in                             false
% 8.02/1.49  --qbf_pred_elim                         true
% 8.02/1.49  --qbf_split                             512
% 8.02/1.49  
% 8.02/1.49  ------ BMC1 Options
% 8.02/1.49  
% 8.02/1.49  --bmc1_incremental                      false
% 8.02/1.49  --bmc1_axioms                           reachable_all
% 8.02/1.49  --bmc1_min_bound                        0
% 8.02/1.49  --bmc1_max_bound                        -1
% 8.02/1.49  --bmc1_max_bound_default                -1
% 8.02/1.49  --bmc1_symbol_reachability              true
% 8.02/1.49  --bmc1_property_lemmas                  false
% 8.02/1.49  --bmc1_k_induction                      false
% 8.02/1.49  --bmc1_non_equiv_states                 false
% 8.02/1.49  --bmc1_deadlock                         false
% 8.02/1.49  --bmc1_ucm                              false
% 8.02/1.49  --bmc1_add_unsat_core                   none
% 8.02/1.49  --bmc1_unsat_core_children              false
% 8.02/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.02/1.49  --bmc1_out_stat                         full
% 8.02/1.49  --bmc1_ground_init                      false
% 8.02/1.49  --bmc1_pre_inst_next_state              false
% 8.02/1.49  --bmc1_pre_inst_state                   false
% 8.02/1.49  --bmc1_pre_inst_reach_state             false
% 8.02/1.49  --bmc1_out_unsat_core                   false
% 8.02/1.49  --bmc1_aig_witness_out                  false
% 8.02/1.49  --bmc1_verbose                          false
% 8.02/1.49  --bmc1_dump_clauses_tptp                false
% 8.02/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.02/1.49  --bmc1_dump_file                        -
% 8.02/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.02/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.02/1.49  --bmc1_ucm_extend_mode                  1
% 8.02/1.49  --bmc1_ucm_init_mode                    2
% 8.02/1.49  --bmc1_ucm_cone_mode                    none
% 8.02/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.02/1.49  --bmc1_ucm_relax_model                  4
% 8.02/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.02/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.02/1.49  --bmc1_ucm_layered_model                none
% 8.02/1.49  --bmc1_ucm_max_lemma_size               10
% 8.02/1.49  
% 8.02/1.49  ------ AIG Options
% 8.02/1.49  
% 8.02/1.49  --aig_mode                              false
% 8.02/1.49  
% 8.02/1.49  ------ Instantiation Options
% 8.02/1.49  
% 8.02/1.49  --instantiation_flag                    true
% 8.02/1.49  --inst_sos_flag                         true
% 8.02/1.49  --inst_sos_phase                        true
% 8.02/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.02/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.02/1.49  --inst_lit_sel_side                     none
% 8.02/1.49  --inst_solver_per_active                1400
% 8.02/1.49  --inst_solver_calls_frac                1.
% 8.02/1.49  --inst_passive_queue_type               priority_queues
% 8.02/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.02/1.49  --inst_passive_queues_freq              [25;2]
% 8.02/1.49  --inst_dismatching                      true
% 8.02/1.49  --inst_eager_unprocessed_to_passive     true
% 8.02/1.49  --inst_prop_sim_given                   true
% 8.02/1.49  --inst_prop_sim_new                     false
% 8.02/1.49  --inst_subs_new                         false
% 8.02/1.49  --inst_eq_res_simp                      false
% 8.02/1.49  --inst_subs_given                       false
% 8.02/1.49  --inst_orphan_elimination               true
% 8.02/1.49  --inst_learning_loop_flag               true
% 8.02/1.49  --inst_learning_start                   3000
% 8.02/1.49  --inst_learning_factor                  2
% 8.02/1.49  --inst_start_prop_sim_after_learn       3
% 8.02/1.49  --inst_sel_renew                        solver
% 8.02/1.49  --inst_lit_activity_flag                true
% 8.02/1.49  --inst_restr_to_given                   false
% 8.02/1.49  --inst_activity_threshold               500
% 8.02/1.49  --inst_out_proof                        true
% 8.02/1.49  
% 8.02/1.49  ------ Resolution Options
% 8.02/1.49  
% 8.02/1.49  --resolution_flag                       false
% 8.02/1.49  --res_lit_sel                           adaptive
% 8.02/1.49  --res_lit_sel_side                      none
% 8.02/1.49  --res_ordering                          kbo
% 8.02/1.49  --res_to_prop_solver                    active
% 8.02/1.49  --res_prop_simpl_new                    false
% 8.02/1.49  --res_prop_simpl_given                  true
% 8.02/1.49  --res_passive_queue_type                priority_queues
% 8.02/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.02/1.49  --res_passive_queues_freq               [15;5]
% 8.02/1.49  --res_forward_subs                      full
% 8.02/1.49  --res_backward_subs                     full
% 8.02/1.49  --res_forward_subs_resolution           true
% 8.02/1.49  --res_backward_subs_resolution          true
% 8.02/1.49  --res_orphan_elimination                true
% 8.02/1.49  --res_time_limit                        2.
% 8.02/1.49  --res_out_proof                         true
% 8.02/1.49  
% 8.02/1.49  ------ Superposition Options
% 8.02/1.49  
% 8.02/1.49  --superposition_flag                    true
% 8.02/1.49  --sup_passive_queue_type                priority_queues
% 8.02/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.02/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.02/1.49  --demod_completeness_check              fast
% 8.02/1.49  --demod_use_ground                      true
% 8.02/1.49  --sup_to_prop_solver                    passive
% 8.02/1.49  --sup_prop_simpl_new                    true
% 8.02/1.49  --sup_prop_simpl_given                  true
% 8.02/1.49  --sup_fun_splitting                     true
% 8.02/1.49  --sup_smt_interval                      50000
% 8.02/1.49  
% 8.02/1.49  ------ Superposition Simplification Setup
% 8.02/1.49  
% 8.02/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.02/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.02/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.02/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.02/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.02/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.02/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.02/1.49  --sup_immed_triv                        [TrivRules]
% 8.02/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.02/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.02/1.49  --sup_immed_bw_main                     []
% 8.02/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.02/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.02/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.02/1.49  --sup_input_bw                          []
% 8.02/1.49  
% 8.02/1.49  ------ Combination Options
% 8.02/1.49  
% 8.02/1.49  --comb_res_mult                         3
% 8.02/1.49  --comb_sup_mult                         2
% 8.02/1.49  --comb_inst_mult                        10
% 8.02/1.49  
% 8.02/1.49  ------ Debug Options
% 8.02/1.49  
% 8.02/1.49  --dbg_backtrace                         false
% 8.02/1.49  --dbg_dump_prop_clauses                 false
% 8.02/1.49  --dbg_dump_prop_clauses_file            -
% 8.02/1.49  --dbg_out_stat                          false
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  ------ Proving...
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  % SZS status Theorem for theBenchmark.p
% 8.02/1.49  
% 8.02/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.02/1.49  
% 8.02/1.49  fof(f2,axiom,(
% 8.02/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f57,plain,(
% 8.02/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.02/1.49    inference(nnf_transformation,[],[f2])).
% 8.02/1.49  
% 8.02/1.49  fof(f58,plain,(
% 8.02/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.02/1.49    inference(flattening,[],[f57])).
% 8.02/1.49  
% 8.02/1.49  fof(f83,plain,(
% 8.02/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 8.02/1.49    inference(cnf_transformation,[],[f58])).
% 8.02/1.49  
% 8.02/1.49  fof(f136,plain,(
% 8.02/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 8.02/1.49    inference(equality_resolution,[],[f83])).
% 8.02/1.49  
% 8.02/1.49  fof(f20,conjecture,(
% 8.02/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f21,negated_conjecture,(
% 8.02/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 8.02/1.49    inference(negated_conjecture,[],[f20])).
% 8.02/1.49  
% 8.02/1.49  fof(f51,plain,(
% 8.02/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 8.02/1.49    inference(ennf_transformation,[],[f21])).
% 8.02/1.49  
% 8.02/1.49  fof(f52,plain,(
% 8.02/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 8.02/1.49    inference(flattening,[],[f51])).
% 8.02/1.49  
% 8.02/1.49  fof(f69,plain,(
% 8.02/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 8.02/1.49    inference(nnf_transformation,[],[f52])).
% 8.02/1.49  
% 8.02/1.49  fof(f70,plain,(
% 8.02/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 8.02/1.49    inference(flattening,[],[f69])).
% 8.02/1.49  
% 8.02/1.49  fof(f78,plain,(
% 8.02/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) => ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK10) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),sK10) | r1_tmap_1(X3,X0,X4,X6)) & sK10 = X6 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(sK10,u1_struct_0(X2)))) )),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f77,plain,(
% 8.02/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) => (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,sK9)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,sK9)) & sK9 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(sK9,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(sK9,u1_struct_0(X3)))) )),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f76,plain,(
% 8.02/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(sK8,u1_struct_0(X2)) & r2_hidden(X6,sK8) & v3_pre_topc(sK8,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f75,plain,(
% 8.02/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK7),X7) | ~r1_tmap_1(X3,X0,sK7,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,sK7),X7) | r1_tmap_1(X3,X0,sK7,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(sK7))) )),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f74,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK6,X2,X4),X7) | ~r1_tmap_1(sK6,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,sK6,X2,X4),X7) | r1_tmap_1(sK6,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,sK6) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK6),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(sK6,X1) & ~v2_struct_0(sK6))) )),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f73,plain,(
% 8.02/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK5,X0,k3_tmap_1(X1,X0,X3,sK5,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(sK5,X0,k3_tmap_1(X1,X0,X3,sK5,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK5)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(sK5))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(sK5,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(sK5,X1) & ~v2_struct_0(sK5))) )),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f72,plain,(
% 8.02/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(sK4,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(sK4,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK4) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))) )),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f71,plain,(
% 8.02/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK3,k3_tmap_1(X1,sK3,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK3,X4,X6)) & (r1_tmap_1(X2,sK3,k3_tmap_1(X1,sK3,X3,X2,X4),X7) | r1_tmap_1(X3,sK3,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f79,plain,(
% 8.02/1.49    ((((((((~r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) | ~r1_tmap_1(sK6,sK3,sK7,sK9)) & (r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) | r1_tmap_1(sK6,sK3,sK7,sK9)) & sK9 = sK10 & r1_tarski(sK8,u1_struct_0(sK5)) & r2_hidden(sK9,sK8) & v3_pre_topc(sK8,sK4) & m1_subset_1(sK10,u1_struct_0(sK5))) & m1_subset_1(sK9,u1_struct_0(sK6))) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_pre_topc(sK5,sK6) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK4) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 8.02/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f70,f78,f77,f76,f75,f74,f73,f72,f71])).
% 8.02/1.49  
% 8.02/1.49  fof(f121,plain,(
% 8.02/1.49    m1_pre_topc(sK6,sK4)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f125,plain,(
% 8.02/1.49    m1_pre_topc(sK5,sK6)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f15,axiom,(
% 8.02/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f41,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.02/1.49    inference(ennf_transformation,[],[f15])).
% 8.02/1.49  
% 8.02/1.49  fof(f42,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.02/1.49    inference(flattening,[],[f41])).
% 8.02/1.49  
% 8.02/1.49  fof(f105,plain,(
% 8.02/1.49    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f42])).
% 8.02/1.49  
% 8.02/1.49  fof(f123,plain,(
% 8.02/1.49    v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK3))),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f122,plain,(
% 8.02/1.49    v1_funct_1(sK7)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f19,axiom,(
% 8.02/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f49,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.02/1.49    inference(ennf_transformation,[],[f19])).
% 8.02/1.49  
% 8.02/1.49  fof(f50,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.02/1.49    inference(flattening,[],[f49])).
% 8.02/1.49  
% 8.02/1.49  fof(f111,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f50])).
% 8.02/1.49  
% 8.02/1.49  fof(f112,plain,(
% 8.02/1.49    ~v2_struct_0(sK3)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f113,plain,(
% 8.02/1.49    v2_pre_topc(sK3)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f114,plain,(
% 8.02/1.49    l1_pre_topc(sK3)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f124,plain,(
% 8.02/1.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f14,axiom,(
% 8.02/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f39,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.02/1.49    inference(ennf_transformation,[],[f14])).
% 8.02/1.49  
% 8.02/1.49  fof(f40,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.02/1.49    inference(flattening,[],[f39])).
% 8.02/1.49  
% 8.02/1.49  fof(f104,plain,(
% 8.02/1.49    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f40])).
% 8.02/1.49  
% 8.02/1.49  fof(f117,plain,(
% 8.02/1.49    l1_pre_topc(sK4)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f120,plain,(
% 8.02/1.49    ~v2_struct_0(sK6)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f8,axiom,(
% 8.02/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f29,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.02/1.49    inference(ennf_transformation,[],[f8])).
% 8.02/1.49  
% 8.02/1.49  fof(f94,plain,(
% 8.02/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f29])).
% 8.02/1.49  
% 8.02/1.49  fof(f116,plain,(
% 8.02/1.49    v2_pre_topc(sK4)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f7,axiom,(
% 8.02/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f27,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.02/1.49    inference(ennf_transformation,[],[f7])).
% 8.02/1.49  
% 8.02/1.49  fof(f28,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.02/1.49    inference(flattening,[],[f27])).
% 8.02/1.49  
% 8.02/1.49  fof(f93,plain,(
% 8.02/1.49    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f28])).
% 8.02/1.49  
% 8.02/1.49  fof(f115,plain,(
% 8.02/1.49    ~v2_struct_0(sK4)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f133,plain,(
% 8.02/1.49    r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) | r1_tmap_1(sK6,sK3,sK7,sK9)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f132,plain,(
% 8.02/1.49    sK9 = sK10),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f18,axiom,(
% 8.02/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f47,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.02/1.49    inference(ennf_transformation,[],[f18])).
% 8.02/1.49  
% 8.02/1.49  fof(f48,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.02/1.49    inference(flattening,[],[f47])).
% 8.02/1.49  
% 8.02/1.49  fof(f68,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.02/1.49    inference(nnf_transformation,[],[f48])).
% 8.02/1.49  
% 8.02/1.49  fof(f110,plain,(
% 8.02/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f68])).
% 8.02/1.49  
% 8.02/1.49  fof(f141,plain,(
% 8.02/1.49    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.02/1.49    inference(equality_resolution,[],[f110])).
% 8.02/1.49  
% 8.02/1.49  fof(f10,axiom,(
% 8.02/1.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f31,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 8.02/1.49    inference(ennf_transformation,[],[f10])).
% 8.02/1.49  
% 8.02/1.49  fof(f32,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 8.02/1.49    inference(flattening,[],[f31])).
% 8.02/1.49  
% 8.02/1.49  fof(f96,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f32])).
% 8.02/1.49  
% 8.02/1.49  fof(f118,plain,(
% 8.02/1.49    ~v2_struct_0(sK5)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f128,plain,(
% 8.02/1.49    m1_subset_1(sK10,u1_struct_0(sK5))),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f5,axiom,(
% 8.02/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f24,plain,(
% 8.02/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 8.02/1.49    inference(ennf_transformation,[],[f5])).
% 8.02/1.49  
% 8.02/1.49  fof(f91,plain,(
% 8.02/1.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f24])).
% 8.02/1.49  
% 8.02/1.49  fof(f3,axiom,(
% 8.02/1.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f59,plain,(
% 8.02/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 8.02/1.49    inference(nnf_transformation,[],[f3])).
% 8.02/1.49  
% 8.02/1.49  fof(f60,plain,(
% 8.02/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 8.02/1.49    inference(rectify,[],[f59])).
% 8.02/1.49  
% 8.02/1.49  fof(f61,plain,(
% 8.02/1.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f62,plain,(
% 8.02/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 8.02/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f60,f61])).
% 8.02/1.49  
% 8.02/1.49  fof(f87,plain,(
% 8.02/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 8.02/1.49    inference(cnf_transformation,[],[f62])).
% 8.02/1.49  
% 8.02/1.49  fof(f137,plain,(
% 8.02/1.49    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 8.02/1.49    inference(equality_resolution,[],[f87])).
% 8.02/1.49  
% 8.02/1.49  fof(f9,axiom,(
% 8.02/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f30,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 8.02/1.49    inference(ennf_transformation,[],[f9])).
% 8.02/1.49  
% 8.02/1.49  fof(f95,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f30])).
% 8.02/1.49  
% 8.02/1.49  fof(f109,plain,(
% 8.02/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f68])).
% 8.02/1.49  
% 8.02/1.49  fof(f142,plain,(
% 8.02/1.49    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.02/1.49    inference(equality_resolution,[],[f109])).
% 8.02/1.49  
% 8.02/1.49  fof(f17,axiom,(
% 8.02/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f45,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.02/1.49    inference(ennf_transformation,[],[f17])).
% 8.02/1.49  
% 8.02/1.49  fof(f46,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.02/1.49    inference(flattening,[],[f45])).
% 8.02/1.49  
% 8.02/1.49  fof(f108,plain,(
% 8.02/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f46])).
% 8.02/1.49  
% 8.02/1.49  fof(f140,plain,(
% 8.02/1.49    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.02/1.49    inference(equality_resolution,[],[f108])).
% 8.02/1.49  
% 8.02/1.49  fof(f134,plain,(
% 8.02/1.49    ~r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) | ~r1_tmap_1(sK6,sK3,sK7,sK9)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f16,axiom,(
% 8.02/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f43,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.02/1.49    inference(ennf_transformation,[],[f16])).
% 8.02/1.49  
% 8.02/1.49  fof(f44,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.02/1.49    inference(flattening,[],[f43])).
% 8.02/1.49  
% 8.02/1.49  fof(f67,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.02/1.49    inference(nnf_transformation,[],[f44])).
% 8.02/1.49  
% 8.02/1.49  fof(f107,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f67])).
% 8.02/1.49  
% 8.02/1.49  fof(f119,plain,(
% 8.02/1.49    m1_pre_topc(sK5,sK4)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f4,axiom,(
% 8.02/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f23,plain,(
% 8.02/1.49    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 8.02/1.49    inference(ennf_transformation,[],[f4])).
% 8.02/1.49  
% 8.02/1.49  fof(f90,plain,(
% 8.02/1.49    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f23])).
% 8.02/1.49  
% 8.02/1.49  fof(f1,axiom,(
% 8.02/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f22,plain,(
% 8.02/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 8.02/1.49    inference(ennf_transformation,[],[f1])).
% 8.02/1.49  
% 8.02/1.49  fof(f53,plain,(
% 8.02/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 8.02/1.49    inference(nnf_transformation,[],[f22])).
% 8.02/1.49  
% 8.02/1.49  fof(f54,plain,(
% 8.02/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.02/1.49    inference(rectify,[],[f53])).
% 8.02/1.49  
% 8.02/1.49  fof(f55,plain,(
% 8.02/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f56,plain,(
% 8.02/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.02/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f54,f55])).
% 8.02/1.49  
% 8.02/1.49  fof(f80,plain,(
% 8.02/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f56])).
% 8.02/1.49  
% 8.02/1.49  fof(f86,plain,(
% 8.02/1.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 8.02/1.49    inference(cnf_transformation,[],[f62])).
% 8.02/1.49  
% 8.02/1.49  fof(f138,plain,(
% 8.02/1.49    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 8.02/1.49    inference(equality_resolution,[],[f86])).
% 8.02/1.49  
% 8.02/1.49  fof(f127,plain,(
% 8.02/1.49    m1_subset_1(sK9,u1_struct_0(sK6))),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f126,plain,(
% 8.02/1.49    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4)))),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f13,axiom,(
% 8.02/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f37,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.02/1.49    inference(ennf_transformation,[],[f13])).
% 8.02/1.49  
% 8.02/1.49  fof(f38,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.02/1.49    inference(flattening,[],[f37])).
% 8.02/1.49  
% 8.02/1.49  fof(f63,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.02/1.49    inference(nnf_transformation,[],[f38])).
% 8.02/1.49  
% 8.02/1.49  fof(f64,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.02/1.49    inference(rectify,[],[f63])).
% 8.02/1.49  
% 8.02/1.49  fof(f65,plain,(
% 8.02/1.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK2(X0,X1,X2)) & r1_tarski(sK2(X0,X1,X2),X2) & v3_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f66,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK2(X0,X1,X2)) & r1_tarski(sK2(X0,X1,X2),X2) & v3_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.02/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f64,f65])).
% 8.02/1.49  
% 8.02/1.49  fof(f103,plain,(
% 8.02/1.49    ( ! [X2,X0,X3,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f66])).
% 8.02/1.49  
% 8.02/1.49  fof(f129,plain,(
% 8.02/1.49    v3_pre_topc(sK8,sK4)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f11,axiom,(
% 8.02/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f33,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.02/1.49    inference(ennf_transformation,[],[f11])).
% 8.02/1.49  
% 8.02/1.49  fof(f34,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.02/1.49    inference(flattening,[],[f33])).
% 8.02/1.49  
% 8.02/1.49  fof(f97,plain,(
% 8.02/1.49    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f34])).
% 8.02/1.49  
% 8.02/1.49  fof(f139,plain,(
% 8.02/1.49    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.02/1.49    inference(equality_resolution,[],[f97])).
% 8.02/1.49  
% 8.02/1.49  fof(f131,plain,(
% 8.02/1.49    r1_tarski(sK8,u1_struct_0(sK5))),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f130,plain,(
% 8.02/1.49    r2_hidden(sK9,sK8)),
% 8.02/1.49    inference(cnf_transformation,[],[f79])).
% 8.02/1.49  
% 8.02/1.49  fof(f106,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f67])).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5,plain,
% 8.02/1.49      ( r1_tarski(X0,X0) ),
% 8.02/1.49      inference(cnf_transformation,[],[f136]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3082,plain,
% 8.02/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_45,negated_conjecture,
% 8.02/1.49      ( m1_pre_topc(sK6,sK4) ),
% 8.02/1.49      inference(cnf_transformation,[],[f121]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3054,plain,
% 8.02/1.49      ( m1_pre_topc(sK6,sK4) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_41,negated_conjecture,
% 8.02/1.49      ( m1_pre_topc(sK5,sK6) ),
% 8.02/1.49      inference(cnf_transformation,[],[f125]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3056,plain,
% 8.02/1.49      ( m1_pre_topc(sK5,sK6) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_25,plain,
% 8.02/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 8.02/1.49      | ~ m1_pre_topc(X1,X3)
% 8.02/1.49      | ~ m1_pre_topc(X4,X3)
% 8.02/1.49      | ~ m1_pre_topc(X4,X1)
% 8.02/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 8.02/1.49      | ~ v1_funct_1(X0)
% 8.02/1.49      | v2_struct_0(X3)
% 8.02/1.49      | v2_struct_0(X2)
% 8.02/1.49      | ~ l1_pre_topc(X3)
% 8.02/1.49      | ~ l1_pre_topc(X2)
% 8.02/1.49      | ~ v2_pre_topc(X3)
% 8.02/1.49      | ~ v2_pre_topc(X2)
% 8.02/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X4)) = k3_tmap_1(X3,X2,X1,X4,X0) ),
% 8.02/1.49      inference(cnf_transformation,[],[f105]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_43,negated_conjecture,
% 8.02/1.49      ( v1_funct_2(sK7,u1_struct_0(sK6),u1_struct_0(sK3)) ),
% 8.02/1.49      inference(cnf_transformation,[],[f123]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_703,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.02/1.49      | ~ m1_pre_topc(X2,X1)
% 8.02/1.49      | ~ m1_pre_topc(X2,X0)
% 8.02/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X4))))
% 8.02/1.49      | ~ v1_funct_1(X3)
% 8.02/1.49      | v2_struct_0(X4)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | ~ l1_pre_topc(X4)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X4)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X4),X3,u1_struct_0(X2)) = k3_tmap_1(X1,X4,X0,X2,X3)
% 8.02/1.49      | u1_struct_0(X0) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X4) != u1_struct_0(sK3)
% 8.02/1.49      | sK7 != X3 ),
% 8.02/1.49      inference(resolution_lifted,[status(thm)],[c_25,c_43]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_704,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.02/1.49      | ~ m1_pre_topc(X2,X1)
% 8.02/1.49      | ~ m1_pre_topc(X2,X0)
% 8.02/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
% 8.02/1.49      | ~ v1_funct_1(sK7)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X3)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X3)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X3)
% 8.02/1.49      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK7,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK7)
% 8.02/1.49      | u1_struct_0(X0) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 8.02/1.49      inference(unflattening,[status(thm)],[c_703]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_44,negated_conjecture,
% 8.02/1.49      ( v1_funct_1(sK7) ),
% 8.02/1.49      inference(cnf_transformation,[],[f122]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_31,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.02/1.49      | ~ m1_pre_topc(X2,X0)
% 8.02/1.49      | m1_pre_topc(X2,X1)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X1) ),
% 8.02/1.49      inference(cnf_transformation,[],[f111]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_708,plain,
% 8.02/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
% 8.02/1.49      | ~ m1_pre_topc(X2,X0)
% 8.02/1.49      | ~ m1_pre_topc(X0,X1)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X3)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X3)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X3)
% 8.02/1.49      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK7,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK7)
% 8.02/1.49      | u1_struct_0(X0) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_704,c_44,c_31]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_709,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.02/1.49      | ~ m1_pre_topc(X2,X0)
% 8.02/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X3)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X3)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X3)
% 8.02/1.49      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X3),sK7,u1_struct_0(X2)) = k3_tmap_1(X1,X3,X0,X2,sK7)
% 8.02/1.49      | u1_struct_0(X0) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_708]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3040,plain,
% 8.02/1.49      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK7,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK7)
% 8.02/1.49      | u1_struct_0(X0) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3)
% 8.02/1.49      | m1_pre_topc(X0,X3) != iProver_top
% 8.02/1.49      | m1_pre_topc(X2,X0) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 8.02/1.49      | v2_struct_0(X3) = iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | l1_pre_topc(X3) != iProver_top
% 8.02/1.49      | l1_pre_topc(X1) != iProver_top
% 8.02/1.49      | v2_pre_topc(X3) != iProver_top
% 8.02/1.49      | v2_pre_topc(X1) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_709]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4454,plain,
% 8.02/1.49      ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(X0),sK7,u1_struct_0(X1)) = k3_tmap_1(X2,X0,sK6,X1,sK7)
% 8.02/1.49      | u1_struct_0(X0) != u1_struct_0(sK3)
% 8.02/1.49      | m1_pre_topc(X1,sK6) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK6,X2) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | v2_struct_0(X2) = iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top
% 8.02/1.49      | l1_pre_topc(X2) != iProver_top
% 8.02/1.49      | v2_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(X2) != iProver_top ),
% 8.02/1.49      inference(equality_resolution,[status(thm)],[c_3040]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4502,plain,
% 8.02/1.49      ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK6,X0,sK7)
% 8.02/1.49      | m1_pre_topc(X0,sK6) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK6,X1) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | v2_struct_0(sK3) = iProver_top
% 8.02/1.49      | l1_pre_topc(X1) != iProver_top
% 8.02/1.49      | l1_pre_topc(sK3) != iProver_top
% 8.02/1.49      | v2_pre_topc(X1) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK3) != iProver_top ),
% 8.02/1.49      inference(equality_resolution,[status(thm)],[c_4454]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_54,negated_conjecture,
% 8.02/1.49      ( ~ v2_struct_0(sK3) ),
% 8.02/1.49      inference(cnf_transformation,[],[f112]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_55,plain,
% 8.02/1.49      ( v2_struct_0(sK3) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_53,negated_conjecture,
% 8.02/1.49      ( v2_pre_topc(sK3) ),
% 8.02/1.49      inference(cnf_transformation,[],[f113]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_56,plain,
% 8.02/1.49      ( v2_pre_topc(sK3) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_52,negated_conjecture,
% 8.02/1.49      ( l1_pre_topc(sK3) ),
% 8.02/1.49      inference(cnf_transformation,[],[f114]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_57,plain,
% 8.02/1.49      ( l1_pre_topc(sK3) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_42,negated_conjecture,
% 8.02/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
% 8.02/1.49      inference(cnf_transformation,[],[f124]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_67,plain,
% 8.02/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5087,plain,
% 8.02/1.49      ( v2_pre_topc(X1) != iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK6,X0,sK7)
% 8.02/1.49      | m1_pre_topc(X0,sK6) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK6,X1) != iProver_top
% 8.02/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_4502,c_55,c_56,c_57,c_67]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5088,plain,
% 8.02/1.49      ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK6,X0,sK7)
% 8.02/1.49      | m1_pre_topc(X0,sK6) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK6,X1) != iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | l1_pre_topc(X1) != iProver_top
% 8.02/1.49      | v2_pre_topc(X1) != iProver_top ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_5087]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5093,plain,
% 8.02/1.49      ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(sK5)) = k3_tmap_1(X0,sK3,sK6,sK5,sK7)
% 8.02/1.49      | m1_pre_topc(sK6,X0) != iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(X0) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_3056,c_5088]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_24,plain,
% 8.02/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 8.02/1.49      | ~ m1_pre_topc(X3,X1)
% 8.02/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 8.02/1.49      | ~ v1_funct_1(X0)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X2)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X2)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X2)
% 8.02/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 8.02/1.49      inference(cnf_transformation,[],[f104]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_751,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.02/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 8.02/1.49      | ~ v1_funct_1(X2)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X3)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X3)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X3)
% 8.02/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X3) != u1_struct_0(sK3)
% 8.02/1.49      | sK7 != X2 ),
% 8.02/1.49      inference(resolution_lifted,[status(thm)],[c_24,c_43]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_752,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.02/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 8.02/1.49      | ~ v1_funct_1(sK7)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X2)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X2)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X2)
% 8.02/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK7,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK7,X0)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X2) != u1_struct_0(sK3) ),
% 8.02/1.49      inference(unflattening,[status(thm)],[c_751]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_756,plain,
% 8.02/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 8.02/1.49      | ~ m1_pre_topc(X0,X1)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X2)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X2)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X2)
% 8.02/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK7,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK7,X0)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X2) != u1_struct_0(sK3) ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_752,c_44]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_757,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.02/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X2)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X2)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X2)
% 8.02/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK7,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK7,X0)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X2) != u1_struct_0(sK3) ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_756]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3039,plain,
% 8.02/1.49      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK7,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK7,X2)
% 8.02/1.49      | u1_struct_0(X0) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3)
% 8.02/1.49      | m1_pre_topc(X2,X0) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top
% 8.02/1.49      | l1_pre_topc(X1) != iProver_top
% 8.02/1.49      | v2_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(X1) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4449,plain,
% 8.02/1.49      ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(X0),sK7,u1_struct_0(X1)) = k2_tmap_1(sK6,X0,sK7,X1)
% 8.02/1.49      | u1_struct_0(X0) != u1_struct_0(sK3)
% 8.02/1.49      | m1_pre_topc(X1,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | v2_struct_0(sK6) = iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top
% 8.02/1.49      | l1_pre_topc(sK6) != iProver_top
% 8.02/1.49      | v2_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK6) != iProver_top ),
% 8.02/1.49      inference(equality_resolution,[status(thm)],[c_3039]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_49,negated_conjecture,
% 8.02/1.49      ( l1_pre_topc(sK4) ),
% 8.02/1.49      inference(cnf_transformation,[],[f117]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_60,plain,
% 8.02/1.49      ( l1_pre_topc(sK4) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_46,negated_conjecture,
% 8.02/1.49      ( ~ v2_struct_0(sK6) ),
% 8.02/1.49      inference(cnf_transformation,[],[f120]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_63,plain,
% 8.02/1.49      ( v2_struct_0(sK6) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_64,plain,
% 8.02/1.49      ( m1_pre_topc(sK6,sK4) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3542,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,sK6)
% 8.02/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(sK6)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(sK6)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(sK6)
% 8.02/1.49      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(X1),sK7,u1_struct_0(X0)) = k2_tmap_1(sK6,X1,sK7,X0)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3)
% 8.02/1.49      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_757]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3543,plain,
% 8.02/1.49      ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(X0),sK7,u1_struct_0(X1)) = k2_tmap_1(sK6,X0,sK7,X1)
% 8.02/1.49      | u1_struct_0(X0) != u1_struct_0(sK3)
% 8.02/1.49      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 8.02/1.49      | m1_pre_topc(X1,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | v2_struct_0(sK6) = iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top
% 8.02/1.49      | l1_pre_topc(sK6) != iProver_top
% 8.02/1.49      | v2_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK6) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_3542]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_14,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 8.02/1.49      inference(cnf_transformation,[],[f94]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3360,plain,
% 8.02/1.49      ( ~ m1_pre_topc(sK6,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK6) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3625,plain,
% 8.02/1.49      ( ~ m1_pre_topc(sK6,sK4) | l1_pre_topc(sK6) | ~ l1_pre_topc(sK4) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_3360]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3626,plain,
% 8.02/1.49      ( m1_pre_topc(sK6,sK4) != iProver_top
% 8.02/1.49      | l1_pre_topc(sK6) = iProver_top
% 8.02/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_3625]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1906,plain,( X0 = X0 ),theory(equality) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4188,plain,
% 8.02/1.49      ( u1_struct_0(sK6) = u1_struct_0(sK6) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_1906]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4491,plain,
% 8.02/1.49      ( l1_pre_topc(X0) != iProver_top
% 8.02/1.49      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(X0),sK7,u1_struct_0(X1)) = k2_tmap_1(sK6,X0,sK7,X1)
% 8.02/1.49      | u1_struct_0(X0) != u1_struct_0(sK3)
% 8.02/1.49      | m1_pre_topc(X1,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | v2_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK6) != iProver_top ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_4449,c_60,c_63,c_64,c_3543,c_3626,c_4188]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4492,plain,
% 8.02/1.49      ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(X0),sK7,u1_struct_0(X1)) = k2_tmap_1(sK6,X0,sK7,X1)
% 8.02/1.49      | u1_struct_0(X0) != u1_struct_0(sK3)
% 8.02/1.49      | m1_pre_topc(X1,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK6) != iProver_top ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_4491]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4497,plain,
% 8.02/1.49      ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(X0)) = k2_tmap_1(sK6,sK3,sK7,X0)
% 8.02/1.49      | m1_pre_topc(X0,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 8.02/1.49      | v2_struct_0(sK3) = iProver_top
% 8.02/1.49      | l1_pre_topc(sK3) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK6) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK3) != iProver_top ),
% 8.02/1.49      inference(equality_resolution,[status(thm)],[c_4492]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_50,negated_conjecture,
% 8.02/1.49      ( v2_pre_topc(sK4) ),
% 8.02/1.49      inference(cnf_transformation,[],[f116]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_59,plain,
% 8.02/1.49      ( v2_pre_topc(sK4) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_13,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | v2_pre_topc(X0) ),
% 8.02/1.49      inference(cnf_transformation,[],[f93]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3745,plain,
% 8.02/1.49      ( ~ m1_pre_topc(sK6,X0)
% 8.02/1.49      | ~ l1_pre_topc(X0)
% 8.02/1.49      | ~ v2_pre_topc(X0)
% 8.02/1.49      | v2_pre_topc(sK6) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4522,plain,
% 8.02/1.49      ( ~ m1_pre_topc(sK6,sK4)
% 8.02/1.49      | ~ l1_pre_topc(sK4)
% 8.02/1.49      | v2_pre_topc(sK6)
% 8.02/1.49      | ~ v2_pre_topc(sK4) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_3745]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4523,plain,
% 8.02/1.49      ( m1_pre_topc(sK6,sK4) != iProver_top
% 8.02/1.49      | l1_pre_topc(sK4) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK6) = iProver_top
% 8.02/1.49      | v2_pre_topc(sK4) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_4522]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4546,plain,
% 8.02/1.49      ( m1_pre_topc(X0,sK6) != iProver_top
% 8.02/1.49      | k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(X0)) = k2_tmap_1(sK6,sK3,sK7,X0) ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_4497,c_55,c_56,c_57,c_59,c_60,c_64,c_67,c_4523]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4547,plain,
% 8.02/1.49      ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(X0)) = k2_tmap_1(sK6,sK3,sK7,X0)
% 8.02/1.49      | m1_pre_topc(X0,sK6) != iProver_top ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_4546]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4552,plain,
% 8.02/1.49      ( k2_partfun1(u1_struct_0(sK6),u1_struct_0(sK3),sK7,u1_struct_0(sK5)) = k2_tmap_1(sK6,sK3,sK7,sK5) ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_3056,c_4547]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5094,plain,
% 8.02/1.49      ( k3_tmap_1(X0,sK3,sK6,sK5,sK7) = k2_tmap_1(sK6,sK3,sK7,sK5)
% 8.02/1.49      | m1_pre_topc(sK6,X0) != iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(X0) != iProver_top ),
% 8.02/1.49      inference(light_normalisation,[status(thm)],[c_5093,c_4552]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5195,plain,
% 8.02/1.49      ( k3_tmap_1(sK4,sK3,sK6,sK5,sK7) = k2_tmap_1(sK6,sK3,sK7,sK5)
% 8.02/1.49      | v2_struct_0(sK4) = iProver_top
% 8.02/1.49      | l1_pre_topc(sK4) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK4) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_3054,c_5094]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_51,negated_conjecture,
% 8.02/1.49      ( ~ v2_struct_0(sK4) ),
% 8.02/1.49      inference(cnf_transformation,[],[f115]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_58,plain,
% 8.02/1.49      ( v2_struct_0(sK4) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5198,plain,
% 8.02/1.49      ( k3_tmap_1(sK4,sK3,sK6,sK5,sK7) = k2_tmap_1(sK6,sK3,sK7,sK5) ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_5195,c_58,c_59,c_60]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_33,negated_conjecture,
% 8.02/1.49      ( r1_tmap_1(sK6,sK3,sK7,sK9)
% 8.02/1.49      | r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) ),
% 8.02/1.49      inference(cnf_transformation,[],[f133]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3063,plain,
% 8.02/1.49      ( r1_tmap_1(sK6,sK3,sK7,sK9) = iProver_top
% 8.02/1.49      | r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_34,negated_conjecture,
% 8.02/1.49      ( sK9 = sK10 ),
% 8.02/1.49      inference(cnf_transformation,[],[f132]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3089,plain,
% 8.02/1.49      ( r1_tmap_1(sK6,sK3,sK7,sK10) = iProver_top
% 8.02/1.49      | r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) = iProver_top ),
% 8.02/1.49      inference(light_normalisation,[status(thm)],[c_3063,c_34]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5200,plain,
% 8.02/1.49      ( r1_tmap_1(sK6,sK3,sK7,sK10) = iProver_top
% 8.02/1.49      | r1_tmap_1(sK5,sK3,k2_tmap_1(sK6,sK3,sK7,sK5),sK10) = iProver_top ),
% 8.02/1.49      inference(demodulation,[status(thm)],[c_5198,c_3089]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_29,plain,
% 8.02/1.49      ( r1_tmap_1(X0,X1,X2,X3)
% 8.02/1.49      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 8.02/1.49      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 8.02/1.49      | ~ m1_connsp_2(X5,X0,X3)
% 8.02/1.49      | ~ m1_pre_topc(X4,X0)
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 8.02/1.49      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 8.02/1.49      | ~ r1_tarski(X5,u1_struct_0(X4))
% 8.02/1.49      | ~ v1_funct_1(X2)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | v2_struct_0(X4)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X0)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X0) ),
% 8.02/1.49      inference(cnf_transformation,[],[f141]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_853,plain,
% 8.02/1.49      ( r1_tmap_1(X0,X1,X2,X3)
% 8.02/1.49      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 8.02/1.49      | ~ m1_connsp_2(X5,X0,X3)
% 8.02/1.49      | ~ m1_pre_topc(X4,X0)
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 8.02/1.49      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 8.02/1.49      | ~ r1_tarski(X5,u1_struct_0(X4))
% 8.02/1.49      | ~ v1_funct_1(X2)
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X4)
% 8.02/1.49      | ~ l1_pre_topc(X0)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X0)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | u1_struct_0(X0) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3)
% 8.02/1.49      | sK7 != X2 ),
% 8.02/1.49      inference(resolution_lifted,[status(thm)],[c_29,c_43]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_854,plain,
% 8.02/1.49      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
% 8.02/1.49      | r1_tmap_1(X2,X1,sK7,X3)
% 8.02/1.49      | ~ m1_connsp_2(X4,X2,X3)
% 8.02/1.49      | ~ m1_pre_topc(X0,X2)
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 8.02/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 8.02/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 8.02/1.49      | ~ r1_tarski(X4,u1_struct_0(X0))
% 8.02/1.49      | ~ v1_funct_1(sK7)
% 8.02/1.49      | v2_struct_0(X2)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | ~ l1_pre_topc(X2)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X2)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | u1_struct_0(X2) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 8.02/1.49      inference(unflattening,[status(thm)],[c_853]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_858,plain,
% 8.02/1.49      ( ~ r1_tarski(X4,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 8.02/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_pre_topc(X0,X2)
% 8.02/1.49      | ~ m1_connsp_2(X4,X2,X3)
% 8.02/1.49      | r1_tmap_1(X2,X1,sK7,X3)
% 8.02/1.49      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
% 8.02/1.49      | v2_struct_0(X2)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | ~ l1_pre_topc(X2)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X2)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | u1_struct_0(X2) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_854,c_44]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_859,plain,
% 8.02/1.49      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
% 8.02/1.49      | r1_tmap_1(X2,X1,sK7,X3)
% 8.02/1.49      | ~ m1_connsp_2(X4,X2,X3)
% 8.02/1.49      | ~ m1_pre_topc(X0,X2)
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 8.02/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 8.02/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 8.02/1.49      | ~ r1_tarski(X4,u1_struct_0(X0))
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X2)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X2)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X2)
% 8.02/1.49      | u1_struct_0(X2) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_858]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_16,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.02/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.02/1.49      | m1_subset_1(X2,u1_struct_0(X1))
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | ~ l1_pre_topc(X1) ),
% 8.02/1.49      inference(cnf_transformation,[],[f96]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_900,plain,
% 8.02/1.49      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
% 8.02/1.49      | r1_tmap_1(X2,X1,sK7,X3)
% 8.02/1.49      | ~ m1_connsp_2(X4,X2,X3)
% 8.02/1.49      | ~ m1_pre_topc(X0,X2)
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 8.02/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 8.02/1.49      | ~ r1_tarski(X4,u1_struct_0(X0))
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X2)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X2)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X2)
% 8.02/1.49      | u1_struct_0(X2) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 8.02/1.49      inference(forward_subsumption_resolution,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_859,c_16]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3037,plain,
% 8.02/1.49      ( u1_struct_0(X0) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3)
% 8.02/1.49      | r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,sK7,X2),X3) != iProver_top
% 8.02/1.49      | r1_tmap_1(X0,X1,sK7,X3) = iProver_top
% 8.02/1.49      | m1_connsp_2(X4,X0,X3) != iProver_top
% 8.02/1.49      | m1_pre_topc(X2,X0) != iProver_top
% 8.02/1.49      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 8.02/1.49      | m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 8.02/1.49      | r1_tarski(X4,u1_struct_0(X2)) != iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | v2_struct_0(X2) = iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | l1_pre_topc(X1) != iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(X1) != iProver_top
% 8.02/1.49      | v2_pre_topc(X0) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_900]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3507,plain,
% 8.02/1.49      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 8.02/1.49      | r1_tmap_1(X1,X0,k2_tmap_1(sK6,X0,sK7,X1),X2) != iProver_top
% 8.02/1.49      | r1_tmap_1(sK6,X0,sK7,X2) = iProver_top
% 8.02/1.49      | m1_connsp_2(X3,sK6,X2) != iProver_top
% 8.02/1.49      | m1_pre_topc(X1,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 8.02/1.49      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 8.02/1.49      | r1_tarski(X3,u1_struct_0(X1)) != iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | v2_struct_0(sK6) = iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top
% 8.02/1.49      | l1_pre_topc(sK6) != iProver_top
% 8.02/1.49      | v2_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK6) != iProver_top ),
% 8.02/1.49      inference(equality_resolution,[status(thm)],[c_3037]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_8419,plain,
% 8.02/1.49      ( v2_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | r1_tarski(X3,u1_struct_0(X1)) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 8.02/1.49      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 8.02/1.49      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 8.02/1.49      | m1_pre_topc(X1,sK6) != iProver_top
% 8.02/1.49      | m1_connsp_2(X3,sK6,X2) != iProver_top
% 8.02/1.49      | r1_tmap_1(sK6,X0,sK7,X2) = iProver_top
% 8.02/1.49      | r1_tmap_1(X1,X0,k2_tmap_1(sK6,X0,sK7,X1),X2) != iProver_top
% 8.02/1.49      | u1_struct_0(X0) != u1_struct_0(sK3)
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_3507,c_59,c_60,c_63,c_64,c_3626,c_4523]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_8420,plain,
% 8.02/1.49      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 8.02/1.49      | r1_tmap_1(X1,X0,k2_tmap_1(sK6,X0,sK7,X1),X2) != iProver_top
% 8.02/1.49      | r1_tmap_1(sK6,X0,sK7,X2) = iProver_top
% 8.02/1.49      | m1_connsp_2(X3,sK6,X2) != iProver_top
% 8.02/1.49      | m1_pre_topc(X1,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 8.02/1.49      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 8.02/1.49      | r1_tarski(X3,u1_struct_0(X1)) != iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(X0) != iProver_top ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_8419]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_8425,plain,
% 8.02/1.49      ( r1_tmap_1(X0,sK3,k2_tmap_1(sK6,sK3,sK7,X0),X1) != iProver_top
% 8.02/1.49      | r1_tmap_1(sK6,sK3,sK7,X1) = iProver_top
% 8.02/1.49      | m1_connsp_2(X2,sK6,X1) != iProver_top
% 8.02/1.49      | m1_pre_topc(X0,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 8.02/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 8.02/1.49      | r1_tarski(X2,u1_struct_0(X0)) != iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | v2_struct_0(sK3) = iProver_top
% 8.02/1.49      | l1_pre_topc(sK3) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK3) != iProver_top ),
% 8.02/1.49      inference(equality_resolution,[status(thm)],[c_8420]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_31566,plain,
% 8.02/1.49      ( v2_struct_0(X0) = iProver_top
% 8.02/1.49      | r1_tarski(X2,u1_struct_0(X0)) != iProver_top
% 8.02/1.49      | r1_tmap_1(X0,sK3,k2_tmap_1(sK6,sK3,sK7,X0),X1) != iProver_top
% 8.02/1.49      | r1_tmap_1(sK6,sK3,sK7,X1) = iProver_top
% 8.02/1.49      | m1_connsp_2(X2,sK6,X1) != iProver_top
% 8.02/1.49      | m1_pre_topc(X0,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 8.02/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_8425,c_55,c_56,c_57,c_67]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_31567,plain,
% 8.02/1.49      ( r1_tmap_1(X0,sK3,k2_tmap_1(sK6,sK3,sK7,X0),X1) != iProver_top
% 8.02/1.49      | r1_tmap_1(sK6,sK3,sK7,X1) = iProver_top
% 8.02/1.49      | m1_connsp_2(X2,sK6,X1) != iProver_top
% 8.02/1.49      | m1_pre_topc(X0,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 8.02/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 8.02/1.49      | r1_tarski(X2,u1_struct_0(X0)) != iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_31566]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_31572,plain,
% 8.02/1.49      ( r1_tmap_1(sK6,sK3,sK7,sK10) = iProver_top
% 8.02/1.49      | m1_connsp_2(X0,sK6,sK10) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK5,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 8.02/1.49      | m1_subset_1(sK10,u1_struct_0(sK5)) != iProver_top
% 8.02/1.49      | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
% 8.02/1.49      | v2_struct_0(sK5) = iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_5200,c_31567]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_48,negated_conjecture,
% 8.02/1.49      ( ~ v2_struct_0(sK5) ),
% 8.02/1.49      inference(cnf_transformation,[],[f118]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_61,plain,
% 8.02/1.49      ( v2_struct_0(sK5) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_68,plain,
% 8.02/1.49      ( m1_pre_topc(sK5,sK6) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_38,negated_conjecture,
% 8.02/1.49      ( m1_subset_1(sK10,u1_struct_0(sK5)) ),
% 8.02/1.49      inference(cnf_transformation,[],[f128]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_71,plain,
% 8.02/1.49      ( m1_subset_1(sK10,u1_struct_0(sK5)) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_11,plain,
% 8.02/1.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 8.02/1.49      inference(cnf_transformation,[],[f91]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4044,plain,
% 8.02/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 8.02/1.49      | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4045,plain,
% 8.02/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 8.02/1.49      | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_4044]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_8,plain,
% 8.02/1.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.02/1.49      inference(cnf_transformation,[],[f137]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4838,plain,
% 8.02/1.49      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 8.02/1.49      | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4839,plain,
% 8.02/1.49      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 8.02/1.49      | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_4838]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_15,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.02/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 8.02/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 8.02/1.49      | ~ l1_pre_topc(X1) ),
% 8.02/1.49      inference(cnf_transformation,[],[f95]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4033,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,sK6)
% 8.02/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.02/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 8.02/1.49      | ~ l1_pre_topc(sK6) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_15]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5225,plain,
% 8.02/1.49      ( ~ m1_pre_topc(sK5,sK6)
% 8.02/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 8.02/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 8.02/1.49      | ~ l1_pre_topc(sK6) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_4033]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5226,plain,
% 8.02/1.49      ( m1_pre_topc(sK5,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 8.02/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 8.02/1.49      | l1_pre_topc(sK6) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_5225]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_30,plain,
% 8.02/1.49      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 8.02/1.49      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 8.02/1.49      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 8.02/1.49      | ~ m1_connsp_2(X5,X0,X3)
% 8.02/1.49      | ~ m1_pre_topc(X4,X0)
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 8.02/1.49      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 8.02/1.49      | ~ r1_tarski(X5,u1_struct_0(X4))
% 8.02/1.49      | ~ v1_funct_1(X2)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | v2_struct_0(X4)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X0)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X0) ),
% 8.02/1.49      inference(cnf_transformation,[],[f142]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_28,plain,
% 8.02/1.49      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 8.02/1.49      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 8.02/1.49      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 8.02/1.49      | ~ m1_pre_topc(X4,X0)
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 8.02/1.49      | ~ v1_funct_1(X2)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | v2_struct_0(X4)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X0)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X0) ),
% 8.02/1.49      inference(cnf_transformation,[],[f140]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_283,plain,
% 8.02/1.49      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 8.02/1.49      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 8.02/1.49      | ~ r1_tmap_1(X0,X1,X2,X3)
% 8.02/1.49      | ~ m1_pre_topc(X4,X0)
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 8.02/1.49      | ~ v1_funct_1(X2)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | v2_struct_0(X4)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X0)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X0) ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_30,c_28]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_284,plain,
% 8.02/1.49      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 8.02/1.49      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 8.02/1.49      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 8.02/1.49      | ~ m1_pre_topc(X4,X0)
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 8.02/1.49      | ~ v1_funct_1(X2)
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X4)
% 8.02/1.49      | ~ l1_pre_topc(X0)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X0)
% 8.02/1.49      | ~ v2_pre_topc(X1) ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_283]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_796,plain,
% 8.02/1.49      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 8.02/1.49      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 8.02/1.49      | ~ m1_pre_topc(X4,X0)
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 8.02/1.49      | ~ v1_funct_1(X2)
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X4)
% 8.02/1.49      | ~ l1_pre_topc(X0)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X0)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | u1_struct_0(X0) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3)
% 8.02/1.49      | sK7 != X2 ),
% 8.02/1.49      inference(resolution_lifted,[status(thm)],[c_284,c_43]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_797,plain,
% 8.02/1.49      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
% 8.02/1.49      | ~ r1_tmap_1(X2,X1,sK7,X3)
% 8.02/1.49      | ~ m1_pre_topc(X0,X2)
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 8.02/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 8.02/1.49      | ~ v1_funct_1(sK7)
% 8.02/1.49      | v2_struct_0(X2)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | ~ l1_pre_topc(X2)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X2)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | u1_struct_0(X2) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 8.02/1.49      inference(unflattening,[status(thm)],[c_796]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_801,plain,
% 8.02/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_pre_topc(X0,X2)
% 8.02/1.49      | ~ r1_tmap_1(X2,X1,sK7,X3)
% 8.02/1.49      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
% 8.02/1.49      | v2_struct_0(X2)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | ~ l1_pre_topc(X2)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X2)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | u1_struct_0(X2) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_797,c_44]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_802,plain,
% 8.02/1.49      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
% 8.02/1.49      | ~ r1_tmap_1(X2,X1,sK7,X3)
% 8.02/1.49      | ~ m1_pre_topc(X0,X2)
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 8.02/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X2)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X2)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X2)
% 8.02/1.49      | u1_struct_0(X2) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_801]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_837,plain,
% 8.02/1.49      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK7,X0),X3)
% 8.02/1.49      | ~ r1_tmap_1(X2,X1,sK7,X3)
% 8.02/1.49      | ~ m1_pre_topc(X0,X2)
% 8.02/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(X2)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(X2)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X2)
% 8.02/1.49      | u1_struct_0(X2) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 8.02/1.49      inference(forward_subsumption_resolution,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_802,c_16]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3038,plain,
% 8.02/1.49      ( u1_struct_0(X0) != u1_struct_0(sK6)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3)
% 8.02/1.49      | r1_tmap_1(X2,X1,k2_tmap_1(X0,X1,sK7,X2),X3) = iProver_top
% 8.02/1.49      | r1_tmap_1(X0,X1,sK7,X3) != iProver_top
% 8.02/1.49      | m1_pre_topc(X2,X0) != iProver_top
% 8.02/1.49      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | v2_struct_0(X2) = iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | l1_pre_topc(X1) != iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(X1) != iProver_top
% 8.02/1.49      | v2_pre_topc(X0) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_837]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4116,plain,
% 8.02/1.49      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 8.02/1.49      | r1_tmap_1(X1,X0,k2_tmap_1(sK6,X0,sK7,X1),X2) = iProver_top
% 8.02/1.49      | r1_tmap_1(sK6,X0,sK7,X2) != iProver_top
% 8.02/1.49      | m1_pre_topc(X1,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | v2_struct_0(sK6) = iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top
% 8.02/1.49      | l1_pre_topc(sK6) != iProver_top
% 8.02/1.49      | v2_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK6) != iProver_top ),
% 8.02/1.49      inference(equality_resolution,[status(thm)],[c_3038]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3560,plain,
% 8.02/1.49      ( r1_tmap_1(X0,X1,k2_tmap_1(sK6,X1,sK7,X0),X2)
% 8.02/1.49      | ~ r1_tmap_1(sK6,X1,sK7,X2)
% 8.02/1.49      | ~ m1_pre_topc(X0,sK6)
% 8.02/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 8.02/1.49      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X1))))
% 8.02/1.49      | v2_struct_0(X0)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | v2_struct_0(sK6)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ l1_pre_topc(sK6)
% 8.02/1.49      | ~ v2_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(sK6)
% 8.02/1.49      | u1_struct_0(X1) != u1_struct_0(sK3)
% 8.02/1.49      | u1_struct_0(sK6) != u1_struct_0(sK6) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_837]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3561,plain,
% 8.02/1.49      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 8.02/1.49      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 8.02/1.49      | r1_tmap_1(X1,X0,k2_tmap_1(sK6,X0,sK7,X1),X2) = iProver_top
% 8.02/1.49      | r1_tmap_1(sK6,X0,sK7,X2) != iProver_top
% 8.02/1.49      | m1_pre_topc(X1,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | v2_struct_0(sK6) = iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top
% 8.02/1.49      | l1_pre_topc(sK6) != iProver_top
% 8.02/1.49      | v2_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK6) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_3560]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5963,plain,
% 8.02/1.49      ( v2_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 8.02/1.49      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 8.02/1.49      | m1_pre_topc(X1,sK6) != iProver_top
% 8.02/1.49      | r1_tmap_1(sK6,X0,sK7,X2) != iProver_top
% 8.02/1.49      | r1_tmap_1(X1,X0,k2_tmap_1(sK6,X0,sK7,X1),X2) = iProver_top
% 8.02/1.49      | u1_struct_0(X0) != u1_struct_0(sK3)
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_4116,c_59,c_60,c_63,c_64,c_3561,c_3626,c_4188,c_4523]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5964,plain,
% 8.02/1.49      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 8.02/1.49      | r1_tmap_1(X1,X0,k2_tmap_1(sK6,X0,sK7,X1),X2) = iProver_top
% 8.02/1.49      | r1_tmap_1(sK6,X0,sK7,X2) != iProver_top
% 8.02/1.49      | m1_pre_topc(X1,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(X0)))) != iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top
% 8.02/1.49      | v2_pre_topc(X0) != iProver_top ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_5963]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5969,plain,
% 8.02/1.49      ( r1_tmap_1(X0,sK3,k2_tmap_1(sK6,sK3,sK7,X0),X1) = iProver_top
% 8.02/1.49      | r1_tmap_1(sK6,sK3,sK7,X1) != iProver_top
% 8.02/1.49      | m1_pre_topc(X0,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 8.02/1.49      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) != iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top
% 8.02/1.49      | v2_struct_0(sK3) = iProver_top
% 8.02/1.49      | l1_pre_topc(sK3) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK3) != iProver_top ),
% 8.02/1.49      inference(equality_resolution,[status(thm)],[c_5964]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_14677,plain,
% 8.02/1.49      ( v2_struct_0(X0) = iProver_top
% 8.02/1.49      | r1_tmap_1(X0,sK3,k2_tmap_1(sK6,sK3,sK7,X0),X1) = iProver_top
% 8.02/1.49      | r1_tmap_1(sK6,sK3,sK7,X1) != iProver_top
% 8.02/1.49      | m1_pre_topc(X0,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_5969,c_55,c_56,c_57,c_67]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_14678,plain,
% 8.02/1.49      ( r1_tmap_1(X0,sK3,k2_tmap_1(sK6,sK3,sK7,X0),X1) = iProver_top
% 8.02/1.49      | r1_tmap_1(sK6,sK3,sK7,X1) != iProver_top
% 8.02/1.49      | m1_pre_topc(X0,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 8.02/1.49      | v2_struct_0(X0) = iProver_top ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_14677]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_32,negated_conjecture,
% 8.02/1.49      ( ~ r1_tmap_1(sK6,sK3,sK7,sK9)
% 8.02/1.49      | ~ r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) ),
% 8.02/1.49      inference(cnf_transformation,[],[f134]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3064,plain,
% 8.02/1.49      ( r1_tmap_1(sK6,sK3,sK7,sK9) != iProver_top
% 8.02/1.49      | r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3090,plain,
% 8.02/1.49      ( r1_tmap_1(sK6,sK3,sK7,sK10) != iProver_top
% 8.02/1.49      | r1_tmap_1(sK5,sK3,k3_tmap_1(sK4,sK3,sK6,sK5,sK7),sK10) != iProver_top ),
% 8.02/1.49      inference(light_normalisation,[status(thm)],[c_3064,c_34]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5201,plain,
% 8.02/1.49      ( r1_tmap_1(sK6,sK3,sK7,sK10) != iProver_top
% 8.02/1.49      | r1_tmap_1(sK5,sK3,k2_tmap_1(sK6,sK3,sK7,sK5),sK10) != iProver_top ),
% 8.02/1.49      inference(demodulation,[status(thm)],[c_5198,c_3090]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_14683,plain,
% 8.02/1.49      ( r1_tmap_1(sK6,sK3,sK7,sK10) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK5,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(sK10,u1_struct_0(sK5)) != iProver_top
% 8.02/1.49      | v2_struct_0(sK5) = iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_14678,c_5201]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_33042,plain,
% 8.02/1.49      ( r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
% 8.02/1.49      | m1_connsp_2(X0,sK6,sK10) != iProver_top ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_31572,c_60,c_61,c_64,c_68,c_71,c_3626,c_4045,c_4839,
% 8.02/1.49                 c_5226,c_14683]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_33043,plain,
% 8.02/1.49      ( m1_connsp_2(X0,sK6,sK10) != iProver_top
% 8.02/1.49      | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_33042]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_33048,plain,
% 8.02/1.49      ( m1_connsp_2(u1_struct_0(sK5),sK6,sK10) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_3082,c_33043]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_26,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.02/1.49      | ~ m1_pre_topc(X2,X1)
% 8.02/1.49      | ~ m1_pre_topc(X0,X2)
% 8.02/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X1) ),
% 8.02/1.49      inference(cnf_transformation,[],[f107]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3067,plain,
% 8.02/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.02/1.49      | m1_pre_topc(X2,X1) != iProver_top
% 8.02/1.49      | m1_pre_topc(X0,X2) != iProver_top
% 8.02/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 8.02/1.49      | l1_pre_topc(X1) != iProver_top
% 8.02/1.49      | v2_pre_topc(X1) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_6667,plain,
% 8.02/1.49      ( m1_pre_topc(X0,sK4) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK6,X0) != iProver_top
% 8.02/1.49      | r1_tarski(u1_struct_0(sK6),u1_struct_0(X0)) = iProver_top
% 8.02/1.49      | l1_pre_topc(sK4) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK4) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_3054,c_3067]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_6765,plain,
% 8.02/1.49      ( m1_pre_topc(X0,sK4) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK6,X0) != iProver_top
% 8.02/1.49      | r1_tarski(u1_struct_0(sK6),u1_struct_0(X0)) = iProver_top ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_6667,c_59,c_60]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_47,negated_conjecture,
% 8.02/1.49      ( m1_pre_topc(sK5,sK4) ),
% 8.02/1.49      inference(cnf_transformation,[],[f119]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3052,plain,
% 8.02/1.49      ( m1_pre_topc(sK5,sK4) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_6668,plain,
% 8.02/1.49      ( m1_pre_topc(X0,sK4) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK5,X0) != iProver_top
% 8.02/1.49      | r1_tarski(u1_struct_0(sK5),u1_struct_0(X0)) = iProver_top
% 8.02/1.49      | l1_pre_topc(sK4) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK4) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_3052,c_3067]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_6777,plain,
% 8.02/1.49      ( m1_pre_topc(X0,sK4) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK5,X0) != iProver_top
% 8.02/1.49      | r1_tarski(u1_struct_0(sK5),u1_struct_0(X0)) = iProver_top ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_6668,c_59,c_60]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_10,plain,
% 8.02/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
% 8.02/1.49      inference(cnf_transformation,[],[f90]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3077,plain,
% 8.02/1.49      ( r1_tarski(X0,X1) != iProver_top
% 8.02/1.49      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3079,plain,
% 8.02/1.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 8.02/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_2,plain,
% 8.02/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 8.02/1.49      inference(cnf_transformation,[],[f80]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3084,plain,
% 8.02/1.49      ( r2_hidden(X0,X1) != iProver_top
% 8.02/1.49      | r2_hidden(X0,X2) = iProver_top
% 8.02/1.49      | r1_tarski(X1,X2) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5355,plain,
% 8.02/1.49      ( r2_hidden(X0,X1) = iProver_top
% 8.02/1.49      | r1_tarski(X0,X2) != iProver_top
% 8.02/1.49      | r1_tarski(k1_zfmisc_1(X2),X1) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_3079,c_3084]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_10050,plain,
% 8.02/1.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 8.02/1.49      | r1_tarski(X2,X1) != iProver_top
% 8.02/1.49      | r1_tarski(X0,X2) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_3077,c_5355]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_10890,plain,
% 8.02/1.49      ( m1_pre_topc(X0,sK4) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK5,X0) != iProver_top
% 8.02/1.49      | r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(X1)) = iProver_top
% 8.02/1.49      | r1_tarski(u1_struct_0(X0),X1) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_6777,c_10050]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_11436,plain,
% 8.02/1.49      ( m1_pre_topc(X0,sK4) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK6,X0) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK6,sK4) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK5,sK6) != iProver_top
% 8.02/1.49      | r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_6765,c_10890]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_12381,plain,
% 8.02/1.49      ( m1_pre_topc(X0,sK4) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK6,X0) != iProver_top
% 8.02/1.49      | r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_11436,c_64,c_68]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_9,plain,
% 8.02/1.49      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 8.02/1.49      inference(cnf_transformation,[],[f138]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3078,plain,
% 8.02/1.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.02/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_12391,plain,
% 8.02/1.49      ( m1_pre_topc(X0,sK4) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK6,X0) != iProver_top
% 8.02/1.49      | r1_tarski(u1_struct_0(sK5),u1_struct_0(X0)) = iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_12381,c_3078]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_39,negated_conjecture,
% 8.02/1.49      ( m1_subset_1(sK9,u1_struct_0(sK6)) ),
% 8.02/1.49      inference(cnf_transformation,[],[f127]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3058,plain,
% 8.02/1.49      ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3088,plain,
% 8.02/1.49      ( m1_subset_1(sK10,u1_struct_0(sK6)) = iProver_top ),
% 8.02/1.49      inference(light_normalisation,[status(thm)],[c_3058,c_34]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_40,negated_conjecture,
% 8.02/1.49      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 8.02/1.49      inference(cnf_transformation,[],[f126]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3057,plain,
% 8.02/1.49      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3072,plain,
% 8.02/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.02/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.02/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.02/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_6200,plain,
% 8.02/1.49      ( m1_pre_topc(sK4,X0) != iProver_top
% 8.02/1.49      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_3057,c_3072]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_6397,plain,
% 8.02/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK4,X0) != iProver_top
% 8.02/1.49      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.02/1.49      | l1_pre_topc(X1) != iProver_top
% 8.02/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_6200,c_3072]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_118,plain,
% 8.02/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.02/1.49      | l1_pre_topc(X1) != iProver_top
% 8.02/1.49      | l1_pre_topc(X0) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_9484,plain,
% 8.02/1.49      ( l1_pre_topc(X1) != iProver_top
% 8.02/1.49      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.02/1.49      | m1_pre_topc(sK4,X0) != iProver_top
% 8.02/1.49      | m1_pre_topc(X0,X1) != iProver_top ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_6397,c_118]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_9485,plain,
% 8.02/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK4,X0) != iProver_top
% 8.02/1.49      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.02/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_9484]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_9488,plain,
% 8.02/1.49      ( m1_pre_topc(sK4,sK5) != iProver_top
% 8.02/1.49      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 8.02/1.49      | l1_pre_topc(sK6) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_3056,c_9485]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_9630,plain,
% 8.02/1.49      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 8.02/1.49      | m1_pre_topc(sK4,sK5) != iProver_top ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_9488,c_60,c_64,c_3626]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_9631,plain,
% 8.02/1.49      ( m1_pre_topc(sK4,sK5) != iProver_top
% 8.02/1.49      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_9630]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3076,plain,
% 8.02/1.49      ( m1_subset_1(X0,X1) = iProver_top
% 8.02/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4254,plain,
% 8.02/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 8.02/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_3079,c_3076]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_19,plain,
% 8.02/1.49      ( m1_connsp_2(X0,X1,X2)
% 8.02/1.49      | ~ v3_pre_topc(X3,X1)
% 8.02/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.02/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 8.02/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.02/1.49      | ~ r2_hidden(X2,X3)
% 8.02/1.49      | ~ r1_tarski(X3,X0)
% 8.02/1.49      | v2_struct_0(X1)
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X1) ),
% 8.02/1.49      inference(cnf_transformation,[],[f103]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3068,plain,
% 8.02/1.49      ( m1_connsp_2(X0,X1,X2) = iProver_top
% 8.02/1.49      | v3_pre_topc(X3,X1) != iProver_top
% 8.02/1.49      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 8.02/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.02/1.49      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.02/1.49      | r2_hidden(X2,X3) != iProver_top
% 8.02/1.49      | r1_tarski(X3,X0) != iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | l1_pre_topc(X1) != iProver_top
% 8.02/1.49      | v2_pre_topc(X1) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_7539,plain,
% 8.02/1.49      ( m1_connsp_2(X0,X1,X2) = iProver_top
% 8.02/1.49      | v3_pre_topc(X3,X1) != iProver_top
% 8.02/1.49      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 8.02/1.49      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.02/1.49      | r2_hidden(X2,X3) != iProver_top
% 8.02/1.49      | r1_tarski(X3,X0) != iProver_top
% 8.02/1.49      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 8.02/1.49      | v2_struct_0(X1) = iProver_top
% 8.02/1.49      | l1_pre_topc(X1) != iProver_top
% 8.02/1.49      | v2_pre_topc(X1) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_4254,c_3068]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_26042,plain,
% 8.02/1.49      ( m1_connsp_2(X0,sK6,X1) = iProver_top
% 8.02/1.49      | v3_pre_topc(sK8,sK6) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK4,sK5) != iProver_top
% 8.02/1.49      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 8.02/1.49      | r2_hidden(X1,sK8) != iProver_top
% 8.02/1.49      | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
% 8.02/1.49      | r1_tarski(sK8,X0) != iProver_top
% 8.02/1.49      | v2_struct_0(sK6) = iProver_top
% 8.02/1.49      | l1_pre_topc(sK6) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK6) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_9631,c_7539]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_69,plain,
% 8.02/1.49      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_37,negated_conjecture,
% 8.02/1.49      ( v3_pre_topc(sK8,sK4) ),
% 8.02/1.49      inference(cnf_transformation,[],[f129]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_72,plain,
% 8.02/1.49      ( v3_pre_topc(sK8,sK4) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4024,plain,
% 8.02/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 8.02/1.49      | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4025,plain,
% 8.02/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 8.02/1.49      | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_4024]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4823,plain,
% 8.02/1.49      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 8.02/1.49      | ~ r1_tarski(X0,u1_struct_0(sK6)) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4824,plain,
% 8.02/1.49      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 8.02/1.49      | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_4823]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_17,plain,
% 8.02/1.49      ( ~ v3_pre_topc(X0,X1)
% 8.02/1.49      | v3_pre_topc(X0,X2)
% 8.02/1.49      | ~ m1_pre_topc(X2,X1)
% 8.02/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.02/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 8.02/1.49      | ~ l1_pre_topc(X1) ),
% 8.02/1.49      inference(cnf_transformation,[],[f139]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4697,plain,
% 8.02/1.49      ( v3_pre_topc(sK8,X0)
% 8.02/1.49      | ~ v3_pre_topc(sK8,sK4)
% 8.02/1.49      | ~ m1_pre_topc(X0,sK4)
% 8.02/1.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(X0)))
% 8.02/1.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4)))
% 8.02/1.49      | ~ l1_pre_topc(sK4) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_6056,plain,
% 8.02/1.49      ( v3_pre_topc(sK8,sK6)
% 8.02/1.49      | ~ v3_pre_topc(sK8,sK4)
% 8.02/1.49      | ~ m1_pre_topc(sK6,sK4)
% 8.02/1.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
% 8.02/1.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4)))
% 8.02/1.49      | ~ l1_pre_topc(sK4) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_4697]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_6057,plain,
% 8.02/1.49      ( v3_pre_topc(sK8,sK6) = iProver_top
% 8.02/1.49      | v3_pre_topc(sK8,sK4) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK6,sK4) != iProver_top
% 8.02/1.49      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 8.02/1.49      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 8.02/1.49      | l1_pre_topc(sK4) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_6056]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_9548,plain,
% 8.02/1.49      ( ~ m1_pre_topc(sK5,sK6)
% 8.02/1.49      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
% 8.02/1.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
% 8.02/1.49      | ~ l1_pre_topc(sK6) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_5225]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_9549,plain,
% 8.02/1.49      ( m1_pre_topc(sK5,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 8.02/1.49      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 8.02/1.49      | l1_pre_topc(sK6) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_9548]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_10549,plain,
% 8.02/1.49      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5)))
% 8.02/1.49      | ~ r2_hidden(sK8,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_4044]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_10554,plain,
% 8.02/1.49      ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 8.02/1.49      | r2_hidden(sK8,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_10549]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_35,negated_conjecture,
% 8.02/1.49      ( r1_tarski(sK8,u1_struct_0(sK5)) ),
% 8.02/1.49      inference(cnf_transformation,[],[f131]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3062,plain,
% 8.02/1.49      ( r1_tarski(sK8,u1_struct_0(sK5)) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_10888,plain,
% 8.02/1.49      ( r2_hidden(sK8,k1_zfmisc_1(X0)) = iProver_top
% 8.02/1.49      | r1_tarski(u1_struct_0(sK5),X0) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_3062,c_10050]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_11045,plain,
% 8.02/1.49      ( r2_hidden(sK8,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_3082,c_10888]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3171,plain,
% 8.02/1.49      ( m1_connsp_2(X0,sK6,X1)
% 8.02/1.49      | ~ v3_pre_topc(X2,sK6)
% 8.02/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 8.02/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 8.02/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 8.02/1.49      | ~ r2_hidden(X1,X2)
% 8.02/1.49      | ~ r1_tarski(X2,X0)
% 8.02/1.49      | v2_struct_0(sK6)
% 8.02/1.49      | ~ l1_pre_topc(sK6)
% 8.02/1.49      | ~ v2_pre_topc(sK6) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_18927,plain,
% 8.02/1.49      ( m1_connsp_2(X0,sK6,X1)
% 8.02/1.49      | ~ v3_pre_topc(sK8,sK6)
% 8.02/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 8.02/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 8.02/1.49      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
% 8.02/1.49      | ~ r2_hidden(X1,sK8)
% 8.02/1.49      | ~ r1_tarski(sK8,X0)
% 8.02/1.49      | v2_struct_0(sK6)
% 8.02/1.49      | ~ l1_pre_topc(sK6)
% 8.02/1.49      | ~ v2_pre_topc(sK6) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_3171]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_18928,plain,
% 8.02/1.49      ( m1_connsp_2(X0,sK6,X1) = iProver_top
% 8.02/1.49      | v3_pre_topc(sK8,sK6) != iProver_top
% 8.02/1.49      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 8.02/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 8.02/1.49      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 8.02/1.49      | r2_hidden(X1,sK8) != iProver_top
% 8.02/1.49      | r1_tarski(sK8,X0) != iProver_top
% 8.02/1.49      | v2_struct_0(sK6) = iProver_top
% 8.02/1.49      | l1_pre_topc(sK6) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK6) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_18927]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_28947,plain,
% 8.02/1.49      ( r1_tarski(sK8,X0) != iProver_top
% 8.02/1.49      | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
% 8.02/1.49      | r2_hidden(X1,sK8) != iProver_top
% 8.02/1.49      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 8.02/1.49      | m1_connsp_2(X0,sK6,X1) = iProver_top ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_26042,c_59,c_60,c_63,c_64,c_68,c_69,c_72,c_3626,
% 8.02/1.49                 c_4025,c_4523,c_4824,c_6057,c_9549,c_10554,c_11045,
% 8.02/1.49                 c_18928]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_28948,plain,
% 8.02/1.49      ( m1_connsp_2(X0,sK6,X1) = iProver_top
% 8.02/1.49      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 8.02/1.49      | r2_hidden(X1,sK8) != iProver_top
% 8.02/1.49      | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
% 8.02/1.49      | r1_tarski(sK8,X0) != iProver_top ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_28947]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_28955,plain,
% 8.02/1.49      ( m1_connsp_2(X0,sK6,sK10) = iProver_top
% 8.02/1.49      | r2_hidden(sK10,sK8) != iProver_top
% 8.02/1.49      | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
% 8.02/1.49      | r1_tarski(sK8,X0) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_3088,c_28948]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_36,negated_conjecture,
% 8.02/1.49      ( r2_hidden(sK9,sK8) ),
% 8.02/1.49      inference(cnf_transformation,[],[f130]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3061,plain,
% 8.02/1.49      ( r2_hidden(sK9,sK8) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3087,plain,
% 8.02/1.49      ( r2_hidden(sK10,sK8) = iProver_top ),
% 8.02/1.49      inference(light_normalisation,[status(thm)],[c_3061,c_34]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_29669,plain,
% 8.02/1.49      ( m1_connsp_2(X0,sK6,sK10) = iProver_top
% 8.02/1.49      | r1_tarski(X0,u1_struct_0(sK6)) != iProver_top
% 8.02/1.49      | r1_tarski(sK8,X0) != iProver_top ),
% 8.02/1.49      inference(global_propositional_subsumption,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_28955,c_3087]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_29683,plain,
% 8.02/1.49      ( m1_connsp_2(u1_struct_0(sK5),sK6,sK10) = iProver_top
% 8.02/1.49      | m1_pre_topc(sK6,sK6) != iProver_top
% 8.02/1.49      | m1_pre_topc(sK6,sK4) != iProver_top
% 8.02/1.49      | r1_tarski(sK8,u1_struct_0(sK5)) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_12391,c_29669]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_6026,plain,
% 8.02/1.49      ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_6027,plain,
% 8.02/1.49      ( r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_6026]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_27,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.02/1.49      | ~ m1_pre_topc(X2,X1)
% 8.02/1.49      | m1_pre_topc(X0,X2)
% 8.02/1.49      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X1) ),
% 8.02/1.49      inference(cnf_transformation,[],[f106]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3636,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,X1)
% 8.02/1.49      | ~ m1_pre_topc(sK6,X1)
% 8.02/1.49      | m1_pre_topc(sK6,X0)
% 8.02/1.49      | ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(X0))
% 8.02/1.49      | ~ l1_pre_topc(X1)
% 8.02/1.49      | ~ v2_pre_topc(X1) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_27]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4247,plain,
% 8.02/1.49      ( ~ m1_pre_topc(X0,sK4)
% 8.02/1.49      | m1_pre_topc(sK6,X0)
% 8.02/1.49      | ~ m1_pre_topc(sK6,sK4)
% 8.02/1.49      | ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(X0))
% 8.02/1.49      | ~ l1_pre_topc(sK4)
% 8.02/1.49      | ~ v2_pre_topc(sK4) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_3636]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4435,plain,
% 8.02/1.49      ( m1_pre_topc(sK6,sK6)
% 8.02/1.49      | ~ m1_pre_topc(sK6,sK4)
% 8.02/1.49      | ~ r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6))
% 8.02/1.49      | ~ l1_pre_topc(sK4)
% 8.02/1.49      | ~ v2_pre_topc(sK4) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_4247]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4436,plain,
% 8.02/1.49      ( m1_pre_topc(sK6,sK6) = iProver_top
% 8.02/1.49      | m1_pre_topc(sK6,sK4) != iProver_top
% 8.02/1.49      | r1_tarski(u1_struct_0(sK6),u1_struct_0(sK6)) != iProver_top
% 8.02/1.49      | l1_pre_topc(sK4) != iProver_top
% 8.02/1.49      | v2_pre_topc(sK4) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_4435]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_74,plain,
% 8.02/1.49      ( r1_tarski(sK8,u1_struct_0(sK5)) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(contradiction,plain,
% 8.02/1.49      ( $false ),
% 8.02/1.49      inference(minisat,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_33048,c_29683,c_6027,c_4436,c_74,c_64,c_60,c_59]) ).
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.02/1.49  
% 8.02/1.49  ------                               Statistics
% 8.02/1.49  
% 8.02/1.49  ------ General
% 8.02/1.49  
% 8.02/1.49  abstr_ref_over_cycles:                  0
% 8.02/1.49  abstr_ref_under_cycles:                 0
% 8.02/1.49  gc_basic_clause_elim:                   0
% 8.02/1.49  forced_gc_time:                         0
% 8.02/1.49  parsing_time:                           0.012
% 8.02/1.49  unif_index_cands_time:                  0.
% 8.02/1.49  unif_index_add_time:                    0.
% 8.02/1.49  orderings_time:                         0.
% 8.02/1.49  out_proof_time:                         0.027
% 8.02/1.49  total_time:                             0.929
% 8.02/1.49  num_of_symbols:                         60
% 8.02/1.49  num_of_terms:                           22454
% 8.02/1.49  
% 8.02/1.49  ------ Preprocessing
% 8.02/1.49  
% 8.02/1.49  num_of_splits:                          0
% 8.02/1.49  num_of_split_atoms:                     0
% 8.02/1.49  num_of_reused_defs:                     0
% 8.02/1.49  num_eq_ax_congr_red:                    41
% 8.02/1.49  num_of_sem_filtered_clauses:            1
% 8.02/1.49  num_of_subtypes:                        0
% 8.02/1.49  monotx_restored_types:                  0
% 8.02/1.49  sat_num_of_epr_types:                   0
% 8.02/1.49  sat_num_of_non_cyclic_types:            0
% 8.02/1.49  sat_guarded_non_collapsed_types:        0
% 8.02/1.49  num_pure_diseq_elim:                    0
% 8.02/1.49  simp_replaced_by:                       0
% 8.02/1.49  res_preprocessed:                       242
% 8.02/1.49  prep_upred:                             0
% 8.02/1.49  prep_unflattend:                        11
% 8.02/1.49  smt_new_axioms:                         0
% 8.02/1.49  pred_elim_cands:                        10
% 8.02/1.49  pred_elim:                              2
% 8.02/1.49  pred_elim_cl:                           3
% 8.02/1.49  pred_elim_cycles:                       4
% 8.02/1.49  merged_defs:                            16
% 8.02/1.49  merged_defs_ncl:                        0
% 8.02/1.49  bin_hyper_res:                          16
% 8.02/1.49  prep_cycles:                            4
% 8.02/1.49  pred_elim_time:                         0.026
% 8.02/1.49  splitting_time:                         0.
% 8.02/1.49  sem_filter_time:                        0.
% 8.02/1.49  monotx_time:                            0.001
% 8.02/1.49  subtype_inf_time:                       0.
% 8.02/1.49  
% 8.02/1.49  ------ Problem properties
% 8.02/1.49  
% 8.02/1.49  clauses:                                51
% 8.02/1.49  conjectures:                            21
% 8.02/1.49  epr:                                    21
% 8.02/1.49  horn:                                   37
% 8.02/1.49  ground:                                 21
% 8.02/1.49  unary:                                  20
% 8.02/1.49  binary:                                 8
% 8.02/1.49  lits:                                   185
% 8.02/1.49  lits_eq:                                14
% 8.02/1.49  fd_pure:                                0
% 8.02/1.49  fd_pseudo:                              0
% 8.02/1.49  fd_cond:                                0
% 8.02/1.49  fd_pseudo_cond:                         3
% 8.02/1.49  ac_symbols:                             0
% 8.02/1.49  
% 8.02/1.49  ------ Propositional Solver
% 8.02/1.49  
% 8.02/1.49  prop_solver_calls:                      29
% 8.02/1.49  prop_fast_solver_calls:                 4056
% 8.02/1.49  smt_solver_calls:                       0
% 8.02/1.49  smt_fast_solver_calls:                  0
% 8.02/1.49  prop_num_of_clauses:                    15248
% 8.02/1.49  prop_preprocess_simplified:             24609
% 8.02/1.49  prop_fo_subsumed:                       236
% 8.02/1.49  prop_solver_time:                       0.
% 8.02/1.49  smt_solver_time:                        0.
% 8.02/1.49  smt_fast_solver_time:                   0.
% 8.02/1.49  prop_fast_solver_time:                  0.
% 8.02/1.49  prop_unsat_core_time:                   0.001
% 8.02/1.49  
% 8.02/1.49  ------ QBF
% 8.02/1.49  
% 8.02/1.49  qbf_q_res:                              0
% 8.02/1.49  qbf_num_tautologies:                    0
% 8.02/1.49  qbf_prep_cycles:                        0
% 8.02/1.49  
% 8.02/1.49  ------ BMC1
% 8.02/1.49  
% 8.02/1.49  bmc1_current_bound:                     -1
% 8.02/1.49  bmc1_last_solved_bound:                 -1
% 8.02/1.49  bmc1_unsat_core_size:                   -1
% 8.02/1.49  bmc1_unsat_core_parents_size:           -1
% 8.02/1.49  bmc1_merge_next_fun:                    0
% 8.02/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.02/1.49  
% 8.02/1.49  ------ Instantiation
% 8.02/1.49  
% 8.02/1.49  inst_num_of_clauses:                    3566
% 8.02/1.49  inst_num_in_passive:                    581
% 8.02/1.49  inst_num_in_active:                     1471
% 8.02/1.49  inst_num_in_unprocessed:                1514
% 8.02/1.49  inst_num_of_loops:                      1860
% 8.02/1.49  inst_num_of_learning_restarts:          0
% 8.02/1.49  inst_num_moves_active_passive:          387
% 8.02/1.49  inst_lit_activity:                      0
% 8.02/1.49  inst_lit_activity_moves:                0
% 8.02/1.49  inst_num_tautologies:                   0
% 8.02/1.49  inst_num_prop_implied:                  0
% 8.02/1.49  inst_num_existing_simplified:           0
% 8.02/1.49  inst_num_eq_res_simplified:             0
% 8.02/1.49  inst_num_child_elim:                    0
% 8.02/1.49  inst_num_of_dismatching_blockings:      2075
% 8.02/1.49  inst_num_of_non_proper_insts:           4172
% 8.02/1.49  inst_num_of_duplicates:                 0
% 8.02/1.49  inst_inst_num_from_inst_to_res:         0
% 8.02/1.49  inst_dismatching_checking_time:         0.
% 8.02/1.49  
% 8.02/1.49  ------ Resolution
% 8.02/1.49  
% 8.02/1.49  res_num_of_clauses:                     0
% 8.02/1.49  res_num_in_passive:                     0
% 8.02/1.49  res_num_in_active:                      0
% 8.02/1.49  res_num_of_loops:                       246
% 8.02/1.49  res_forward_subset_subsumed:            266
% 8.02/1.49  res_backward_subset_subsumed:           2
% 8.02/1.49  res_forward_subsumed:                   0
% 8.02/1.49  res_backward_subsumed:                  0
% 8.02/1.49  res_forward_subsumption_resolution:     10
% 8.02/1.49  res_backward_subsumption_resolution:    0
% 8.02/1.49  res_clause_to_clause_subsumption:       6036
% 8.02/1.49  res_orphan_elimination:                 0
% 8.02/1.49  res_tautology_del:                      209
% 8.02/1.49  res_num_eq_res_simplified:              0
% 8.02/1.49  res_num_sel_changes:                    0
% 8.02/1.49  res_moves_from_active_to_pass:          0
% 8.02/1.49  
% 8.02/1.49  ------ Superposition
% 8.02/1.49  
% 8.02/1.49  sup_time_total:                         0.
% 8.02/1.49  sup_time_generating:                    0.
% 8.02/1.49  sup_time_sim_full:                      0.
% 8.02/1.49  sup_time_sim_immed:                     0.
% 8.02/1.49  
% 8.02/1.49  sup_num_of_clauses:                     1304
% 8.02/1.49  sup_num_in_active:                      362
% 8.02/1.49  sup_num_in_passive:                     942
% 8.02/1.49  sup_num_of_loops:                       371
% 8.02/1.49  sup_fw_superposition:                   985
% 8.02/1.49  sup_bw_superposition:                   929
% 8.02/1.49  sup_immediate_simplified:               223
% 8.02/1.49  sup_given_eliminated:                   3
% 8.02/1.49  comparisons_done:                       0
% 8.02/1.49  comparisons_avoided:                    0
% 8.02/1.49  
% 8.02/1.49  ------ Simplifications
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  sim_fw_subset_subsumed:                 68
% 8.02/1.49  sim_bw_subset_subsumed:                 23
% 8.02/1.49  sim_fw_subsumed:                        119
% 8.02/1.49  sim_bw_subsumed:                        81
% 8.02/1.49  sim_fw_subsumption_res:                 0
% 8.02/1.49  sim_bw_subsumption_res:                 0
% 8.02/1.49  sim_tautology_del:                      24
% 8.02/1.49  sim_eq_tautology_del:                   58
% 8.02/1.49  sim_eq_res_simp:                        0
% 8.02/1.49  sim_fw_demodulated:                     1
% 8.02/1.49  sim_bw_demodulated:                     2
% 8.02/1.49  sim_light_normalised:                   5
% 8.02/1.49  sim_joinable_taut:                      0
% 8.02/1.49  sim_joinable_simp:                      0
% 8.02/1.49  sim_ac_normalised:                      0
% 8.02/1.49  sim_smt_subsumption:                    0
% 8.02/1.49  
%------------------------------------------------------------------------------
