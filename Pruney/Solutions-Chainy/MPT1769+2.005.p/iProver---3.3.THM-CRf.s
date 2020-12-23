%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:02 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  147 (1511 expanded)
%              Number of clauses        :   86 ( 241 expanded)
%              Number of leaves         :   15 ( 658 expanded)
%              Depth                    :   18
%              Number of atoms          :  958 (33667 expanded)
%              Number of equality atoms :  198 (2058 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ! [X6] :
                              ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                             => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                  & X0 = X3 )
                               => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( ( r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                    & X0 = X3 )
                                 => ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                                  <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)
                              <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f24])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(nnf_transformation,[],[f25])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
            | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
          & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
            | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
          & X0 = X3
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X6) )
     => ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK7),X5) )
        & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
          | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK7),X5) )
        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK7)
        & X0 = X3
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
              & X0 = X3
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X6) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ? [X6] :
            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK6)
              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK6) )
            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK6)
              | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK6) )
            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
            & X0 = X3
            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X6) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                    | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                  & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                    | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                  & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                  & X0 = X3
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X6) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK5,X2),X5)
                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK5,X2),X5)
                  | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK5,X6)
                & X0 = X3
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X6) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                        | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                      & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                        | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                      & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                      & X0 = X3
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X6) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X6),X5) )
                    & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X6),X5) )
                    & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK4),u1_struct_0(X1),X4,X6)
                    & sK4 = X0
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                    & v1_funct_2(X6,u1_struct_0(sK4),u1_struct_0(X1))
                    & v1_funct_1(X6) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                            | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                          & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                            | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                          & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                          & X0 = X3
                          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X6) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK3),X5)
                          | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X6),X5) )
                        & ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK3),X5)
                          | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X6),X5) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                        & X0 = X3
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X6) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK3,X0)
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
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & X0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X4,X2),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X6),X5) )
                            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X4,X2),X5)
                              | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X6),X5) )
                            & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X3),u1_struct_0(sK2),X4,X6)
                            & X0 = X3
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2))))
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK2))
                            & v1_funct_1(X6) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK2))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK2))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
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
                                ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                                & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                                  | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                                & X0 = X3
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X6) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK1,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK1,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(sK1),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & sK1 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X1))
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

fof(f39,plain,
    ( ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) )
    & ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6)
      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) )
    & r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)
    & sK1 = sK4
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f31,f38,f37,f36,f35,f34,f33,f32])).

fof(f59,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
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

fof(f55,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f52,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f53,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f54,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    sK1 = sK4 ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f27])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X4 = X5
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f73,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_750,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1654,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_755,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1649,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_768,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X3_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_pre_topc(X2_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X3_53)
    | v2_struct_0(X1_53)
    | ~ v2_pre_topc(X3_53)
    | ~ v2_pre_topc(X1_53)
    | ~ l1_pre_topc(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v1_funct_1(X0_52)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_52,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1637,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_52,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_52)
    | v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X2_53,X3_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_3786,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK2,sK1,X0_53,sK5)
    | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK1) != iProver_top
    | m1_pre_topc(sK1,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_1637])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_38,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_39,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_40,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_45,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_46,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4934,plain,
    ( v2_pre_topc(X1_53) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK2,sK1,X0_53,sK5)
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK1) != iProver_top
    | m1_pre_topc(sK1,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3786,c_38,c_39,c_40,c_45,c_46])).

cnf(c_4935,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK2,sK1,X0_53,sK5)
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK1) != iProver_top
    | m1_pre_topc(sK1,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4934])).

cnf(c_4947,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK1,sK2,sK1,sK3,sK5)
    | m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1654,c_4935])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_769,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v1_funct_1(X0_52)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_52,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_52,X2_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1636,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_52,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_52,X2_53)
    | v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_769])).

cnf(c_3200,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_53)) = k2_tmap_1(sK1,sK2,sK5,X0_53)
    | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0_53,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_1636])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4363,plain,
    ( m1_pre_topc(X0_53,sK1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_53)) = k2_tmap_1(sK1,sK2,sK5,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3200,c_35,c_36,c_37,c_38,c_39,c_40,c_45,c_46])).

cnf(c_4364,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_53)) = k2_tmap_1(sK1,sK2,sK5,X0_53)
    | m1_pre_topc(X0_53,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4363])).

cnf(c_4371,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK1,sK2,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_1654,c_4364])).

cnf(c_4966,plain,
    ( k3_tmap_1(sK1,sK2,sK1,sK3,sK5) = k2_tmap_1(sK1,sK2,sK5,sK3)
    | m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4947,c_4371])).

cnf(c_42,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_752,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1652,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_15,negated_conjecture,
    ( sK1 = sK4 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_762,negated_conjecture,
    ( sK1 = sK4 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1679,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1652,c_762])).

cnf(c_5656,plain,
    ( k3_tmap_1(sK1,sK2,sK1,sK3,sK5) = k2_tmap_1(sK1,sK2,sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4966,c_35,c_36,c_37,c_42,c_1679])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_761,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1643,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_1702,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1643,c_762])).

cnf(c_2,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_772,plain,
    ( ~ r2_funct_2(X0_52,X1_52,X2_52,X3_52)
    | ~ v1_funct_2(X3_52,X0_52,X1_52)
    | ~ v1_funct_2(X2_52,X0_52,X1_52)
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X3_52)
    | ~ v1_funct_1(X2_52)
    | X2_52 = X3_52 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1633,plain,
    ( X0_52 = X1_52
    | r2_funct_2(X2_52,X3_52,X0_52,X1_52) != iProver_top
    | v1_funct_2(X0_52,X2_52,X3_52) != iProver_top
    | v1_funct_2(X1_52,X2_52,X3_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_2760,plain,
    ( sK5 = X0_52
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK5,X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_1633])).

cnf(c_4011,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | sK5 = X0_52
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK5,X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2760,c_45,c_46])).

cnf(c_4012,plain,
    ( sK5 = X0_52
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK5,X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_4011])).

cnf(c_4024,plain,
    ( sK7 = sK5
    | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK7) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1702,c_4012])).

cnf(c_4,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_79,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_82,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_438,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | u1_struct_0(sK4) != X4
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK2) != X5
    | u1_struct_0(sK2) != X2
    | sK7 != X3
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_439,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(u1_struct_0(sK2))
    | sK7 = sK5 ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_441,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | sK7 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_439,c_24,c_23,c_22,c_18,c_17,c_16])).

cnf(c_742,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | sK7 = sK5 ),
    inference(subtyping,[status(esa)],[c_441])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_774,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
    | ~ v1_xboole_0(X1_52)
    | v1_xboole_0(X0_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1969,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0_52)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_2363,plain,
    ( ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1969])).

cnf(c_4068,plain,
    ( sK7 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4024,c_31,c_30,c_29,c_79,c_82,c_742,c_2363])).

cnf(c_13,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_763,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1642,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_1731,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1642,c_762])).

cnf(c_4073,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK5),sK6) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4068,c_1731])).

cnf(c_5659,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5656,c_4073])).

cnf(c_12,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_764,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1641,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_1736,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1641,c_762])).

cnf(c_4074,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK5),sK6) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4068,c_1736])).

cnf(c_5660,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5656,c_4074])).

cnf(c_5664,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5659,c_5660])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.33  % CPULimit   : 60
% 0.18/0.33  % WCLimit    : 600
% 0.18/0.33  % DateTime   : Tue Dec  1 16:56:10 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  % Running in FOF mode
% 2.90/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/0.99  
% 2.90/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.90/0.99  
% 2.90/0.99  ------  iProver source info
% 2.90/0.99  
% 2.90/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.90/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.90/0.99  git: non_committed_changes: false
% 2.90/0.99  git: last_make_outside_of_git: false
% 2.90/0.99  
% 2.90/0.99  ------ 
% 2.90/0.99  
% 2.90/0.99  ------ Input Options
% 2.90/0.99  
% 2.90/0.99  --out_options                           all
% 2.90/0.99  --tptp_safe_out                         true
% 2.90/0.99  --problem_path                          ""
% 2.90/0.99  --include_path                          ""
% 2.90/0.99  --clausifier                            res/vclausify_rel
% 2.90/0.99  --clausifier_options                    --mode clausify
% 2.90/0.99  --stdin                                 false
% 2.90/0.99  --stats_out                             all
% 2.90/0.99  
% 2.90/0.99  ------ General Options
% 2.90/0.99  
% 2.90/0.99  --fof                                   false
% 2.90/0.99  --time_out_real                         305.
% 2.90/0.99  --time_out_virtual                      -1.
% 2.90/0.99  --symbol_type_check                     false
% 2.90/0.99  --clausify_out                          false
% 2.90/0.99  --sig_cnt_out                           false
% 2.90/0.99  --trig_cnt_out                          false
% 2.90/0.99  --trig_cnt_out_tolerance                1.
% 2.90/0.99  --trig_cnt_out_sk_spl                   false
% 2.90/0.99  --abstr_cl_out                          false
% 2.90/0.99  
% 2.90/0.99  ------ Global Options
% 2.90/0.99  
% 2.90/0.99  --schedule                              default
% 2.90/0.99  --add_important_lit                     false
% 2.90/0.99  --prop_solver_per_cl                    1000
% 2.90/0.99  --min_unsat_core                        false
% 2.90/0.99  --soft_assumptions                      false
% 2.90/0.99  --soft_lemma_size                       3
% 2.90/0.99  --prop_impl_unit_size                   0
% 2.90/0.99  --prop_impl_unit                        []
% 2.90/0.99  --share_sel_clauses                     true
% 2.90/0.99  --reset_solvers                         false
% 2.90/0.99  --bc_imp_inh                            [conj_cone]
% 2.90/0.99  --conj_cone_tolerance                   3.
% 2.90/0.99  --extra_neg_conj                        none
% 2.90/0.99  --large_theory_mode                     true
% 2.90/0.99  --prolific_symb_bound                   200
% 2.90/0.99  --lt_threshold                          2000
% 2.90/0.99  --clause_weak_htbl                      true
% 2.90/0.99  --gc_record_bc_elim                     false
% 2.90/0.99  
% 2.90/0.99  ------ Preprocessing Options
% 2.90/0.99  
% 2.90/0.99  --preprocessing_flag                    true
% 2.90/0.99  --time_out_prep_mult                    0.1
% 2.90/0.99  --splitting_mode                        input
% 2.90/0.99  --splitting_grd                         true
% 2.90/0.99  --splitting_cvd                         false
% 2.90/0.99  --splitting_cvd_svl                     false
% 2.90/0.99  --splitting_nvd                         32
% 2.90/0.99  --sub_typing                            true
% 2.90/0.99  --prep_gs_sim                           true
% 2.90/0.99  --prep_unflatten                        true
% 2.90/0.99  --prep_res_sim                          true
% 2.90/0.99  --prep_upred                            true
% 2.90/0.99  --prep_sem_filter                       exhaustive
% 2.90/0.99  --prep_sem_filter_out                   false
% 2.90/0.99  --pred_elim                             true
% 2.90/0.99  --res_sim_input                         true
% 2.90/0.99  --eq_ax_congr_red                       true
% 2.90/0.99  --pure_diseq_elim                       true
% 2.90/0.99  --brand_transform                       false
% 2.90/0.99  --non_eq_to_eq                          false
% 2.90/0.99  --prep_def_merge                        true
% 2.90/0.99  --prep_def_merge_prop_impl              false
% 2.90/0.99  --prep_def_merge_mbd                    true
% 2.90/0.99  --prep_def_merge_tr_red                 false
% 2.90/0.99  --prep_def_merge_tr_cl                  false
% 2.90/0.99  --smt_preprocessing                     true
% 2.90/0.99  --smt_ac_axioms                         fast
% 2.90/0.99  --preprocessed_out                      false
% 2.90/0.99  --preprocessed_stats                    false
% 2.90/0.99  
% 2.90/0.99  ------ Abstraction refinement Options
% 2.90/0.99  
% 2.90/0.99  --abstr_ref                             []
% 2.90/0.99  --abstr_ref_prep                        false
% 2.90/0.99  --abstr_ref_until_sat                   false
% 2.90/0.99  --abstr_ref_sig_restrict                funpre
% 2.90/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.90/0.99  --abstr_ref_under                       []
% 2.90/0.99  
% 2.90/0.99  ------ SAT Options
% 2.90/0.99  
% 2.90/0.99  --sat_mode                              false
% 2.90/0.99  --sat_fm_restart_options                ""
% 2.90/0.99  --sat_gr_def                            false
% 2.90/0.99  --sat_epr_types                         true
% 2.90/0.99  --sat_non_cyclic_types                  false
% 2.90/0.99  --sat_finite_models                     false
% 2.90/0.99  --sat_fm_lemmas                         false
% 2.90/0.99  --sat_fm_prep                           false
% 2.90/0.99  --sat_fm_uc_incr                        true
% 2.90/0.99  --sat_out_model                         small
% 2.90/0.99  --sat_out_clauses                       false
% 2.90/0.99  
% 2.90/0.99  ------ QBF Options
% 2.90/0.99  
% 2.90/0.99  --qbf_mode                              false
% 2.90/0.99  --qbf_elim_univ                         false
% 2.90/0.99  --qbf_dom_inst                          none
% 2.90/0.99  --qbf_dom_pre_inst                      false
% 2.90/0.99  --qbf_sk_in                             false
% 2.90/0.99  --qbf_pred_elim                         true
% 2.90/0.99  --qbf_split                             512
% 2.90/0.99  
% 2.90/0.99  ------ BMC1 Options
% 2.90/0.99  
% 2.90/0.99  --bmc1_incremental                      false
% 2.90/0.99  --bmc1_axioms                           reachable_all
% 2.90/0.99  --bmc1_min_bound                        0
% 2.90/0.99  --bmc1_max_bound                        -1
% 2.90/0.99  --bmc1_max_bound_default                -1
% 2.90/0.99  --bmc1_symbol_reachability              true
% 2.90/0.99  --bmc1_property_lemmas                  false
% 2.90/0.99  --bmc1_k_induction                      false
% 2.90/0.99  --bmc1_non_equiv_states                 false
% 2.90/0.99  --bmc1_deadlock                         false
% 2.90/0.99  --bmc1_ucm                              false
% 2.90/0.99  --bmc1_add_unsat_core                   none
% 2.90/0.99  --bmc1_unsat_core_children              false
% 2.90/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.90/0.99  --bmc1_out_stat                         full
% 2.90/0.99  --bmc1_ground_init                      false
% 2.90/0.99  --bmc1_pre_inst_next_state              false
% 2.90/0.99  --bmc1_pre_inst_state                   false
% 2.90/0.99  --bmc1_pre_inst_reach_state             false
% 2.90/0.99  --bmc1_out_unsat_core                   false
% 2.90/0.99  --bmc1_aig_witness_out                  false
% 2.90/0.99  --bmc1_verbose                          false
% 2.90/0.99  --bmc1_dump_clauses_tptp                false
% 2.90/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.90/0.99  --bmc1_dump_file                        -
% 2.90/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.90/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.90/0.99  --bmc1_ucm_extend_mode                  1
% 2.90/0.99  --bmc1_ucm_init_mode                    2
% 2.90/0.99  --bmc1_ucm_cone_mode                    none
% 2.90/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.90/0.99  --bmc1_ucm_relax_model                  4
% 2.90/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.90/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.90/0.99  --bmc1_ucm_layered_model                none
% 2.90/0.99  --bmc1_ucm_max_lemma_size               10
% 2.90/0.99  
% 2.90/0.99  ------ AIG Options
% 2.90/0.99  
% 2.90/0.99  --aig_mode                              false
% 2.90/0.99  
% 2.90/0.99  ------ Instantiation Options
% 2.90/0.99  
% 2.90/0.99  --instantiation_flag                    true
% 2.90/0.99  --inst_sos_flag                         false
% 2.90/0.99  --inst_sos_phase                        true
% 2.90/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.90/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.90/0.99  --inst_lit_sel_side                     num_symb
% 2.90/0.99  --inst_solver_per_active                1400
% 2.90/0.99  --inst_solver_calls_frac                1.
% 2.90/0.99  --inst_passive_queue_type               priority_queues
% 2.90/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.90/0.99  --inst_passive_queues_freq              [25;2]
% 2.90/0.99  --inst_dismatching                      true
% 2.90/0.99  --inst_eager_unprocessed_to_passive     true
% 2.90/0.99  --inst_prop_sim_given                   true
% 2.90/0.99  --inst_prop_sim_new                     false
% 2.90/0.99  --inst_subs_new                         false
% 2.90/0.99  --inst_eq_res_simp                      false
% 2.90/0.99  --inst_subs_given                       false
% 2.90/0.99  --inst_orphan_elimination               true
% 2.90/0.99  --inst_learning_loop_flag               true
% 2.90/0.99  --inst_learning_start                   3000
% 2.90/0.99  --inst_learning_factor                  2
% 2.90/0.99  --inst_start_prop_sim_after_learn       3
% 2.90/0.99  --inst_sel_renew                        solver
% 2.90/0.99  --inst_lit_activity_flag                true
% 2.90/0.99  --inst_restr_to_given                   false
% 2.90/0.99  --inst_activity_threshold               500
% 2.90/0.99  --inst_out_proof                        true
% 2.90/0.99  
% 2.90/0.99  ------ Resolution Options
% 2.90/0.99  
% 2.90/0.99  --resolution_flag                       true
% 2.90/0.99  --res_lit_sel                           adaptive
% 2.90/0.99  --res_lit_sel_side                      none
% 2.90/0.99  --res_ordering                          kbo
% 2.90/0.99  --res_to_prop_solver                    active
% 2.90/0.99  --res_prop_simpl_new                    false
% 2.90/0.99  --res_prop_simpl_given                  true
% 2.90/0.99  --res_passive_queue_type                priority_queues
% 2.90/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.90/0.99  --res_passive_queues_freq               [15;5]
% 2.90/0.99  --res_forward_subs                      full
% 2.90/0.99  --res_backward_subs                     full
% 2.90/0.99  --res_forward_subs_resolution           true
% 2.90/0.99  --res_backward_subs_resolution          true
% 2.90/0.99  --res_orphan_elimination                true
% 2.90/0.99  --res_time_limit                        2.
% 2.90/0.99  --res_out_proof                         true
% 2.90/0.99  
% 2.90/0.99  ------ Superposition Options
% 2.90/0.99  
% 2.90/0.99  --superposition_flag                    true
% 2.90/0.99  --sup_passive_queue_type                priority_queues
% 2.90/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.90/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.90/0.99  --demod_completeness_check              fast
% 2.90/0.99  --demod_use_ground                      true
% 2.90/0.99  --sup_to_prop_solver                    passive
% 2.90/0.99  --sup_prop_simpl_new                    true
% 2.90/0.99  --sup_prop_simpl_given                  true
% 2.90/0.99  --sup_fun_splitting                     false
% 2.90/0.99  --sup_smt_interval                      50000
% 2.90/0.99  
% 2.90/0.99  ------ Superposition Simplification Setup
% 2.90/0.99  
% 2.90/0.99  --sup_indices_passive                   []
% 2.90/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.90/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.99  --sup_full_bw                           [BwDemod]
% 2.90/0.99  --sup_immed_triv                        [TrivRules]
% 2.90/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.99  --sup_immed_bw_main                     []
% 2.90/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.90/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.99  
% 2.90/0.99  ------ Combination Options
% 2.90/0.99  
% 2.90/0.99  --comb_res_mult                         3
% 2.90/0.99  --comb_sup_mult                         2
% 2.90/0.99  --comb_inst_mult                        10
% 2.90/0.99  
% 2.90/0.99  ------ Debug Options
% 2.90/0.99  
% 2.90/0.99  --dbg_backtrace                         false
% 2.90/0.99  --dbg_dump_prop_clauses                 false
% 2.90/0.99  --dbg_dump_prop_clauses_file            -
% 2.90/0.99  --dbg_out_stat                          false
% 2.90/0.99  ------ Parsing...
% 2.90/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.90/0.99  
% 2.90/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.90/0.99  
% 2.90/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.90/0.99  
% 2.90/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.90/0.99  ------ Proving...
% 2.90/0.99  ------ Problem Properties 
% 2.90/0.99  
% 2.90/0.99  
% 2.90/0.99  clauses                                 33
% 2.90/0.99  conjectures                             22
% 2.90/0.99  EPR                                     14
% 2.90/0.99  Horn                                    25
% 2.90/0.99  unary                                   20
% 2.90/0.99  binary                                  3
% 2.90/0.99  lits                                    109
% 2.90/0.99  lits eq                                 5
% 2.90/0.99  fd_pure                                 0
% 2.90/0.99  fd_pseudo                               0
% 2.90/0.99  fd_cond                                 0
% 2.90/0.99  fd_pseudo_cond                          1
% 2.90/0.99  AC symbols                              0
% 2.90/0.99  
% 2.90/0.99  ------ Schedule dynamic 5 is on 
% 2.90/0.99  
% 2.90/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.90/0.99  
% 2.90/0.99  
% 2.90/0.99  ------ 
% 2.90/0.99  Current options:
% 2.90/0.99  ------ 
% 2.90/0.99  
% 2.90/0.99  ------ Input Options
% 2.90/0.99  
% 2.90/0.99  --out_options                           all
% 2.90/0.99  --tptp_safe_out                         true
% 2.90/0.99  --problem_path                          ""
% 2.90/0.99  --include_path                          ""
% 2.90/0.99  --clausifier                            res/vclausify_rel
% 2.90/0.99  --clausifier_options                    --mode clausify
% 2.90/0.99  --stdin                                 false
% 2.90/0.99  --stats_out                             all
% 2.90/0.99  
% 2.90/0.99  ------ General Options
% 2.90/0.99  
% 2.90/0.99  --fof                                   false
% 2.90/0.99  --time_out_real                         305.
% 2.90/0.99  --time_out_virtual                      -1.
% 2.90/0.99  --symbol_type_check                     false
% 2.90/0.99  --clausify_out                          false
% 2.90/0.99  --sig_cnt_out                           false
% 2.90/0.99  --trig_cnt_out                          false
% 2.90/0.99  --trig_cnt_out_tolerance                1.
% 2.90/0.99  --trig_cnt_out_sk_spl                   false
% 2.90/0.99  --abstr_cl_out                          false
% 2.90/0.99  
% 2.90/0.99  ------ Global Options
% 2.90/0.99  
% 2.90/0.99  --schedule                              default
% 2.90/0.99  --add_important_lit                     false
% 2.90/0.99  --prop_solver_per_cl                    1000
% 2.90/0.99  --min_unsat_core                        false
% 2.90/0.99  --soft_assumptions                      false
% 2.90/0.99  --soft_lemma_size                       3
% 2.90/0.99  --prop_impl_unit_size                   0
% 2.90/0.99  --prop_impl_unit                        []
% 2.90/0.99  --share_sel_clauses                     true
% 2.90/0.99  --reset_solvers                         false
% 2.90/0.99  --bc_imp_inh                            [conj_cone]
% 2.90/0.99  --conj_cone_tolerance                   3.
% 2.90/0.99  --extra_neg_conj                        none
% 2.90/0.99  --large_theory_mode                     true
% 2.90/0.99  --prolific_symb_bound                   200
% 2.90/0.99  --lt_threshold                          2000
% 2.90/0.99  --clause_weak_htbl                      true
% 2.90/0.99  --gc_record_bc_elim                     false
% 2.90/0.99  
% 2.90/0.99  ------ Preprocessing Options
% 2.90/0.99  
% 2.90/0.99  --preprocessing_flag                    true
% 2.90/0.99  --time_out_prep_mult                    0.1
% 2.90/0.99  --splitting_mode                        input
% 2.90/0.99  --splitting_grd                         true
% 2.90/0.99  --splitting_cvd                         false
% 2.90/0.99  --splitting_cvd_svl                     false
% 2.90/0.99  --splitting_nvd                         32
% 2.90/0.99  --sub_typing                            true
% 2.90/0.99  --prep_gs_sim                           true
% 2.90/0.99  --prep_unflatten                        true
% 2.90/0.99  --prep_res_sim                          true
% 2.90/0.99  --prep_upred                            true
% 2.90/0.99  --prep_sem_filter                       exhaustive
% 2.90/0.99  --prep_sem_filter_out                   false
% 2.90/0.99  --pred_elim                             true
% 2.90/0.99  --res_sim_input                         true
% 2.90/0.99  --eq_ax_congr_red                       true
% 2.90/0.99  --pure_diseq_elim                       true
% 2.90/0.99  --brand_transform                       false
% 2.90/0.99  --non_eq_to_eq                          false
% 2.90/0.99  --prep_def_merge                        true
% 2.90/0.99  --prep_def_merge_prop_impl              false
% 2.90/0.99  --prep_def_merge_mbd                    true
% 2.90/0.99  --prep_def_merge_tr_red                 false
% 2.90/0.99  --prep_def_merge_tr_cl                  false
% 2.90/0.99  --smt_preprocessing                     true
% 2.90/0.99  --smt_ac_axioms                         fast
% 2.90/0.99  --preprocessed_out                      false
% 2.90/0.99  --preprocessed_stats                    false
% 2.90/0.99  
% 2.90/0.99  ------ Abstraction refinement Options
% 2.90/0.99  
% 2.90/0.99  --abstr_ref                             []
% 2.90/0.99  --abstr_ref_prep                        false
% 2.90/0.99  --abstr_ref_until_sat                   false
% 2.90/0.99  --abstr_ref_sig_restrict                funpre
% 2.90/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.90/0.99  --abstr_ref_under                       []
% 2.90/0.99  
% 2.90/0.99  ------ SAT Options
% 2.90/0.99  
% 2.90/0.99  --sat_mode                              false
% 2.90/0.99  --sat_fm_restart_options                ""
% 2.90/0.99  --sat_gr_def                            false
% 2.90/0.99  --sat_epr_types                         true
% 2.90/0.99  --sat_non_cyclic_types                  false
% 2.90/0.99  --sat_finite_models                     false
% 2.90/0.99  --sat_fm_lemmas                         false
% 2.90/0.99  --sat_fm_prep                           false
% 2.90/0.99  --sat_fm_uc_incr                        true
% 2.90/0.99  --sat_out_model                         small
% 2.90/0.99  --sat_out_clauses                       false
% 2.90/0.99  
% 2.90/0.99  ------ QBF Options
% 2.90/0.99  
% 2.90/0.99  --qbf_mode                              false
% 2.90/0.99  --qbf_elim_univ                         false
% 2.90/0.99  --qbf_dom_inst                          none
% 2.90/0.99  --qbf_dom_pre_inst                      false
% 2.90/0.99  --qbf_sk_in                             false
% 2.90/0.99  --qbf_pred_elim                         true
% 2.90/0.99  --qbf_split                             512
% 2.90/0.99  
% 2.90/0.99  ------ BMC1 Options
% 2.90/0.99  
% 2.90/0.99  --bmc1_incremental                      false
% 2.90/0.99  --bmc1_axioms                           reachable_all
% 2.90/0.99  --bmc1_min_bound                        0
% 2.90/0.99  --bmc1_max_bound                        -1
% 2.90/0.99  --bmc1_max_bound_default                -1
% 2.90/0.99  --bmc1_symbol_reachability              true
% 2.90/0.99  --bmc1_property_lemmas                  false
% 2.90/0.99  --bmc1_k_induction                      false
% 2.90/0.99  --bmc1_non_equiv_states                 false
% 2.90/0.99  --bmc1_deadlock                         false
% 2.90/0.99  --bmc1_ucm                              false
% 2.90/0.99  --bmc1_add_unsat_core                   none
% 2.90/0.99  --bmc1_unsat_core_children              false
% 2.90/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.90/0.99  --bmc1_out_stat                         full
% 2.90/0.99  --bmc1_ground_init                      false
% 2.90/0.99  --bmc1_pre_inst_next_state              false
% 2.90/0.99  --bmc1_pre_inst_state                   false
% 2.90/0.99  --bmc1_pre_inst_reach_state             false
% 2.90/0.99  --bmc1_out_unsat_core                   false
% 2.90/0.99  --bmc1_aig_witness_out                  false
% 2.90/0.99  --bmc1_verbose                          false
% 2.90/0.99  --bmc1_dump_clauses_tptp                false
% 2.90/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.90/0.99  --bmc1_dump_file                        -
% 2.90/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.90/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.90/0.99  --bmc1_ucm_extend_mode                  1
% 2.90/0.99  --bmc1_ucm_init_mode                    2
% 2.90/0.99  --bmc1_ucm_cone_mode                    none
% 2.90/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.90/0.99  --bmc1_ucm_relax_model                  4
% 2.90/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.90/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.90/0.99  --bmc1_ucm_layered_model                none
% 2.90/0.99  --bmc1_ucm_max_lemma_size               10
% 2.90/0.99  
% 2.90/0.99  ------ AIG Options
% 2.90/0.99  
% 2.90/0.99  --aig_mode                              false
% 2.90/0.99  
% 2.90/0.99  ------ Instantiation Options
% 2.90/0.99  
% 2.90/0.99  --instantiation_flag                    true
% 2.90/0.99  --inst_sos_flag                         false
% 2.90/0.99  --inst_sos_phase                        true
% 2.90/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.90/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.90/0.99  --inst_lit_sel_side                     none
% 2.90/0.99  --inst_solver_per_active                1400
% 2.90/0.99  --inst_solver_calls_frac                1.
% 2.90/0.99  --inst_passive_queue_type               priority_queues
% 2.90/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.90/0.99  --inst_passive_queues_freq              [25;2]
% 2.90/0.99  --inst_dismatching                      true
% 2.90/0.99  --inst_eager_unprocessed_to_passive     true
% 2.90/0.99  --inst_prop_sim_given                   true
% 2.90/0.99  --inst_prop_sim_new                     false
% 2.90/0.99  --inst_subs_new                         false
% 2.90/0.99  --inst_eq_res_simp                      false
% 2.90/0.99  --inst_subs_given                       false
% 2.90/0.99  --inst_orphan_elimination               true
% 2.90/0.99  --inst_learning_loop_flag               true
% 2.90/0.99  --inst_learning_start                   3000
% 2.90/0.99  --inst_learning_factor                  2
% 2.90/0.99  --inst_start_prop_sim_after_learn       3
% 2.90/0.99  --inst_sel_renew                        solver
% 2.90/0.99  --inst_lit_activity_flag                true
% 2.90/0.99  --inst_restr_to_given                   false
% 2.90/0.99  --inst_activity_threshold               500
% 2.90/0.99  --inst_out_proof                        true
% 2.90/0.99  
% 2.90/0.99  ------ Resolution Options
% 2.90/0.99  
% 2.90/0.99  --resolution_flag                       false
% 2.90/0.99  --res_lit_sel                           adaptive
% 2.90/0.99  --res_lit_sel_side                      none
% 2.90/0.99  --res_ordering                          kbo
% 2.90/0.99  --res_to_prop_solver                    active
% 2.90/0.99  --res_prop_simpl_new                    false
% 2.90/0.99  --res_prop_simpl_given                  true
% 2.90/0.99  --res_passive_queue_type                priority_queues
% 2.90/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.90/0.99  --res_passive_queues_freq               [15;5]
% 2.90/0.99  --res_forward_subs                      full
% 2.90/0.99  --res_backward_subs                     full
% 2.90/0.99  --res_forward_subs_resolution           true
% 2.90/0.99  --res_backward_subs_resolution          true
% 2.90/0.99  --res_orphan_elimination                true
% 2.90/0.99  --res_time_limit                        2.
% 2.90/0.99  --res_out_proof                         true
% 2.90/0.99  
% 2.90/0.99  ------ Superposition Options
% 2.90/0.99  
% 2.90/0.99  --superposition_flag                    true
% 2.90/0.99  --sup_passive_queue_type                priority_queues
% 2.90/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.90/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.90/0.99  --demod_completeness_check              fast
% 2.90/0.99  --demod_use_ground                      true
% 2.90/0.99  --sup_to_prop_solver                    passive
% 2.90/0.99  --sup_prop_simpl_new                    true
% 2.90/0.99  --sup_prop_simpl_given                  true
% 2.90/0.99  --sup_fun_splitting                     false
% 2.90/0.99  --sup_smt_interval                      50000
% 2.90/0.99  
% 2.90/0.99  ------ Superposition Simplification Setup
% 2.90/0.99  
% 2.90/0.99  --sup_indices_passive                   []
% 2.90/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.90/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.99  --sup_full_bw                           [BwDemod]
% 2.90/0.99  --sup_immed_triv                        [TrivRules]
% 2.90/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.99  --sup_immed_bw_main                     []
% 2.90/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.90/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.99  
% 2.90/0.99  ------ Combination Options
% 2.90/0.99  
% 2.90/0.99  --comb_res_mult                         3
% 2.90/0.99  --comb_sup_mult                         2
% 2.90/0.99  --comb_inst_mult                        10
% 2.90/0.99  
% 2.90/0.99  ------ Debug Options
% 2.90/0.99  
% 2.90/0.99  --dbg_backtrace                         false
% 2.90/0.99  --dbg_dump_prop_clauses                 false
% 2.90/0.99  --dbg_dump_prop_clauses_file            -
% 2.90/0.99  --dbg_out_stat                          false
% 2.90/0.99  
% 2.90/0.99  
% 2.90/0.99  
% 2.90/0.99  
% 2.90/0.99  ------ Proving...
% 2.90/0.99  
% 2.90/0.99  
% 2.90/0.99  % SZS status Theorem for theBenchmark.p
% 2.90/0.99  
% 2.90/0.99   Resolution empty clause
% 2.90/0.99  
% 2.90/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.90/0.99  
% 2.90/0.99  fof(f8,conjecture,(
% 2.90/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 2.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f9,negated_conjecture,(
% 2.90/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 2.90/0.99    inference(negated_conjecture,[],[f8])).
% 2.90/0.99  
% 2.90/0.99  fof(f24,plain,(
% 2.90/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.90/0.99    inference(ennf_transformation,[],[f9])).
% 2.90/0.99  
% 2.90/0.99  fof(f25,plain,(
% 2.90/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.90/0.99    inference(flattening,[],[f24])).
% 2.90/0.99  
% 2.90/0.99  fof(f30,plain,(
% 2.90/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.90/0.99    inference(nnf_transformation,[],[f25])).
% 2.90/0.99  
% 2.90/0.99  fof(f31,plain,(
% 2.90/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.90/0.99    inference(flattening,[],[f30])).
% 2.90/0.99  
% 2.90/0.99  fof(f38,plain,(
% 2.90/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK7),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK7),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK7) & X0 = X3 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 2.90/0.99    introduced(choice_axiom,[])).
% 2.90/0.99  
% 2.90/0.99  fof(f37,plain,(
% 2.90/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK6) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK6)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK6) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK6)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 2.90/0.99    introduced(choice_axiom,[])).
% 2.90/0.99  
% 2.90/0.99  fof(f36,plain,(
% 2.90/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK5,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK5,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK5,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.90/0.99    introduced(choice_axiom,[])).
% 2.90/0.99  
% 2.90/0.99  fof(f35,plain,(
% 2.90/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK4),u1_struct_0(X1),X4,X6) & sK4 = X0 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.90/0.99    introduced(choice_axiom,[])).
% 2.90/0.99  
% 2.90/0.99  fof(f34,plain,(
% 2.90/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK3),X5) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X6),X5)) & (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK3),X5) | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.90/0.99    introduced(choice_axiom,[])).
% 2.90/0.99  
% 2.90/0.99  fof(f33,plain,(
% 2.90/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X3),u1_struct_0(sK2),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.90/0.99    introduced(choice_axiom,[])).
% 2.90/0.99  
% 2.90/0.99  fof(f32,plain,(
% 2.90/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK1,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK1,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK1),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK1 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.90/0.99    introduced(choice_axiom,[])).
% 2.90/0.99  
% 2.90/0.99  fof(f39,plain,(
% 2.90/0.99    (((((((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)) & (r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)) & r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) & sK1 = sK4 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.90/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f31,f38,f37,f36,f35,f34,f33,f32])).
% 2.90/0.99  
% 2.90/0.99  fof(f59,plain,(
% 2.90/0.99    m1_pre_topc(sK3,sK1)),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f64,plain,(
% 2.90/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f6,axiom,(
% 2.90/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f20,plain,(
% 2.90/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.90/0.99    inference(ennf_transformation,[],[f6])).
% 2.90/0.99  
% 2.90/0.99  fof(f21,plain,(
% 2.90/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.90/0.99    inference(flattening,[],[f20])).
% 2.90/0.99  
% 2.90/0.99  fof(f48,plain,(
% 2.90/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f21])).
% 2.90/0.99  
% 2.90/0.99  fof(f55,plain,(
% 2.90/0.99    ~v2_struct_0(sK2)),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f56,plain,(
% 2.90/0.99    v2_pre_topc(sK2)),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f57,plain,(
% 2.90/0.99    l1_pre_topc(sK2)),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f62,plain,(
% 2.90/0.99    v1_funct_1(sK5)),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f63,plain,(
% 2.90/0.99    v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f5,axiom,(
% 2.90/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f18,plain,(
% 2.90/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.90/0.99    inference(ennf_transformation,[],[f5])).
% 2.90/0.99  
% 2.90/0.99  fof(f19,plain,(
% 2.90/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.90/0.99    inference(flattening,[],[f18])).
% 2.90/0.99  
% 2.90/0.99  fof(f47,plain,(
% 2.90/0.99    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f19])).
% 2.90/0.99  
% 2.90/0.99  fof(f52,plain,(
% 2.90/0.99    ~v2_struct_0(sK1)),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f53,plain,(
% 2.90/0.99    v2_pre_topc(sK1)),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f54,plain,(
% 2.90/0.99    l1_pre_topc(sK1)),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f61,plain,(
% 2.90/0.99    m1_pre_topc(sK4,sK1)),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f71,plain,(
% 2.90/0.99    sK1 = sK4),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f70,plain,(
% 2.90/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f2,axiom,(
% 2.90/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f12,plain,(
% 2.90/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.90/0.99    inference(ennf_transformation,[],[f2])).
% 2.90/0.99  
% 2.90/0.99  fof(f13,plain,(
% 2.90/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.90/0.99    inference(flattening,[],[f12])).
% 2.90/0.99  
% 2.90/0.99  fof(f26,plain,(
% 2.90/0.99    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.90/0.99    inference(nnf_transformation,[],[f13])).
% 2.90/0.99  
% 2.90/0.99  fof(f41,plain,(
% 2.90/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f26])).
% 2.90/0.99  
% 2.90/0.99  fof(f3,axiom,(
% 2.90/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f10,plain,(
% 2.90/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.90/0.99    inference(pure_predicate_removal,[],[f3])).
% 2.90/0.99  
% 2.90/0.99  fof(f14,plain,(
% 2.90/0.99    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.90/0.99    inference(ennf_transformation,[],[f10])).
% 2.90/0.99  
% 2.90/0.99  fof(f15,plain,(
% 2.90/0.99    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.90/0.99    inference(flattening,[],[f14])).
% 2.90/0.99  
% 2.90/0.99  fof(f27,plain,(
% 2.90/0.99    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.90/0.99    introduced(choice_axiom,[])).
% 2.90/0.99  
% 2.90/0.99  fof(f28,plain,(
% 2.90/0.99    ! [X0] : ((~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.90/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f27])).
% 2.90/0.99  
% 2.90/0.99  fof(f43,plain,(
% 2.90/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f28])).
% 2.90/0.99  
% 2.90/0.99  fof(f44,plain,(
% 2.90/0.99    ( ! [X0] : (~v1_xboole_0(sK0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f28])).
% 2.90/0.99  
% 2.90/0.99  fof(f4,axiom,(
% 2.90/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f16,plain,(
% 2.90/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.90/0.99    inference(ennf_transformation,[],[f4])).
% 2.90/0.99  
% 2.90/0.99  fof(f17,plain,(
% 2.90/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.90/0.99    inference(flattening,[],[f16])).
% 2.90/0.99  
% 2.90/0.99  fof(f29,plain,(
% 2.90/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.90/0.99    inference(nnf_transformation,[],[f17])).
% 2.90/0.99  
% 2.90/0.99  fof(f45,plain,(
% 2.90/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f29])).
% 2.90/0.99  
% 2.90/0.99  fof(f72,plain,(
% 2.90/0.99    r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f68,plain,(
% 2.90/0.99    v1_funct_1(sK7)),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f69,plain,(
% 2.90/0.99    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2))),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f1,axiom,(
% 2.90/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.99  
% 2.90/0.99  fof(f11,plain,(
% 2.90/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.90/0.99    inference(ennf_transformation,[],[f1])).
% 2.90/0.99  
% 2.90/0.99  fof(f40,plain,(
% 2.90/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.90/0.99    inference(cnf_transformation,[],[f11])).
% 2.90/0.99  
% 2.90/0.99  fof(f73,plain,(
% 2.90/0.99    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  fof(f74,plain,(
% 2.90/0.99    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)),
% 2.90/0.99    inference(cnf_transformation,[],[f39])).
% 2.90/0.99  
% 2.90/0.99  cnf(c_27,negated_conjecture,
% 2.90/0.99      ( m1_pre_topc(sK3,sK1) ),
% 2.90/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_750,negated_conjecture,
% 2.90/0.99      ( m1_pre_topc(sK3,sK1) ),
% 2.90/0.99      inference(subtyping,[status(esa)],[c_27]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1654,plain,
% 2.90/0.99      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_22,negated_conjecture,
% 2.90/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.90/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_755,negated_conjecture,
% 2.90/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.90/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1649,plain,
% 2.90/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_8,plain,
% 2.90/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.90/0.99      | ~ m1_pre_topc(X3,X4)
% 2.90/0.99      | ~ m1_pre_topc(X1,X4)
% 2.90/0.99      | ~ m1_pre_topc(X3,X1)
% 2.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.90/0.99      | v2_struct_0(X4)
% 2.90/0.99      | v2_struct_0(X2)
% 2.90/0.99      | ~ v2_pre_topc(X4)
% 2.90/0.99      | ~ v2_pre_topc(X2)
% 2.90/0.99      | ~ l1_pre_topc(X4)
% 2.90/0.99      | ~ l1_pre_topc(X2)
% 2.90/0.99      | ~ v1_funct_1(X0)
% 2.90/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.90/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_768,plain,
% 2.90/0.99      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 2.90/0.99      | ~ m1_pre_topc(X2_53,X3_53)
% 2.90/0.99      | ~ m1_pre_topc(X0_53,X3_53)
% 2.90/0.99      | ~ m1_pre_topc(X2_53,X0_53)
% 2.90/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 2.90/0.99      | v2_struct_0(X3_53)
% 2.90/0.99      | v2_struct_0(X1_53)
% 2.90/0.99      | ~ v2_pre_topc(X3_53)
% 2.90/0.99      | ~ v2_pre_topc(X1_53)
% 2.90/0.99      | ~ l1_pre_topc(X3_53)
% 2.90/0.99      | ~ l1_pre_topc(X1_53)
% 2.90/0.99      | ~ v1_funct_1(X0_52)
% 2.90/0.99      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_52,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_52) ),
% 2.90/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1637,plain,
% 2.90/0.99      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_52,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_52)
% 2.90/0.99      | v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 2.90/0.99      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.90/0.99      | m1_pre_topc(X2_53,X3_53) != iProver_top
% 2.90/0.99      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 2.90/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.90/0.99      | v2_struct_0(X3_53) = iProver_top
% 2.90/0.99      | v2_struct_0(X1_53) = iProver_top
% 2.90/0.99      | v2_pre_topc(X3_53) != iProver_top
% 2.90/0.99      | v2_pre_topc(X1_53) != iProver_top
% 2.90/0.99      | l1_pre_topc(X3_53) != iProver_top
% 2.90/0.99      | l1_pre_topc(X1_53) != iProver_top
% 2.90/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_768]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3786,plain,
% 2.90/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK2,sK1,X0_53,sK5)
% 2.90/0.99      | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.90/0.99      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.90/0.99      | m1_pre_topc(X0_53,sK1) != iProver_top
% 2.90/0.99      | m1_pre_topc(sK1,X1_53) != iProver_top
% 2.90/0.99      | v2_struct_0(X1_53) = iProver_top
% 2.90/0.99      | v2_struct_0(sK2) = iProver_top
% 2.90/0.99      | v2_pre_topc(X1_53) != iProver_top
% 2.90/0.99      | v2_pre_topc(sK2) != iProver_top
% 2.90/0.99      | l1_pre_topc(X1_53) != iProver_top
% 2.90/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.90/0.99      | v1_funct_1(sK5) != iProver_top ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_1649,c_1637]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_31,negated_conjecture,
% 2.90/0.99      ( ~ v2_struct_0(sK2) ),
% 2.90/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_38,plain,
% 2.90/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_30,negated_conjecture,
% 2.90/0.99      ( v2_pre_topc(sK2) ),
% 2.90/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_39,plain,
% 2.90/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_29,negated_conjecture,
% 2.90/0.99      ( l1_pre_topc(sK2) ),
% 2.90/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_40,plain,
% 2.90/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_24,negated_conjecture,
% 2.90/0.99      ( v1_funct_1(sK5) ),
% 2.90/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_45,plain,
% 2.90/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_23,negated_conjecture,
% 2.90/0.99      ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.90/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_46,plain,
% 2.90/0.99      ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4934,plain,
% 2.90/0.99      ( v2_pre_topc(X1_53) != iProver_top
% 2.90/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK2,sK1,X0_53,sK5)
% 2.90/0.99      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.90/0.99      | m1_pre_topc(X0_53,sK1) != iProver_top
% 2.90/0.99      | m1_pre_topc(sK1,X1_53) != iProver_top
% 2.90/0.99      | v2_struct_0(X1_53) = iProver_top
% 2.90/0.99      | l1_pre_topc(X1_53) != iProver_top ),
% 2.90/0.99      inference(global_propositional_subsumption,
% 2.90/0.99                [status(thm)],
% 2.90/0.99                [c_3786,c_38,c_39,c_40,c_45,c_46]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4935,plain,
% 2.90/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK2,sK1,X0_53,sK5)
% 2.90/0.99      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 2.90/0.99      | m1_pre_topc(X0_53,sK1) != iProver_top
% 2.90/0.99      | m1_pre_topc(sK1,X1_53) != iProver_top
% 2.90/0.99      | v2_struct_0(X1_53) = iProver_top
% 2.90/0.99      | v2_pre_topc(X1_53) != iProver_top
% 2.90/0.99      | l1_pre_topc(X1_53) != iProver_top ),
% 2.90/0.99      inference(renaming,[status(thm)],[c_4934]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4947,plain,
% 2.90/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK1,sK2,sK1,sK3,sK5)
% 2.90/0.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.90/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.90/0.99      | v2_struct_0(sK1) = iProver_top
% 2.90/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.90/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_1654,c_4935]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_7,plain,
% 2.90/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.90/0.99      | ~ m1_pre_topc(X3,X1)
% 2.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.90/0.99      | v2_struct_0(X1)
% 2.90/0.99      | v2_struct_0(X2)
% 2.90/0.99      | ~ v2_pre_topc(X1)
% 2.90/0.99      | ~ v2_pre_topc(X2)
% 2.90/0.99      | ~ l1_pre_topc(X1)
% 2.90/0.99      | ~ l1_pre_topc(X2)
% 2.90/0.99      | ~ v1_funct_1(X0)
% 2.90/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.90/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_769,plain,
% 2.90/0.99      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 2.90/0.99      | ~ m1_pre_topc(X2_53,X0_53)
% 2.90/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 2.90/0.99      | v2_struct_0(X1_53)
% 2.90/0.99      | v2_struct_0(X0_53)
% 2.90/0.99      | ~ v2_pre_topc(X1_53)
% 2.90/0.99      | ~ v2_pre_topc(X0_53)
% 2.90/0.99      | ~ l1_pre_topc(X1_53)
% 2.90/0.99      | ~ l1_pre_topc(X0_53)
% 2.90/0.99      | ~ v1_funct_1(X0_52)
% 2.90/0.99      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_52,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_52,X2_53) ),
% 2.90/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1636,plain,
% 2.90/0.99      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_52,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_52,X2_53)
% 2.90/0.99      | v1_funct_2(X0_52,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 2.90/0.99      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 2.90/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.90/0.99      | v2_struct_0(X1_53) = iProver_top
% 2.90/0.99      | v2_struct_0(X0_53) = iProver_top
% 2.90/0.99      | v2_pre_topc(X1_53) != iProver_top
% 2.90/0.99      | v2_pre_topc(X0_53) != iProver_top
% 2.90/0.99      | l1_pre_topc(X1_53) != iProver_top
% 2.90/0.99      | l1_pre_topc(X0_53) != iProver_top
% 2.90/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_769]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_3200,plain,
% 2.90/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_53)) = k2_tmap_1(sK1,sK2,sK5,X0_53)
% 2.90/0.99      | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.90/0.99      | m1_pre_topc(X0_53,sK1) != iProver_top
% 2.90/0.99      | v2_struct_0(sK1) = iProver_top
% 2.90/0.99      | v2_struct_0(sK2) = iProver_top
% 2.90/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.90/0.99      | v2_pre_topc(sK2) != iProver_top
% 2.90/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.90/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.90/0.99      | v1_funct_1(sK5) != iProver_top ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_1649,c_1636]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_34,negated_conjecture,
% 2.90/0.99      ( ~ v2_struct_0(sK1) ),
% 2.90/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_35,plain,
% 2.90/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_33,negated_conjecture,
% 2.90/0.99      ( v2_pre_topc(sK1) ),
% 2.90/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_36,plain,
% 2.90/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_32,negated_conjecture,
% 2.90/0.99      ( l1_pre_topc(sK1) ),
% 2.90/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_37,plain,
% 2.90/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4363,plain,
% 2.90/0.99      ( m1_pre_topc(X0_53,sK1) != iProver_top
% 2.90/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_53)) = k2_tmap_1(sK1,sK2,sK5,X0_53) ),
% 2.90/0.99      inference(global_propositional_subsumption,
% 2.90/0.99                [status(thm)],
% 2.90/0.99                [c_3200,c_35,c_36,c_37,c_38,c_39,c_40,c_45,c_46]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4364,plain,
% 2.90/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(X0_53)) = k2_tmap_1(sK1,sK2,sK5,X0_53)
% 2.90/0.99      | m1_pre_topc(X0_53,sK1) != iProver_top ),
% 2.90/0.99      inference(renaming,[status(thm)],[c_4363]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4371,plain,
% 2.90/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK1,sK2,sK5,sK3) ),
% 2.90/0.99      inference(superposition,[status(thm)],[c_1654,c_4364]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_4966,plain,
% 2.90/0.99      ( k3_tmap_1(sK1,sK2,sK1,sK3,sK5) = k2_tmap_1(sK1,sK2,sK5,sK3)
% 2.90/0.99      | m1_pre_topc(sK1,sK1) != iProver_top
% 2.90/0.99      | m1_pre_topc(sK3,sK1) != iProver_top
% 2.90/0.99      | v2_struct_0(sK1) = iProver_top
% 2.90/0.99      | v2_pre_topc(sK1) != iProver_top
% 2.90/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.90/0.99      inference(light_normalisation,[status(thm)],[c_4947,c_4371]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_42,plain,
% 2.90/0.99      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_25,negated_conjecture,
% 2.90/0.99      ( m1_pre_topc(sK4,sK1) ),
% 2.90/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_752,negated_conjecture,
% 2.90/0.99      ( m1_pre_topc(sK4,sK1) ),
% 2.90/0.99      inference(subtyping,[status(esa)],[c_25]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1652,plain,
% 2.90/0.99      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_15,negated_conjecture,
% 2.90/0.99      ( sK1 = sK4 ),
% 2.90/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_762,negated_conjecture,
% 2.90/0.99      ( sK1 = sK4 ),
% 2.90/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1679,plain,
% 2.90/0.99      ( m1_pre_topc(sK1,sK1) = iProver_top ),
% 2.90/0.99      inference(light_normalisation,[status(thm)],[c_1652,c_762]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_5656,plain,
% 2.90/0.99      ( k3_tmap_1(sK1,sK2,sK1,sK3,sK5) = k2_tmap_1(sK1,sK2,sK5,sK3) ),
% 2.90/0.99      inference(global_propositional_subsumption,
% 2.90/0.99                [status(thm)],
% 2.90/0.99                [c_4966,c_35,c_36,c_37,c_42,c_1679]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_16,negated_conjecture,
% 2.90/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 2.90/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_761,negated_conjecture,
% 2.90/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 2.90/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1643,plain,
% 2.90/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 2.90/0.99      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_1702,plain,
% 2.90/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 2.90/0.99      inference(light_normalisation,[status(thm)],[c_1643,c_762]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_2,plain,
% 2.90/0.99      ( ~ r2_funct_2(X0,X1,X2,X3)
% 2.90/0.99      | ~ v1_funct_2(X3,X0,X1)
% 2.90/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.90/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.90/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.90/0.99      | ~ v1_funct_1(X3)
% 2.90/0.99      | ~ v1_funct_1(X2)
% 2.90/0.99      | X2 = X3 ),
% 2.90/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.90/0.99  
% 2.90/0.99  cnf(c_772,plain,
% 2.90/1.00      ( ~ r2_funct_2(X0_52,X1_52,X2_52,X3_52)
% 2.90/1.00      | ~ v1_funct_2(X3_52,X0_52,X1_52)
% 2.90/1.00      | ~ v1_funct_2(X2_52,X0_52,X1_52)
% 2.90/1.00      | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.90/1.00      | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.90/1.00      | ~ v1_funct_1(X3_52)
% 2.90/1.00      | ~ v1_funct_1(X2_52)
% 2.90/1.00      | X2_52 = X3_52 ),
% 2.90/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_1633,plain,
% 2.90/1.00      ( X0_52 = X1_52
% 2.90/1.00      | r2_funct_2(X2_52,X3_52,X0_52,X1_52) != iProver_top
% 2.90/1.00      | v1_funct_2(X0_52,X2_52,X3_52) != iProver_top
% 2.90/1.00      | v1_funct_2(X1_52,X2_52,X3_52) != iProver_top
% 2.90/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
% 2.90/1.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
% 2.90/1.00      | v1_funct_1(X0_52) != iProver_top
% 2.90/1.00      | v1_funct_1(X1_52) != iProver_top ),
% 2.90/1.00      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_2760,plain,
% 2.90/1.00      ( sK5 = X0_52
% 2.90/1.00      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK5,X0_52) != iProver_top
% 2.90/1.00      | v1_funct_2(X0_52,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.90/1.00      | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.90/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.90/1.00      | v1_funct_1(X0_52) != iProver_top
% 2.90/1.00      | v1_funct_1(sK5) != iProver_top ),
% 2.90/1.00      inference(superposition,[status(thm)],[c_1649,c_1633]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_4011,plain,
% 2.90/1.00      ( v1_funct_1(X0_52) != iProver_top
% 2.90/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.90/1.00      | sK5 = X0_52
% 2.90/1.00      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK5,X0_52) != iProver_top
% 2.90/1.00      | v1_funct_2(X0_52,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
% 2.90/1.00      inference(global_propositional_subsumption,
% 2.90/1.00                [status(thm)],
% 2.90/1.00                [c_2760,c_45,c_46]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_4012,plain,
% 2.90/1.00      ( sK5 = X0_52
% 2.90/1.00      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK5,X0_52) != iProver_top
% 2.90/1.00      | v1_funct_2(X0_52,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.90/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 2.90/1.00      | v1_funct_1(X0_52) != iProver_top ),
% 2.90/1.00      inference(renaming,[status(thm)],[c_4011]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_4024,plain,
% 2.90/1.00      ( sK7 = sK5
% 2.90/1.00      | r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK7) != iProver_top
% 2.90/1.00      | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.90/1.00      | v1_funct_1(sK7) != iProver_top ),
% 2.90/1.00      inference(superposition,[status(thm)],[c_1702,c_4012]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_4,plain,
% 2.90/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.90/1.00      | v2_struct_0(X0)
% 2.90/1.00      | ~ v2_pre_topc(X0)
% 2.90/1.00      | ~ l1_pre_topc(X0) ),
% 2.90/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_79,plain,
% 2.90/1.00      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.90/1.00      | v2_struct_0(sK2)
% 2.90/1.00      | ~ v2_pre_topc(sK2)
% 2.90/1.00      | ~ l1_pre_topc(sK2) ),
% 2.90/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_3,plain,
% 2.90/1.00      ( v2_struct_0(X0)
% 2.90/1.00      | ~ v2_pre_topc(X0)
% 2.90/1.00      | ~ l1_pre_topc(X0)
% 2.90/1.00      | ~ v1_xboole_0(sK0(X0)) ),
% 2.90/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_82,plain,
% 2.90/1.00      ( v2_struct_0(sK2)
% 2.90/1.00      | ~ v2_pre_topc(sK2)
% 2.90/1.00      | ~ l1_pre_topc(sK2)
% 2.90/1.00      | ~ v1_xboole_0(sK0(sK2)) ),
% 2.90/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_6,plain,
% 2.90/1.00      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 2.90/1.00      | ~ v1_funct_2(X5,X2,X3)
% 2.90/1.00      | ~ v1_funct_2(X4,X0,X1)
% 2.90/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.90/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.90/1.00      | ~ v1_funct_1(X5)
% 2.90/1.00      | ~ v1_funct_1(X4)
% 2.90/1.00      | v1_xboole_0(X1)
% 2.90/1.00      | v1_xboole_0(X3)
% 2.90/1.00      | X4 = X5 ),
% 2.90/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_14,negated_conjecture,
% 2.90/1.00      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) ),
% 2.90/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_438,plain,
% 2.90/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.90/1.00      | ~ v1_funct_2(X3,X4,X5)
% 2.90/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.90/1.00      | ~ v1_funct_1(X0)
% 2.90/1.00      | ~ v1_funct_1(X3)
% 2.90/1.00      | v1_xboole_0(X2)
% 2.90/1.00      | v1_xboole_0(X5)
% 2.90/1.00      | X3 = X0
% 2.90/1.00      | u1_struct_0(sK4) != X4
% 2.90/1.00      | u1_struct_0(sK1) != X1
% 2.90/1.00      | u1_struct_0(sK2) != X5
% 2.90/1.00      | u1_struct_0(sK2) != X2
% 2.90/1.00      | sK7 != X3
% 2.90/1.00      | sK5 != X0 ),
% 2.90/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_14]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_439,plain,
% 2.90/1.00      ( ~ v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2))
% 2.90/1.00      | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.90/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.90/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.90/1.00      | ~ v1_funct_1(sK7)
% 2.90/1.00      | ~ v1_funct_1(sK5)
% 2.90/1.00      | v1_xboole_0(u1_struct_0(sK2))
% 2.90/1.00      | sK7 = sK5 ),
% 2.90/1.00      inference(unflattening,[status(thm)],[c_438]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_18,negated_conjecture,
% 2.90/1.00      ( v1_funct_1(sK7) ),
% 2.90/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_17,negated_conjecture,
% 2.90/1.00      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 2.90/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_441,plain,
% 2.90/1.00      ( v1_xboole_0(u1_struct_0(sK2)) | sK7 = sK5 ),
% 2.90/1.00      inference(global_propositional_subsumption,
% 2.90/1.00                [status(thm)],
% 2.90/1.00                [c_439,c_24,c_23,c_22,c_18,c_17,c_16]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_742,plain,
% 2.90/1.00      ( v1_xboole_0(u1_struct_0(sK2)) | sK7 = sK5 ),
% 2.90/1.00      inference(subtyping,[status(esa)],[c_441]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_0,plain,
% 2.90/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.90/1.00      | ~ v1_xboole_0(X1)
% 2.90/1.00      | v1_xboole_0(X0) ),
% 2.90/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_774,plain,
% 2.90/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
% 2.90/1.00      | ~ v1_xboole_0(X1_52)
% 2.90/1.00      | v1_xboole_0(X0_52) ),
% 2.90/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_1969,plain,
% 2.90/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.90/1.00      | v1_xboole_0(X0_52)
% 2.90/1.00      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.90/1.00      inference(instantiation,[status(thm)],[c_774]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_2363,plain,
% 2.90/1.00      ( ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.90/1.00      | ~ v1_xboole_0(u1_struct_0(sK2))
% 2.90/1.00      | v1_xboole_0(sK0(sK2)) ),
% 2.90/1.00      inference(instantiation,[status(thm)],[c_1969]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_4068,plain,
% 2.90/1.00      ( sK7 = sK5 ),
% 2.90/1.00      inference(global_propositional_subsumption,
% 2.90/1.00                [status(thm)],
% 2.90/1.00                [c_4024,c_31,c_30,c_29,c_79,c_82,c_742,c_2363]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_13,negated_conjecture,
% 2.90/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
% 2.90/1.00      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
% 2.90/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_763,negated_conjecture,
% 2.90/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
% 2.90/1.00      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
% 2.90/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_1642,plain,
% 2.90/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) = iProver_top
% 2.90/1.00      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 2.90/1.00      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_1731,plain,
% 2.90/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) = iProver_top
% 2.90/1.00      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 2.90/1.00      inference(light_normalisation,[status(thm)],[c_1642,c_762]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_4073,plain,
% 2.90/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK5),sK6) = iProver_top
% 2.90/1.00      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 2.90/1.00      inference(demodulation,[status(thm)],[c_4068,c_1731]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_5659,plain,
% 2.90/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 2.90/1.00      inference(demodulation,[status(thm)],[c_5656,c_4073]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_12,negated_conjecture,
% 2.90/1.00      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
% 2.90/1.00      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
% 2.90/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_764,negated_conjecture,
% 2.90/1.00      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
% 2.90/1.00      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
% 2.90/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_1641,plain,
% 2.90/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) != iProver_top
% 2.90/1.00      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 2.90/1.00      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_1736,plain,
% 2.90/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) != iProver_top
% 2.90/1.00      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 2.90/1.00      inference(light_normalisation,[status(thm)],[c_1641,c_762]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_4074,plain,
% 2.90/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK5),sK6) != iProver_top
% 2.90/1.00      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 2.90/1.00      inference(demodulation,[status(thm)],[c_4068,c_1736]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_5660,plain,
% 2.90/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 2.90/1.00      inference(demodulation,[status(thm)],[c_5656,c_4074]) ).
% 2.90/1.00  
% 2.90/1.00  cnf(c_5664,plain,
% 2.90/1.00      ( $false ),
% 2.90/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5659,c_5660]) ).
% 2.90/1.00  
% 2.90/1.00  
% 2.90/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.90/1.00  
% 2.90/1.00  ------                               Statistics
% 2.90/1.00  
% 2.90/1.00  ------ General
% 2.90/1.00  
% 2.90/1.00  abstr_ref_over_cycles:                  0
% 2.90/1.00  abstr_ref_under_cycles:                 0
% 2.90/1.00  gc_basic_clause_elim:                   0
% 2.90/1.00  forced_gc_time:                         0
% 2.90/1.00  parsing_time:                           0.012
% 2.90/1.00  unif_index_cands_time:                  0.
% 2.90/1.00  unif_index_add_time:                    0.
% 2.90/1.00  orderings_time:                         0.
% 2.90/1.00  out_proof_time:                         0.012
% 2.90/1.00  total_time:                             0.233
% 2.90/1.00  num_of_symbols:                         58
% 2.90/1.00  num_of_terms:                           5116
% 2.90/1.00  
% 2.90/1.00  ------ Preprocessing
% 2.90/1.00  
% 2.90/1.00  num_of_splits:                          0
% 2.90/1.00  num_of_split_atoms:                     0
% 2.90/1.00  num_of_reused_defs:                     0
% 2.90/1.00  num_eq_ax_congr_red:                    6
% 2.90/1.00  num_of_sem_filtered_clauses:            1
% 2.90/1.00  num_of_subtypes:                        3
% 2.90/1.00  monotx_restored_types:                  0
% 2.90/1.00  sat_num_of_epr_types:                   0
% 2.90/1.00  sat_num_of_non_cyclic_types:            0
% 2.90/1.00  sat_guarded_non_collapsed_types:        1
% 2.90/1.00  num_pure_diseq_elim:                    0
% 2.90/1.00  simp_replaced_by:                       0
% 2.90/1.00  res_preprocessed:                       175
% 2.90/1.00  prep_upred:                             0
% 2.90/1.00  prep_unflattend:                        12
% 2.90/1.00  smt_new_axioms:                         0
% 2.90/1.00  pred_elim_cands:                        9
% 2.90/1.00  pred_elim:                              1
% 2.90/1.00  pred_elim_cl:                           2
% 2.90/1.00  pred_elim_cycles:                       3
% 2.90/1.00  merged_defs:                            8
% 2.90/1.00  merged_defs_ncl:                        0
% 2.90/1.00  bin_hyper_res:                          8
% 2.90/1.00  prep_cycles:                            4
% 2.90/1.00  pred_elim_time:                         0.002
% 2.90/1.00  splitting_time:                         0.
% 2.90/1.00  sem_filter_time:                        0.
% 2.90/1.00  monotx_time:                            0.
% 2.90/1.00  subtype_inf_time:                       0.001
% 2.90/1.00  
% 2.90/1.00  ------ Problem properties
% 2.90/1.00  
% 2.90/1.00  clauses:                                33
% 2.90/1.00  conjectures:                            22
% 2.90/1.00  epr:                                    14
% 2.90/1.00  horn:                                   25
% 2.90/1.00  ground:                                 23
% 2.90/1.00  unary:                                  20
% 2.90/1.00  binary:                                 3
% 2.90/1.00  lits:                                   109
% 2.90/1.00  lits_eq:                                5
% 2.90/1.00  fd_pure:                                0
% 2.90/1.00  fd_pseudo:                              0
% 2.90/1.00  fd_cond:                                0
% 2.90/1.00  fd_pseudo_cond:                         1
% 2.90/1.00  ac_symbols:                             0
% 2.90/1.00  
% 2.90/1.00  ------ Propositional Solver
% 2.90/1.00  
% 2.90/1.00  prop_solver_calls:                      27
% 2.90/1.00  prop_fast_solver_calls:                 1678
% 2.90/1.00  smt_solver_calls:                       0
% 2.90/1.00  smt_fast_solver_calls:                  0
% 2.90/1.00  prop_num_of_clauses:                    1749
% 2.90/1.00  prop_preprocess_simplified:             5661
% 2.90/1.00  prop_fo_subsumed:                       110
% 2.90/1.00  prop_solver_time:                       0.
% 2.90/1.00  smt_solver_time:                        0.
% 2.90/1.00  smt_fast_solver_time:                   0.
% 2.90/1.00  prop_fast_solver_time:                  0.
% 2.90/1.00  prop_unsat_core_time:                   0.
% 2.90/1.00  
% 2.90/1.00  ------ QBF
% 2.90/1.00  
% 2.90/1.00  qbf_q_res:                              0
% 2.90/1.00  qbf_num_tautologies:                    0
% 2.90/1.00  qbf_prep_cycles:                        0
% 2.90/1.00  
% 2.90/1.00  ------ BMC1
% 2.90/1.00  
% 2.90/1.00  bmc1_current_bound:                     -1
% 2.90/1.00  bmc1_last_solved_bound:                 -1
% 2.90/1.00  bmc1_unsat_core_size:                   -1
% 2.90/1.00  bmc1_unsat_core_parents_size:           -1
% 2.90/1.00  bmc1_merge_next_fun:                    0
% 2.90/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.90/1.00  
% 2.90/1.00  ------ Instantiation
% 2.90/1.00  
% 2.90/1.00  inst_num_of_clauses:                    510
% 2.90/1.00  inst_num_in_passive:                    140
% 2.90/1.00  inst_num_in_active:                     303
% 2.90/1.00  inst_num_in_unprocessed:                68
% 2.90/1.00  inst_num_of_loops:                      310
% 2.90/1.00  inst_num_of_learning_restarts:          0
% 2.90/1.00  inst_num_moves_active_passive:          4
% 2.90/1.00  inst_lit_activity:                      0
% 2.90/1.00  inst_lit_activity_moves:                0
% 2.90/1.00  inst_num_tautologies:                   0
% 2.90/1.00  inst_num_prop_implied:                  0
% 2.90/1.00  inst_num_existing_simplified:           0
% 2.90/1.00  inst_num_eq_res_simplified:             0
% 2.90/1.00  inst_num_child_elim:                    0
% 2.90/1.00  inst_num_of_dismatching_blockings:      84
% 2.90/1.00  inst_num_of_non_proper_insts:           436
% 2.90/1.00  inst_num_of_duplicates:                 0
% 2.90/1.00  inst_inst_num_from_inst_to_res:         0
% 2.90/1.00  inst_dismatching_checking_time:         0.
% 2.90/1.00  
% 2.90/1.00  ------ Resolution
% 2.90/1.00  
% 2.90/1.00  res_num_of_clauses:                     0
% 2.90/1.00  res_num_in_passive:                     0
% 2.90/1.00  res_num_in_active:                      0
% 2.90/1.00  res_num_of_loops:                       179
% 2.90/1.00  res_forward_subset_subsumed:            35
% 2.90/1.00  res_backward_subset_subsumed:           2
% 2.90/1.00  res_forward_subsumed:                   0
% 2.90/1.00  res_backward_subsumed:                  0
% 2.90/1.00  res_forward_subsumption_resolution:     0
% 2.90/1.00  res_backward_subsumption_resolution:    0
% 2.90/1.00  res_clause_to_clause_subsumption:       209
% 2.90/1.00  res_orphan_elimination:                 0
% 2.90/1.00  res_tautology_del:                      50
% 2.90/1.00  res_num_eq_res_simplified:              0
% 2.90/1.00  res_num_sel_changes:                    0
% 2.90/1.00  res_moves_from_active_to_pass:          0
% 2.90/1.00  
% 2.90/1.00  ------ Superposition
% 2.90/1.00  
% 2.90/1.00  sup_time_total:                         0.
% 2.90/1.00  sup_time_generating:                    0.
% 2.90/1.00  sup_time_sim_full:                      0.
% 2.90/1.00  sup_time_sim_immed:                     0.
% 2.90/1.00  
% 2.90/1.00  sup_num_of_clauses:                     65
% 2.90/1.00  sup_num_in_active:                      52
% 2.90/1.00  sup_num_in_passive:                     13
% 2.90/1.00  sup_num_of_loops:                       61
% 2.90/1.00  sup_fw_superposition:                   29
% 2.90/1.00  sup_bw_superposition:                   19
% 2.90/1.00  sup_immediate_simplified:               2
% 2.90/1.00  sup_given_eliminated:                   0
% 2.90/1.00  comparisons_done:                       0
% 2.90/1.00  comparisons_avoided:                    0
% 2.90/1.00  
% 2.90/1.00  ------ Simplifications
% 2.90/1.00  
% 2.90/1.00  
% 2.90/1.00  sim_fw_subset_subsumed:                 0
% 2.90/1.00  sim_bw_subset_subsumed:                 1
% 2.90/1.00  sim_fw_subsumed:                        0
% 2.90/1.00  sim_bw_subsumed:                        0
% 2.90/1.00  sim_fw_subsumption_res:                 4
% 2.90/1.00  sim_bw_subsumption_res:                 0
% 2.90/1.00  sim_tautology_del:                      1
% 2.90/1.00  sim_eq_tautology_del:                   2
% 2.90/1.00  sim_eq_res_simp:                        0
% 2.90/1.00  sim_fw_demodulated:                     1
% 2.90/1.00  sim_bw_demodulated:                     9
% 2.90/1.00  sim_light_normalised:                   12
% 2.90/1.00  sim_joinable_taut:                      0
% 2.90/1.00  sim_joinable_simp:                      0
% 2.90/1.00  sim_ac_normalised:                      0
% 2.90/1.00  sim_smt_subsumption:                    0
% 2.90/1.00  
%------------------------------------------------------------------------------
