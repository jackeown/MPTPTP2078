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
% DateTime   : Thu Dec  3 12:23:03 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :  142 (1551 expanded)
%              Number of clauses        :   87 ( 259 expanded)
%              Number of leaves         :   14 ( 672 expanded)
%              Depth                    :   19
%              Number of atoms          :  890 (34499 expanded)
%              Number of equality atoms :  200 (2144 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(negated_conjecture,[],[f7])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f30,plain,(
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
          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK6),X5) )
        & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
          | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK6),X5) )
        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK6)
        & X0 = X3
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK5)
              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK5) )
            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK5)
              | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK5) )
            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
            & X0 = X3
            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X6) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
                ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),X5)
                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),X5)
                  | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK4,X6)
                & X0 = X3
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X6) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
                      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X6),X5) )
                    & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X6),X5) )
                    & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK3),u1_struct_0(X1),X4,X6)
                    & sK3 = X0
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
                    & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X1))
                    & v1_funct_1(X6) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
                        ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK2),X5)
                          | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X6),X5) )
                        & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK2),X5)
                          | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X6),X5) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                        & X0 = X3
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X6) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
                            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X4,X2),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X6),X5) )
                            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X4,X2),X5)
                              | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X6),X5) )
                            & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6)
                            & X0 = X3
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1))
                            & v1_funct_1(X6) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
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
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & sK0 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
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

fof(f31,plain,
    ( ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) )
    & ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) )
    & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)
    & sK0 = sK3
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f23,f30,f29,f28,f27,f26,f25,f24])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    sK0 = sK3 ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f36,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f60,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2354,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_3167,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2354])).

cnf(c_10,negated_conjecture,
    ( sK0 = sK3 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2364,negated_conjecture,
    ( sK0 = sK3 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3194,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3167,c_2364])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2352,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3169,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2352])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2357,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_3164,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2357])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2368,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X2_52,X3_52)
    | ~ m1_pre_topc(X2_52,X0_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v2_struct_0(X3_52)
    | v2_struct_0(X1_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X3_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X3_52)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3154,plain,
    ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_51)
    | v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X0_52,X3_52) != iProver_top
    | m1_pre_topc(X2_52,X3_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X3_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X3_52) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2368])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2367,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_pre_topc(X1_52,X2_52)
    | m1_pre_topc(X0_52,X2_52)
    | ~ v2_pre_topc(X2_52)
    | ~ l1_pre_topc(X2_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3155,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X1_52,X2_52) != iProver_top
    | m1_pre_topc(X0_52,X2_52) = iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2367])).

cnf(c_3291,plain,
    ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_51)
    | v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X0_52,X3_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X3_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X3_52) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3154,c_3155])).

cnf(c_4427,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_52,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3164,c_3291])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_33,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_34,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_35,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_40,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_41,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4835,plain,
    ( v2_pre_topc(X1_52) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
    | m1_pre_topc(X0_52,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4427,c_33,c_34,c_35,c_40,c_41])).

cnf(c_4836,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
    | m1_pre_topc(X0_52,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_4835])).

cnf(c_4847,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0_52,sK1,sK0,sK2,sK4)
    | m1_pre_topc(sK0,X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_3169,c_4836])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2369,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X2_52,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | v2_struct_0(X1_52)
    | v2_struct_0(X0_52)
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X0_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_51,X2_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3153,plain,
    ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_51,X2_52)
    | v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2369])).

cnf(c_3850,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_52,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3164,c_3153])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_30,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_31,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_32,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4298,plain,
    ( m1_pre_topc(X0_52,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3850,c_30,c_31,c_32,c_33,c_34,c_35,c_40,c_41])).

cnf(c_4299,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52)
    | m1_pre_topc(X0_52,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4298])).

cnf(c_4306,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_3169,c_4299])).

cnf(c_4865,plain,
    ( k3_tmap_1(X0_52,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | m1_pre_topc(sK0,X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4847,c_4306])).

cnf(c_5512,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | v2_struct_0(sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3194,c_4865])).

cnf(c_5515,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5512,c_30,c_31,c_32])).

cnf(c_3,plain,
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
    inference(cnf_transformation,[],[f34])).

cnf(c_9,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_364,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | u1_struct_0(sK3) != X4
    | u1_struct_0(sK0) != X1
    | u1_struct_0(sK1) != X5
    | u1_struct_0(sK1) != X2
    | sK6 != X3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_9])).

cnf(c_365,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(u1_struct_0(sK1))
    | sK6 = sK4 ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_12,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_367,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | sK6 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_19,c_18,c_17,c_13,c_12,c_11])).

cnf(c_2344,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | sK6 = sK4 ),
    inference(subtyping,[status(esa)],[c_367])).

cnf(c_3177,plain,
    ( sK6 = sK4
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2344])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2370,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_xboole_0(X2_51)
    | v1_xboole_0(X0_51) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3152,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | v1_xboole_0(X2_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2370])).

cnf(c_3807,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3164,c_3152])).

cnf(c_4202,plain,
    ( sK6 = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3177,c_3807])).

cnf(c_2363,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3158,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2363])).

cnf(c_3217,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3158,c_2364])).

cnf(c_3811,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3217,c_3152])).

cnf(c_4201,plain,
    ( sK6 = sK4
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3177,c_3811])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2371,plain,
    ( ~ v1_xboole_0(X0_51)
    | ~ v1_xboole_0(X1_51)
    | X1_51 = X0_51 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3151,plain,
    ( X0_51 = X1_51
    | v1_xboole_0(X0_51) != iProver_top
    | v1_xboole_0(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2371])).

cnf(c_5043,plain,
    ( sK6 = X0_51
    | sK6 = sK4
    | v1_xboole_0(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_4201,c_3151])).

cnf(c_5193,plain,
    ( sK6 = sK4 ),
    inference(superposition,[status(thm)],[c_4202,c_5043])).

cnf(c_8,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2365,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3157,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2365])).

cnf(c_3236,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3157,c_2364])).

cnf(c_5206,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5193,c_3236])).

cnf(c_5518,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5515,c_5206])).

cnf(c_7,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2366,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3156,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2366])).

cnf(c_3241,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3156,c_2364])).

cnf(c_5207,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5193,c_3241])).

cnf(c_5519,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5515,c_5207])).

cnf(c_5523,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5518,c_5519])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.39/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.00  
% 2.39/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.39/1.00  
% 2.39/1.00  ------  iProver source info
% 2.39/1.00  
% 2.39/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.39/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.39/1.00  git: non_committed_changes: false
% 2.39/1.00  git: last_make_outside_of_git: false
% 2.39/1.00  
% 2.39/1.00  ------ 
% 2.39/1.00  
% 2.39/1.00  ------ Input Options
% 2.39/1.00  
% 2.39/1.00  --out_options                           all
% 2.39/1.00  --tptp_safe_out                         true
% 2.39/1.00  --problem_path                          ""
% 2.39/1.00  --include_path                          ""
% 2.39/1.00  --clausifier                            res/vclausify_rel
% 2.39/1.00  --clausifier_options                    --mode clausify
% 2.39/1.00  --stdin                                 false
% 2.39/1.00  --stats_out                             all
% 2.39/1.00  
% 2.39/1.00  ------ General Options
% 2.39/1.00  
% 2.39/1.00  --fof                                   false
% 2.39/1.00  --time_out_real                         305.
% 2.39/1.00  --time_out_virtual                      -1.
% 2.39/1.00  --symbol_type_check                     false
% 2.39/1.00  --clausify_out                          false
% 2.39/1.00  --sig_cnt_out                           false
% 2.39/1.00  --trig_cnt_out                          false
% 2.39/1.00  --trig_cnt_out_tolerance                1.
% 2.39/1.00  --trig_cnt_out_sk_spl                   false
% 2.39/1.00  --abstr_cl_out                          false
% 2.39/1.00  
% 2.39/1.00  ------ Global Options
% 2.39/1.00  
% 2.39/1.00  --schedule                              default
% 2.39/1.00  --add_important_lit                     false
% 2.39/1.00  --prop_solver_per_cl                    1000
% 2.39/1.00  --min_unsat_core                        false
% 2.39/1.00  --soft_assumptions                      false
% 2.39/1.00  --soft_lemma_size                       3
% 2.39/1.00  --prop_impl_unit_size                   0
% 2.39/1.00  --prop_impl_unit                        []
% 2.39/1.00  --share_sel_clauses                     true
% 2.39/1.00  --reset_solvers                         false
% 2.39/1.00  --bc_imp_inh                            [conj_cone]
% 2.39/1.00  --conj_cone_tolerance                   3.
% 2.39/1.00  --extra_neg_conj                        none
% 2.39/1.00  --large_theory_mode                     true
% 2.39/1.00  --prolific_symb_bound                   200
% 2.39/1.00  --lt_threshold                          2000
% 2.39/1.00  --clause_weak_htbl                      true
% 2.39/1.00  --gc_record_bc_elim                     false
% 2.39/1.00  
% 2.39/1.00  ------ Preprocessing Options
% 2.39/1.00  
% 2.39/1.00  --preprocessing_flag                    true
% 2.39/1.00  --time_out_prep_mult                    0.1
% 2.39/1.00  --splitting_mode                        input
% 2.39/1.00  --splitting_grd                         true
% 2.39/1.00  --splitting_cvd                         false
% 2.39/1.00  --splitting_cvd_svl                     false
% 2.39/1.00  --splitting_nvd                         32
% 2.39/1.00  --sub_typing                            true
% 2.39/1.00  --prep_gs_sim                           true
% 2.39/1.00  --prep_unflatten                        true
% 2.39/1.00  --prep_res_sim                          true
% 2.39/1.00  --prep_upred                            true
% 2.39/1.00  --prep_sem_filter                       exhaustive
% 2.39/1.00  --prep_sem_filter_out                   false
% 2.39/1.00  --pred_elim                             true
% 2.39/1.00  --res_sim_input                         true
% 2.39/1.00  --eq_ax_congr_red                       true
% 2.39/1.00  --pure_diseq_elim                       true
% 2.39/1.00  --brand_transform                       false
% 2.39/1.00  --non_eq_to_eq                          false
% 2.39/1.00  --prep_def_merge                        true
% 2.39/1.00  --prep_def_merge_prop_impl              false
% 2.39/1.00  --prep_def_merge_mbd                    true
% 2.39/1.00  --prep_def_merge_tr_red                 false
% 2.39/1.00  --prep_def_merge_tr_cl                  false
% 2.39/1.00  --smt_preprocessing                     true
% 2.39/1.00  --smt_ac_axioms                         fast
% 2.39/1.00  --preprocessed_out                      false
% 2.39/1.00  --preprocessed_stats                    false
% 2.39/1.00  
% 2.39/1.00  ------ Abstraction refinement Options
% 2.39/1.00  
% 2.39/1.00  --abstr_ref                             []
% 2.39/1.00  --abstr_ref_prep                        false
% 2.39/1.00  --abstr_ref_until_sat                   false
% 2.39/1.00  --abstr_ref_sig_restrict                funpre
% 2.39/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.39/1.00  --abstr_ref_under                       []
% 2.39/1.00  
% 2.39/1.00  ------ SAT Options
% 2.39/1.00  
% 2.39/1.00  --sat_mode                              false
% 2.39/1.00  --sat_fm_restart_options                ""
% 2.39/1.00  --sat_gr_def                            false
% 2.39/1.00  --sat_epr_types                         true
% 2.39/1.00  --sat_non_cyclic_types                  false
% 2.39/1.00  --sat_finite_models                     false
% 2.39/1.00  --sat_fm_lemmas                         false
% 2.39/1.00  --sat_fm_prep                           false
% 2.39/1.00  --sat_fm_uc_incr                        true
% 2.39/1.00  --sat_out_model                         small
% 2.39/1.00  --sat_out_clauses                       false
% 2.39/1.00  
% 2.39/1.00  ------ QBF Options
% 2.39/1.00  
% 2.39/1.00  --qbf_mode                              false
% 2.39/1.00  --qbf_elim_univ                         false
% 2.39/1.00  --qbf_dom_inst                          none
% 2.39/1.00  --qbf_dom_pre_inst                      false
% 2.39/1.00  --qbf_sk_in                             false
% 2.39/1.00  --qbf_pred_elim                         true
% 2.39/1.00  --qbf_split                             512
% 2.39/1.00  
% 2.39/1.00  ------ BMC1 Options
% 2.39/1.00  
% 2.39/1.00  --bmc1_incremental                      false
% 2.39/1.00  --bmc1_axioms                           reachable_all
% 2.39/1.00  --bmc1_min_bound                        0
% 2.39/1.00  --bmc1_max_bound                        -1
% 2.39/1.00  --bmc1_max_bound_default                -1
% 2.39/1.00  --bmc1_symbol_reachability              true
% 2.39/1.00  --bmc1_property_lemmas                  false
% 2.39/1.00  --bmc1_k_induction                      false
% 2.39/1.00  --bmc1_non_equiv_states                 false
% 2.39/1.00  --bmc1_deadlock                         false
% 2.39/1.00  --bmc1_ucm                              false
% 2.39/1.00  --bmc1_add_unsat_core                   none
% 2.39/1.00  --bmc1_unsat_core_children              false
% 2.39/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.39/1.00  --bmc1_out_stat                         full
% 2.39/1.00  --bmc1_ground_init                      false
% 2.39/1.00  --bmc1_pre_inst_next_state              false
% 2.39/1.00  --bmc1_pre_inst_state                   false
% 2.39/1.00  --bmc1_pre_inst_reach_state             false
% 2.39/1.00  --bmc1_out_unsat_core                   false
% 2.39/1.00  --bmc1_aig_witness_out                  false
% 2.39/1.00  --bmc1_verbose                          false
% 2.39/1.00  --bmc1_dump_clauses_tptp                false
% 2.39/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.39/1.00  --bmc1_dump_file                        -
% 2.39/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.39/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.39/1.00  --bmc1_ucm_extend_mode                  1
% 2.39/1.00  --bmc1_ucm_init_mode                    2
% 2.39/1.00  --bmc1_ucm_cone_mode                    none
% 2.39/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.39/1.00  --bmc1_ucm_relax_model                  4
% 2.39/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.39/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.39/1.00  --bmc1_ucm_layered_model                none
% 2.39/1.00  --bmc1_ucm_max_lemma_size               10
% 2.39/1.00  
% 2.39/1.00  ------ AIG Options
% 2.39/1.00  
% 2.39/1.00  --aig_mode                              false
% 2.39/1.00  
% 2.39/1.00  ------ Instantiation Options
% 2.39/1.00  
% 2.39/1.00  --instantiation_flag                    true
% 2.39/1.00  --inst_sos_flag                         false
% 2.39/1.00  --inst_sos_phase                        true
% 2.39/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.39/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.39/1.00  --inst_lit_sel_side                     num_symb
% 2.39/1.00  --inst_solver_per_active                1400
% 2.39/1.00  --inst_solver_calls_frac                1.
% 2.39/1.00  --inst_passive_queue_type               priority_queues
% 2.39/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.39/1.00  --inst_passive_queues_freq              [25;2]
% 2.39/1.00  --inst_dismatching                      true
% 2.39/1.00  --inst_eager_unprocessed_to_passive     true
% 2.39/1.00  --inst_prop_sim_given                   true
% 2.39/1.00  --inst_prop_sim_new                     false
% 2.39/1.00  --inst_subs_new                         false
% 2.39/1.00  --inst_eq_res_simp                      false
% 2.39/1.00  --inst_subs_given                       false
% 2.39/1.00  --inst_orphan_elimination               true
% 2.39/1.00  --inst_learning_loop_flag               true
% 2.39/1.00  --inst_learning_start                   3000
% 2.39/1.00  --inst_learning_factor                  2
% 2.39/1.00  --inst_start_prop_sim_after_learn       3
% 2.39/1.00  --inst_sel_renew                        solver
% 2.39/1.00  --inst_lit_activity_flag                true
% 2.39/1.00  --inst_restr_to_given                   false
% 2.39/1.00  --inst_activity_threshold               500
% 2.39/1.00  --inst_out_proof                        true
% 2.39/1.00  
% 2.39/1.00  ------ Resolution Options
% 2.39/1.00  
% 2.39/1.00  --resolution_flag                       true
% 2.39/1.00  --res_lit_sel                           adaptive
% 2.39/1.00  --res_lit_sel_side                      none
% 2.39/1.00  --res_ordering                          kbo
% 2.39/1.00  --res_to_prop_solver                    active
% 2.39/1.00  --res_prop_simpl_new                    false
% 2.39/1.00  --res_prop_simpl_given                  true
% 2.39/1.00  --res_passive_queue_type                priority_queues
% 2.39/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.39/1.00  --res_passive_queues_freq               [15;5]
% 2.39/1.00  --res_forward_subs                      full
% 2.39/1.00  --res_backward_subs                     full
% 2.39/1.00  --res_forward_subs_resolution           true
% 2.39/1.00  --res_backward_subs_resolution          true
% 2.39/1.00  --res_orphan_elimination                true
% 2.39/1.00  --res_time_limit                        2.
% 2.39/1.00  --res_out_proof                         true
% 2.39/1.00  
% 2.39/1.00  ------ Superposition Options
% 2.39/1.00  
% 2.39/1.00  --superposition_flag                    true
% 2.39/1.00  --sup_passive_queue_type                priority_queues
% 2.39/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.39/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.39/1.00  --demod_completeness_check              fast
% 2.39/1.00  --demod_use_ground                      true
% 2.39/1.00  --sup_to_prop_solver                    passive
% 2.39/1.00  --sup_prop_simpl_new                    true
% 2.39/1.00  --sup_prop_simpl_given                  true
% 2.39/1.00  --sup_fun_splitting                     false
% 2.39/1.00  --sup_smt_interval                      50000
% 2.39/1.00  
% 2.39/1.00  ------ Superposition Simplification Setup
% 2.39/1.00  
% 2.39/1.00  --sup_indices_passive                   []
% 2.39/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.39/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.00  --sup_full_bw                           [BwDemod]
% 2.39/1.00  --sup_immed_triv                        [TrivRules]
% 2.39/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.39/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.00  --sup_immed_bw_main                     []
% 2.39/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.39/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.00  
% 2.39/1.00  ------ Combination Options
% 2.39/1.00  
% 2.39/1.00  --comb_res_mult                         3
% 2.39/1.00  --comb_sup_mult                         2
% 2.39/1.00  --comb_inst_mult                        10
% 2.39/1.00  
% 2.39/1.00  ------ Debug Options
% 2.39/1.00  
% 2.39/1.00  --dbg_backtrace                         false
% 2.39/1.00  --dbg_dump_prop_clauses                 false
% 2.39/1.00  --dbg_dump_prop_clauses_file            -
% 2.39/1.00  --dbg_out_stat                          false
% 2.39/1.00  ------ Parsing...
% 2.39/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.39/1.00  
% 2.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.39/1.00  
% 2.39/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.39/1.00  
% 2.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.39/1.00  ------ Proving...
% 2.39/1.00  ------ Problem Properties 
% 2.39/1.00  
% 2.39/1.00  
% 2.39/1.00  clauses                                 28
% 2.39/1.00  conjectures                             22
% 2.39/1.00  EPR                                     16
% 2.39/1.00  Horn                                    24
% 2.39/1.00  unary                                   20
% 2.39/1.00  binary                                  3
% 2.39/1.00  lits                                    61
% 2.39/1.00  lits eq                                 5
% 2.39/1.00  fd_pure                                 0
% 2.39/1.00  fd_pseudo                               0
% 2.39/1.00  fd_cond                                 0
% 2.39/1.00  fd_pseudo_cond                          1
% 2.39/1.00  AC symbols                              0
% 2.39/1.00  
% 2.39/1.00  ------ Schedule dynamic 5 is on 
% 2.39/1.00  
% 2.39/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.39/1.00  
% 2.39/1.00  
% 2.39/1.00  ------ 
% 2.39/1.00  Current options:
% 2.39/1.00  ------ 
% 2.39/1.00  
% 2.39/1.00  ------ Input Options
% 2.39/1.00  
% 2.39/1.00  --out_options                           all
% 2.39/1.00  --tptp_safe_out                         true
% 2.39/1.00  --problem_path                          ""
% 2.39/1.00  --include_path                          ""
% 2.39/1.00  --clausifier                            res/vclausify_rel
% 2.39/1.00  --clausifier_options                    --mode clausify
% 2.39/1.00  --stdin                                 false
% 2.39/1.00  --stats_out                             all
% 2.39/1.00  
% 2.39/1.00  ------ General Options
% 2.39/1.00  
% 2.39/1.00  --fof                                   false
% 2.39/1.00  --time_out_real                         305.
% 2.39/1.00  --time_out_virtual                      -1.
% 2.39/1.00  --symbol_type_check                     false
% 2.39/1.00  --clausify_out                          false
% 2.39/1.00  --sig_cnt_out                           false
% 2.39/1.00  --trig_cnt_out                          false
% 2.39/1.00  --trig_cnt_out_tolerance                1.
% 2.39/1.00  --trig_cnt_out_sk_spl                   false
% 2.39/1.00  --abstr_cl_out                          false
% 2.39/1.00  
% 2.39/1.00  ------ Global Options
% 2.39/1.00  
% 2.39/1.00  --schedule                              default
% 2.39/1.00  --add_important_lit                     false
% 2.39/1.00  --prop_solver_per_cl                    1000
% 2.39/1.00  --min_unsat_core                        false
% 2.39/1.00  --soft_assumptions                      false
% 2.39/1.00  --soft_lemma_size                       3
% 2.39/1.00  --prop_impl_unit_size                   0
% 2.39/1.00  --prop_impl_unit                        []
% 2.39/1.00  --share_sel_clauses                     true
% 2.39/1.00  --reset_solvers                         false
% 2.39/1.00  --bc_imp_inh                            [conj_cone]
% 2.39/1.00  --conj_cone_tolerance                   3.
% 2.39/1.00  --extra_neg_conj                        none
% 2.39/1.00  --large_theory_mode                     true
% 2.39/1.00  --prolific_symb_bound                   200
% 2.39/1.00  --lt_threshold                          2000
% 2.39/1.00  --clause_weak_htbl                      true
% 2.39/1.00  --gc_record_bc_elim                     false
% 2.39/1.00  
% 2.39/1.00  ------ Preprocessing Options
% 2.39/1.00  
% 2.39/1.00  --preprocessing_flag                    true
% 2.39/1.00  --time_out_prep_mult                    0.1
% 2.39/1.00  --splitting_mode                        input
% 2.39/1.00  --splitting_grd                         true
% 2.39/1.00  --splitting_cvd                         false
% 2.39/1.00  --splitting_cvd_svl                     false
% 2.39/1.00  --splitting_nvd                         32
% 2.39/1.00  --sub_typing                            true
% 2.39/1.00  --prep_gs_sim                           true
% 2.39/1.00  --prep_unflatten                        true
% 2.39/1.00  --prep_res_sim                          true
% 2.39/1.00  --prep_upred                            true
% 2.39/1.00  --prep_sem_filter                       exhaustive
% 2.39/1.00  --prep_sem_filter_out                   false
% 2.39/1.00  --pred_elim                             true
% 2.39/1.00  --res_sim_input                         true
% 2.39/1.00  --eq_ax_congr_red                       true
% 2.39/1.00  --pure_diseq_elim                       true
% 2.39/1.00  --brand_transform                       false
% 2.39/1.00  --non_eq_to_eq                          false
% 2.39/1.00  --prep_def_merge                        true
% 2.39/1.00  --prep_def_merge_prop_impl              false
% 2.39/1.00  --prep_def_merge_mbd                    true
% 2.39/1.00  --prep_def_merge_tr_red                 false
% 2.39/1.00  --prep_def_merge_tr_cl                  false
% 2.39/1.00  --smt_preprocessing                     true
% 2.39/1.00  --smt_ac_axioms                         fast
% 2.39/1.00  --preprocessed_out                      false
% 2.39/1.00  --preprocessed_stats                    false
% 2.39/1.00  
% 2.39/1.00  ------ Abstraction refinement Options
% 2.39/1.00  
% 2.39/1.00  --abstr_ref                             []
% 2.39/1.00  --abstr_ref_prep                        false
% 2.39/1.00  --abstr_ref_until_sat                   false
% 2.39/1.00  --abstr_ref_sig_restrict                funpre
% 2.39/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.39/1.00  --abstr_ref_under                       []
% 2.39/1.00  
% 2.39/1.00  ------ SAT Options
% 2.39/1.00  
% 2.39/1.00  --sat_mode                              false
% 2.39/1.00  --sat_fm_restart_options                ""
% 2.39/1.00  --sat_gr_def                            false
% 2.39/1.00  --sat_epr_types                         true
% 2.39/1.00  --sat_non_cyclic_types                  false
% 2.39/1.00  --sat_finite_models                     false
% 2.39/1.00  --sat_fm_lemmas                         false
% 2.39/1.00  --sat_fm_prep                           false
% 2.39/1.00  --sat_fm_uc_incr                        true
% 2.39/1.00  --sat_out_model                         small
% 2.39/1.00  --sat_out_clauses                       false
% 2.39/1.00  
% 2.39/1.00  ------ QBF Options
% 2.39/1.00  
% 2.39/1.00  --qbf_mode                              false
% 2.39/1.00  --qbf_elim_univ                         false
% 2.39/1.00  --qbf_dom_inst                          none
% 2.39/1.00  --qbf_dom_pre_inst                      false
% 2.39/1.00  --qbf_sk_in                             false
% 2.39/1.00  --qbf_pred_elim                         true
% 2.39/1.00  --qbf_split                             512
% 2.39/1.00  
% 2.39/1.00  ------ BMC1 Options
% 2.39/1.00  
% 2.39/1.00  --bmc1_incremental                      false
% 2.39/1.00  --bmc1_axioms                           reachable_all
% 2.39/1.00  --bmc1_min_bound                        0
% 2.39/1.00  --bmc1_max_bound                        -1
% 2.39/1.00  --bmc1_max_bound_default                -1
% 2.39/1.00  --bmc1_symbol_reachability              true
% 2.39/1.00  --bmc1_property_lemmas                  false
% 2.39/1.00  --bmc1_k_induction                      false
% 2.39/1.00  --bmc1_non_equiv_states                 false
% 2.39/1.00  --bmc1_deadlock                         false
% 2.39/1.00  --bmc1_ucm                              false
% 2.39/1.00  --bmc1_add_unsat_core                   none
% 2.39/1.00  --bmc1_unsat_core_children              false
% 2.39/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.39/1.00  --bmc1_out_stat                         full
% 2.39/1.00  --bmc1_ground_init                      false
% 2.39/1.00  --bmc1_pre_inst_next_state              false
% 2.39/1.00  --bmc1_pre_inst_state                   false
% 2.39/1.00  --bmc1_pre_inst_reach_state             false
% 2.39/1.00  --bmc1_out_unsat_core                   false
% 2.39/1.00  --bmc1_aig_witness_out                  false
% 2.39/1.00  --bmc1_verbose                          false
% 2.39/1.00  --bmc1_dump_clauses_tptp                false
% 2.39/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.39/1.00  --bmc1_dump_file                        -
% 2.39/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.39/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.39/1.00  --bmc1_ucm_extend_mode                  1
% 2.39/1.00  --bmc1_ucm_init_mode                    2
% 2.39/1.00  --bmc1_ucm_cone_mode                    none
% 2.39/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.39/1.00  --bmc1_ucm_relax_model                  4
% 2.39/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.39/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.39/1.00  --bmc1_ucm_layered_model                none
% 2.39/1.00  --bmc1_ucm_max_lemma_size               10
% 2.39/1.00  
% 2.39/1.00  ------ AIG Options
% 2.39/1.00  
% 2.39/1.00  --aig_mode                              false
% 2.39/1.00  
% 2.39/1.00  ------ Instantiation Options
% 2.39/1.00  
% 2.39/1.00  --instantiation_flag                    true
% 2.39/1.00  --inst_sos_flag                         false
% 2.39/1.00  --inst_sos_phase                        true
% 2.39/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.39/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.39/1.00  --inst_lit_sel_side                     none
% 2.39/1.00  --inst_solver_per_active                1400
% 2.39/1.00  --inst_solver_calls_frac                1.
% 2.39/1.00  --inst_passive_queue_type               priority_queues
% 2.39/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.39/1.00  --inst_passive_queues_freq              [25;2]
% 2.39/1.00  --inst_dismatching                      true
% 2.39/1.00  --inst_eager_unprocessed_to_passive     true
% 2.39/1.00  --inst_prop_sim_given                   true
% 2.39/1.00  --inst_prop_sim_new                     false
% 2.39/1.00  --inst_subs_new                         false
% 2.39/1.00  --inst_eq_res_simp                      false
% 2.39/1.00  --inst_subs_given                       false
% 2.39/1.00  --inst_orphan_elimination               true
% 2.39/1.00  --inst_learning_loop_flag               true
% 2.39/1.00  --inst_learning_start                   3000
% 2.39/1.00  --inst_learning_factor                  2
% 2.39/1.00  --inst_start_prop_sim_after_learn       3
% 2.39/1.00  --inst_sel_renew                        solver
% 2.39/1.00  --inst_lit_activity_flag                true
% 2.39/1.00  --inst_restr_to_given                   false
% 2.39/1.00  --inst_activity_threshold               500
% 2.39/1.00  --inst_out_proof                        true
% 2.39/1.00  
% 2.39/1.00  ------ Resolution Options
% 2.39/1.00  
% 2.39/1.00  --resolution_flag                       false
% 2.39/1.00  --res_lit_sel                           adaptive
% 2.39/1.00  --res_lit_sel_side                      none
% 2.39/1.00  --res_ordering                          kbo
% 2.39/1.00  --res_to_prop_solver                    active
% 2.39/1.00  --res_prop_simpl_new                    false
% 2.39/1.00  --res_prop_simpl_given                  true
% 2.39/1.00  --res_passive_queue_type                priority_queues
% 2.39/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.39/1.00  --res_passive_queues_freq               [15;5]
% 2.39/1.00  --res_forward_subs                      full
% 2.39/1.00  --res_backward_subs                     full
% 2.39/1.00  --res_forward_subs_resolution           true
% 2.39/1.00  --res_backward_subs_resolution          true
% 2.39/1.00  --res_orphan_elimination                true
% 2.39/1.00  --res_time_limit                        2.
% 2.39/1.00  --res_out_proof                         true
% 2.39/1.00  
% 2.39/1.00  ------ Superposition Options
% 2.39/1.00  
% 2.39/1.00  --superposition_flag                    true
% 2.39/1.00  --sup_passive_queue_type                priority_queues
% 2.39/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.39/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.39/1.00  --demod_completeness_check              fast
% 2.39/1.00  --demod_use_ground                      true
% 2.39/1.00  --sup_to_prop_solver                    passive
% 2.39/1.00  --sup_prop_simpl_new                    true
% 2.39/1.00  --sup_prop_simpl_given                  true
% 2.39/1.00  --sup_fun_splitting                     false
% 2.39/1.00  --sup_smt_interval                      50000
% 2.39/1.00  
% 2.39/1.00  ------ Superposition Simplification Setup
% 2.39/1.00  
% 2.39/1.00  --sup_indices_passive                   []
% 2.39/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.39/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.39/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.00  --sup_full_bw                           [BwDemod]
% 2.39/1.00  --sup_immed_triv                        [TrivRules]
% 2.39/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.39/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.00  --sup_immed_bw_main                     []
% 2.39/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.39/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.39/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.39/1.00  
% 2.39/1.00  ------ Combination Options
% 2.39/1.00  
% 2.39/1.00  --comb_res_mult                         3
% 2.39/1.00  --comb_sup_mult                         2
% 2.39/1.00  --comb_inst_mult                        10
% 2.39/1.00  
% 2.39/1.00  ------ Debug Options
% 2.39/1.00  
% 2.39/1.00  --dbg_backtrace                         false
% 2.39/1.00  --dbg_dump_prop_clauses                 false
% 2.39/1.00  --dbg_dump_prop_clauses_file            -
% 2.39/1.00  --dbg_out_stat                          false
% 2.39/1.00  
% 2.39/1.00  
% 2.39/1.00  
% 2.39/1.00  
% 2.39/1.00  ------ Proving...
% 2.39/1.00  
% 2.39/1.00  
% 2.39/1.00  % SZS status Theorem for theBenchmark.p
% 2.39/1.00  
% 2.39/1.00   Resolution empty clause
% 2.39/1.00  
% 2.39/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.39/1.00  
% 2.39/1.00  fof(f7,conjecture,(
% 2.39/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f8,negated_conjecture,(
% 2.39/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 2.39/1.00    inference(negated_conjecture,[],[f7])).
% 2.39/1.00  
% 2.39/1.00  fof(f19,plain,(
% 2.39/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.39/1.00    inference(ennf_transformation,[],[f8])).
% 2.39/1.00  
% 2.39/1.00  fof(f20,plain,(
% 2.39/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.39/1.00    inference(flattening,[],[f19])).
% 2.39/1.00  
% 2.39/1.00  fof(f22,plain,(
% 2.39/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.39/1.00    inference(nnf_transformation,[],[f20])).
% 2.39/1.00  
% 2.39/1.00  fof(f23,plain,(
% 2.39/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.39/1.00    inference(flattening,[],[f22])).
% 2.39/1.00  
% 2.39/1.00  fof(f30,plain,(
% 2.39/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK6) & X0 = X3 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 2.39/1.00    introduced(choice_axiom,[])).
% 2.39/1.00  
% 2.39/1.00  fof(f29,plain,(
% 2.39/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.39/1.00    introduced(choice_axiom,[])).
% 2.39/1.00  
% 2.39/1.00  fof(f28,plain,(
% 2.39/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 2.39/1.00    introduced(choice_axiom,[])).
% 2.39/1.00  
% 2.39/1.00  fof(f27,plain,(
% 2.39/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK3),u1_struct_0(X1),X4,X6) & sK3 = X0 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.39/1.00    introduced(choice_axiom,[])).
% 2.39/1.00  
% 2.39/1.00  fof(f26,plain,(
% 2.39/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK2),X5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X6),X5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK2),X5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.39/1.00    introduced(choice_axiom,[])).
% 2.39/1.00  
% 2.39/1.00  fof(f25,plain,(
% 2.39/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(X3),u1_struct_0(sK1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 2.39/1.00    introduced(choice_axiom,[])).
% 2.39/1.00  
% 2.39/1.00  fof(f24,plain,(
% 2.39/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.39/1.00    introduced(choice_axiom,[])).
% 2.39/1.00  
% 2.39/1.00  fof(f31,plain,(
% 2.39/1.00    (((((((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & (r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)) & r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) & sK0 = sK3 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.39/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f23,f30,f29,f28,f27,f26,f25,f24])).
% 2.39/1.00  
% 2.39/1.00  fof(f48,plain,(
% 2.39/1.00    m1_pre_topc(sK3,sK0)),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f58,plain,(
% 2.39/1.00    sK0 = sK3),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f46,plain,(
% 2.39/1.00    m1_pre_topc(sK2,sK0)),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f51,plain,(
% 2.39/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f5,axiom,(
% 2.39/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f15,plain,(
% 2.39/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.39/1.00    inference(ennf_transformation,[],[f5])).
% 2.39/1.00  
% 2.39/1.00  fof(f16,plain,(
% 2.39/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.39/1.00    inference(flattening,[],[f15])).
% 2.39/1.00  
% 2.39/1.00  fof(f37,plain,(
% 2.39/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f16])).
% 2.39/1.00  
% 2.39/1.00  fof(f6,axiom,(
% 2.39/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f17,plain,(
% 2.39/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.39/1.00    inference(ennf_transformation,[],[f6])).
% 2.39/1.00  
% 2.39/1.00  fof(f18,plain,(
% 2.39/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.39/1.00    inference(flattening,[],[f17])).
% 2.39/1.00  
% 2.39/1.00  fof(f38,plain,(
% 2.39/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f18])).
% 2.39/1.00  
% 2.39/1.00  fof(f42,plain,(
% 2.39/1.00    ~v2_struct_0(sK1)),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f43,plain,(
% 2.39/1.00    v2_pre_topc(sK1)),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f44,plain,(
% 2.39/1.00    l1_pre_topc(sK1)),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f49,plain,(
% 2.39/1.00    v1_funct_1(sK4)),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f50,plain,(
% 2.39/1.00    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f4,axiom,(
% 2.39/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f13,plain,(
% 2.39/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.39/1.00    inference(ennf_transformation,[],[f4])).
% 2.39/1.00  
% 2.39/1.00  fof(f14,plain,(
% 2.39/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.39/1.00    inference(flattening,[],[f13])).
% 2.39/1.00  
% 2.39/1.00  fof(f36,plain,(
% 2.39/1.00    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f14])).
% 2.39/1.00  
% 2.39/1.00  fof(f39,plain,(
% 2.39/1.00    ~v2_struct_0(sK0)),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f40,plain,(
% 2.39/1.00    v2_pre_topc(sK0)),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f41,plain,(
% 2.39/1.00    l1_pre_topc(sK0)),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f3,axiom,(
% 2.39/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.00  
% 2.39/1.00  fof(f11,plain,(
% 2.39/1.00    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.39/1.00    inference(ennf_transformation,[],[f3])).
% 2.39/1.00  
% 2.39/1.00  fof(f12,plain,(
% 2.39/1.00    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.39/1.00    inference(flattening,[],[f11])).
% 2.39/1.00  
% 2.39/1.00  fof(f21,plain,(
% 2.39/1.00    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.39/1.00    inference(nnf_transformation,[],[f12])).
% 2.39/1.00  
% 2.39/1.00  fof(f34,plain,(
% 2.39/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.39/1.00    inference(cnf_transformation,[],[f21])).
% 2.39/1.00  
% 2.39/1.00  fof(f59,plain,(
% 2.39/1.00    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6)),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f55,plain,(
% 2.39/1.00    v1_funct_1(sK6)),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f56,plain,(
% 2.39/1.00    v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f57,plain,(
% 2.39/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.39/1.00    inference(cnf_transformation,[],[f31])).
% 2.39/1.00  
% 2.39/1.00  fof(f2,axiom,(
% 2.39/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.39/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.01  
% 2.39/1.01  fof(f10,plain,(
% 2.39/1.01    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.39/1.01    inference(ennf_transformation,[],[f2])).
% 2.39/1.01  
% 2.39/1.01  fof(f33,plain,(
% 2.39/1.01    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.39/1.01    inference(cnf_transformation,[],[f10])).
% 2.39/1.01  
% 2.39/1.01  fof(f1,axiom,(
% 2.39/1.01    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.39/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.39/1.01  
% 2.39/1.01  fof(f9,plain,(
% 2.39/1.01    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.39/1.01    inference(ennf_transformation,[],[f1])).
% 2.39/1.01  
% 2.39/1.01  fof(f32,plain,(
% 2.39/1.01    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.39/1.01    inference(cnf_transformation,[],[f9])).
% 2.39/1.01  
% 2.39/1.01  fof(f60,plain,(
% 2.39/1.01    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 2.39/1.01    inference(cnf_transformation,[],[f31])).
% 2.39/1.01  
% 2.39/1.01  fof(f61,plain,(
% 2.39/1.01    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)),
% 2.39/1.01    inference(cnf_transformation,[],[f31])).
% 2.39/1.01  
% 2.39/1.01  cnf(c_20,negated_conjecture,
% 2.39/1.01      ( m1_pre_topc(sK3,sK0) ),
% 2.39/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_2354,negated_conjecture,
% 2.39/1.01      ( m1_pre_topc(sK3,sK0) ),
% 2.39/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3167,plain,
% 2.39/1.01      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_2354]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_10,negated_conjecture,
% 2.39/1.01      ( sK0 = sK3 ),
% 2.39/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_2364,negated_conjecture,
% 2.39/1.01      ( sK0 = sK3 ),
% 2.39/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3194,plain,
% 2.39/1.01      ( m1_pre_topc(sK0,sK0) = iProver_top ),
% 2.39/1.01      inference(light_normalisation,[status(thm)],[c_3167,c_2364]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_22,negated_conjecture,
% 2.39/1.01      ( m1_pre_topc(sK2,sK0) ),
% 2.39/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_2352,negated_conjecture,
% 2.39/1.01      ( m1_pre_topc(sK2,sK0) ),
% 2.39/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3169,plain,
% 2.39/1.01      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_2352]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_17,negated_conjecture,
% 2.39/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.39/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_2357,negated_conjecture,
% 2.39/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.39/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3164,plain,
% 2.39/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_2357]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_5,plain,
% 2.39/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.39/1.01      | ~ m1_pre_topc(X3,X4)
% 2.39/1.01      | ~ m1_pre_topc(X3,X1)
% 2.39/1.01      | ~ m1_pre_topc(X1,X4)
% 2.39/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.39/1.01      | v2_struct_0(X4)
% 2.39/1.01      | v2_struct_0(X2)
% 2.39/1.01      | ~ v2_pre_topc(X2)
% 2.39/1.01      | ~ v2_pre_topc(X4)
% 2.39/1.01      | ~ l1_pre_topc(X2)
% 2.39/1.01      | ~ l1_pre_topc(X4)
% 2.39/1.01      | ~ v1_funct_1(X0)
% 2.39/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.39/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_2368,plain,
% 2.39/1.01      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 2.39/1.01      | ~ m1_pre_topc(X2_52,X3_52)
% 2.39/1.01      | ~ m1_pre_topc(X2_52,X0_52)
% 2.39/1.01      | ~ m1_pre_topc(X0_52,X3_52)
% 2.39/1.01      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 2.39/1.01      | v2_struct_0(X3_52)
% 2.39/1.01      | v2_struct_0(X1_52)
% 2.39/1.01      | ~ v2_pre_topc(X1_52)
% 2.39/1.01      | ~ v2_pre_topc(X3_52)
% 2.39/1.01      | ~ l1_pre_topc(X1_52)
% 2.39/1.01      | ~ l1_pre_topc(X3_52)
% 2.39/1.01      | ~ v1_funct_1(X0_51)
% 2.39/1.01      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_51) ),
% 2.39/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3154,plain,
% 2.39/1.01      ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_51)
% 2.39/1.01      | v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 2.39/1.01      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.39/1.01      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 2.39/1.01      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 2.39/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 2.39/1.01      | v2_struct_0(X1_52) = iProver_top
% 2.39/1.01      | v2_struct_0(X3_52) = iProver_top
% 2.39/1.01      | v2_pre_topc(X1_52) != iProver_top
% 2.39/1.01      | v2_pre_topc(X3_52) != iProver_top
% 2.39/1.01      | l1_pre_topc(X1_52) != iProver_top
% 2.39/1.01      | l1_pre_topc(X3_52) != iProver_top
% 2.39/1.01      | v1_funct_1(X0_51) != iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_2368]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_6,plain,
% 2.39/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.39/1.01      | ~ m1_pre_topc(X1,X2)
% 2.39/1.01      | m1_pre_topc(X0,X2)
% 2.39/1.01      | ~ v2_pre_topc(X2)
% 2.39/1.01      | ~ l1_pre_topc(X2) ),
% 2.39/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_2367,plain,
% 2.39/1.01      ( ~ m1_pre_topc(X0_52,X1_52)
% 2.39/1.01      | ~ m1_pre_topc(X1_52,X2_52)
% 2.39/1.01      | m1_pre_topc(X0_52,X2_52)
% 2.39/1.01      | ~ v2_pre_topc(X2_52)
% 2.39/1.01      | ~ l1_pre_topc(X2_52) ),
% 2.39/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3155,plain,
% 2.39/1.01      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 2.39/1.01      | m1_pre_topc(X1_52,X2_52) != iProver_top
% 2.39/1.01      | m1_pre_topc(X0_52,X2_52) = iProver_top
% 2.39/1.01      | v2_pre_topc(X2_52) != iProver_top
% 2.39/1.01      | l1_pre_topc(X2_52) != iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_2367]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3291,plain,
% 2.39/1.01      ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_51)
% 2.39/1.01      | v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 2.39/1.01      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.39/1.01      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 2.39/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 2.39/1.01      | v2_struct_0(X1_52) = iProver_top
% 2.39/1.01      | v2_struct_0(X3_52) = iProver_top
% 2.39/1.01      | v2_pre_topc(X1_52) != iProver_top
% 2.39/1.01      | v2_pre_topc(X3_52) != iProver_top
% 2.39/1.01      | l1_pre_topc(X1_52) != iProver_top
% 2.39/1.01      | l1_pre_topc(X3_52) != iProver_top
% 2.39/1.01      | v1_funct_1(X0_51) != iProver_top ),
% 2.39/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_3154,c_3155]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_4427,plain,
% 2.39/1.01      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
% 2.39/1.01      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.39/1.01      | m1_pre_topc(X0_52,sK0) != iProver_top
% 2.39/1.01      | m1_pre_topc(sK0,X1_52) != iProver_top
% 2.39/1.01      | v2_struct_0(X1_52) = iProver_top
% 2.39/1.01      | v2_struct_0(sK1) = iProver_top
% 2.39/1.01      | v2_pre_topc(X1_52) != iProver_top
% 2.39/1.01      | v2_pre_topc(sK1) != iProver_top
% 2.39/1.01      | l1_pre_topc(X1_52) != iProver_top
% 2.39/1.01      | l1_pre_topc(sK1) != iProver_top
% 2.39/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.39/1.01      inference(superposition,[status(thm)],[c_3164,c_3291]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_26,negated_conjecture,
% 2.39/1.01      ( ~ v2_struct_0(sK1) ),
% 2.39/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_33,plain,
% 2.39/1.01      ( v2_struct_0(sK1) != iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_25,negated_conjecture,
% 2.39/1.01      ( v2_pre_topc(sK1) ),
% 2.39/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_34,plain,
% 2.39/1.01      ( v2_pre_topc(sK1) = iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_24,negated_conjecture,
% 2.39/1.01      ( l1_pre_topc(sK1) ),
% 2.39/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_35,plain,
% 2.39/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_19,negated_conjecture,
% 2.39/1.01      ( v1_funct_1(sK4) ),
% 2.39/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_40,plain,
% 2.39/1.01      ( v1_funct_1(sK4) = iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_18,negated_conjecture,
% 2.39/1.01      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.39/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_41,plain,
% 2.39/1.01      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_4835,plain,
% 2.39/1.01      ( v2_pre_topc(X1_52) != iProver_top
% 2.39/1.01      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
% 2.39/1.01      | m1_pre_topc(X0_52,sK0) != iProver_top
% 2.39/1.01      | m1_pre_topc(sK0,X1_52) != iProver_top
% 2.39/1.01      | v2_struct_0(X1_52) = iProver_top
% 2.39/1.01      | l1_pre_topc(X1_52) != iProver_top ),
% 2.39/1.01      inference(global_propositional_subsumption,
% 2.39/1.01                [status(thm)],
% 2.39/1.01                [c_4427,c_33,c_34,c_35,c_40,c_41]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_4836,plain,
% 2.39/1.01      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
% 2.39/1.01      | m1_pre_topc(X0_52,sK0) != iProver_top
% 2.39/1.01      | m1_pre_topc(sK0,X1_52) != iProver_top
% 2.39/1.01      | v2_struct_0(X1_52) = iProver_top
% 2.39/1.01      | v2_pre_topc(X1_52) != iProver_top
% 2.39/1.01      | l1_pre_topc(X1_52) != iProver_top ),
% 2.39/1.01      inference(renaming,[status(thm)],[c_4835]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_4847,plain,
% 2.39/1.01      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(X0_52,sK1,sK0,sK2,sK4)
% 2.39/1.01      | m1_pre_topc(sK0,X0_52) != iProver_top
% 2.39/1.01      | v2_struct_0(X0_52) = iProver_top
% 2.39/1.01      | v2_pre_topc(X0_52) != iProver_top
% 2.39/1.01      | l1_pre_topc(X0_52) != iProver_top ),
% 2.39/1.01      inference(superposition,[status(thm)],[c_3169,c_4836]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_4,plain,
% 2.39/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.39/1.01      | ~ m1_pre_topc(X3,X1)
% 2.39/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.39/1.01      | v2_struct_0(X1)
% 2.39/1.01      | v2_struct_0(X2)
% 2.39/1.01      | ~ v2_pre_topc(X2)
% 2.39/1.01      | ~ v2_pre_topc(X1)
% 2.39/1.01      | ~ l1_pre_topc(X2)
% 2.39/1.01      | ~ l1_pre_topc(X1)
% 2.39/1.01      | ~ v1_funct_1(X0)
% 2.39/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.39/1.01      inference(cnf_transformation,[],[f36]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_2369,plain,
% 2.39/1.01      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 2.39/1.01      | ~ m1_pre_topc(X2_52,X0_52)
% 2.39/1.01      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 2.39/1.01      | v2_struct_0(X1_52)
% 2.39/1.01      | v2_struct_0(X0_52)
% 2.39/1.01      | ~ v2_pre_topc(X1_52)
% 2.39/1.01      | ~ v2_pre_topc(X0_52)
% 2.39/1.01      | ~ l1_pre_topc(X1_52)
% 2.39/1.01      | ~ l1_pre_topc(X0_52)
% 2.39/1.01      | ~ v1_funct_1(X0_51)
% 2.39/1.01      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_51,X2_52) ),
% 2.39/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3153,plain,
% 2.39/1.01      ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_51,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_51,X2_52)
% 2.39/1.01      | v1_funct_2(X0_51,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 2.39/1.01      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 2.39/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 2.39/1.01      | v2_struct_0(X1_52) = iProver_top
% 2.39/1.01      | v2_struct_0(X0_52) = iProver_top
% 2.39/1.01      | v2_pre_topc(X1_52) != iProver_top
% 2.39/1.01      | v2_pre_topc(X0_52) != iProver_top
% 2.39/1.01      | l1_pre_topc(X1_52) != iProver_top
% 2.39/1.01      | l1_pre_topc(X0_52) != iProver_top
% 2.39/1.01      | v1_funct_1(X0_51) != iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_2369]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3850,plain,
% 2.39/1.01      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52)
% 2.39/1.01      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.39/1.01      | m1_pre_topc(X0_52,sK0) != iProver_top
% 2.39/1.01      | v2_struct_0(sK0) = iProver_top
% 2.39/1.01      | v2_struct_0(sK1) = iProver_top
% 2.39/1.01      | v2_pre_topc(sK0) != iProver_top
% 2.39/1.01      | v2_pre_topc(sK1) != iProver_top
% 2.39/1.01      | l1_pre_topc(sK0) != iProver_top
% 2.39/1.01      | l1_pre_topc(sK1) != iProver_top
% 2.39/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.39/1.01      inference(superposition,[status(thm)],[c_3164,c_3153]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_29,negated_conjecture,
% 2.39/1.01      ( ~ v2_struct_0(sK0) ),
% 2.39/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_30,plain,
% 2.39/1.01      ( v2_struct_0(sK0) != iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_28,negated_conjecture,
% 2.39/1.01      ( v2_pre_topc(sK0) ),
% 2.39/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_31,plain,
% 2.39/1.01      ( v2_pre_topc(sK0) = iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_27,negated_conjecture,
% 2.39/1.01      ( l1_pre_topc(sK0) ),
% 2.39/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_32,plain,
% 2.39/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_4298,plain,
% 2.39/1.01      ( m1_pre_topc(X0_52,sK0) != iProver_top
% 2.39/1.01      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52) ),
% 2.39/1.01      inference(global_propositional_subsumption,
% 2.39/1.01                [status(thm)],
% 2.39/1.01                [c_3850,c_30,c_31,c_32,c_33,c_34,c_35,c_40,c_41]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_4299,plain,
% 2.39/1.01      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52)
% 2.39/1.01      | m1_pre_topc(X0_52,sK0) != iProver_top ),
% 2.39/1.01      inference(renaming,[status(thm)],[c_4298]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_4306,plain,
% 2.39/1.01      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 2.39/1.01      inference(superposition,[status(thm)],[c_3169,c_4299]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_4865,plain,
% 2.39/1.01      ( k3_tmap_1(X0_52,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 2.39/1.01      | m1_pre_topc(sK0,X0_52) != iProver_top
% 2.39/1.01      | v2_struct_0(X0_52) = iProver_top
% 2.39/1.01      | v2_pre_topc(X0_52) != iProver_top
% 2.39/1.01      | l1_pre_topc(X0_52) != iProver_top ),
% 2.39/1.01      inference(light_normalisation,[status(thm)],[c_4847,c_4306]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_5512,plain,
% 2.39/1.01      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 2.39/1.01      | v2_struct_0(sK0) = iProver_top
% 2.39/1.01      | v2_pre_topc(sK0) != iProver_top
% 2.39/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 2.39/1.01      inference(superposition,[status(thm)],[c_3194,c_4865]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_5515,plain,
% 2.39/1.01      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 2.39/1.01      inference(global_propositional_subsumption,
% 2.39/1.01                [status(thm)],
% 2.39/1.01                [c_5512,c_30,c_31,c_32]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3,plain,
% 2.39/1.01      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 2.39/1.01      | ~ v1_funct_2(X5,X2,X3)
% 2.39/1.01      | ~ v1_funct_2(X4,X0,X1)
% 2.39/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.39/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.39/1.01      | ~ v1_funct_1(X5)
% 2.39/1.01      | ~ v1_funct_1(X4)
% 2.39/1.01      | v1_xboole_0(X1)
% 2.39/1.01      | v1_xboole_0(X3)
% 2.39/1.01      | X4 = X5 ),
% 2.39/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_9,negated_conjecture,
% 2.39/1.01      ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK3),u1_struct_0(sK1),sK4,sK6) ),
% 2.39/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_364,plain,
% 2.39/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.39/1.01      | ~ v1_funct_2(X3,X4,X5)
% 2.39/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.39/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.39/1.01      | ~ v1_funct_1(X0)
% 2.39/1.01      | ~ v1_funct_1(X3)
% 2.39/1.01      | v1_xboole_0(X2)
% 2.39/1.01      | v1_xboole_0(X5)
% 2.39/1.01      | X3 = X0
% 2.39/1.01      | u1_struct_0(sK3) != X4
% 2.39/1.01      | u1_struct_0(sK0) != X1
% 2.39/1.01      | u1_struct_0(sK1) != X5
% 2.39/1.01      | u1_struct_0(sK1) != X2
% 2.39/1.01      | sK6 != X3
% 2.39/1.01      | sK4 != X0 ),
% 2.39/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_9]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_365,plain,
% 2.39/1.01      ( ~ v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1))
% 2.39/1.01      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.39/1.01      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.39/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.39/1.01      | ~ v1_funct_1(sK6)
% 2.39/1.01      | ~ v1_funct_1(sK4)
% 2.39/1.01      | v1_xboole_0(u1_struct_0(sK1))
% 2.39/1.01      | sK6 = sK4 ),
% 2.39/1.01      inference(unflattening,[status(thm)],[c_364]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_13,negated_conjecture,
% 2.39/1.01      ( v1_funct_1(sK6) ),
% 2.39/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_12,negated_conjecture,
% 2.39/1.01      ( v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 2.39/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_11,negated_conjecture,
% 2.39/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.39/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_367,plain,
% 2.39/1.01      ( v1_xboole_0(u1_struct_0(sK1)) | sK6 = sK4 ),
% 2.39/1.01      inference(global_propositional_subsumption,
% 2.39/1.01                [status(thm)],
% 2.39/1.01                [c_365,c_19,c_18,c_17,c_13,c_12,c_11]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_2344,plain,
% 2.39/1.01      ( v1_xboole_0(u1_struct_0(sK1)) | sK6 = sK4 ),
% 2.39/1.01      inference(subtyping,[status(esa)],[c_367]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3177,plain,
% 2.39/1.01      ( sK6 = sK4 | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_2344]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_1,plain,
% 2.39/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.39/1.01      | ~ v1_xboole_0(X2)
% 2.39/1.01      | v1_xboole_0(X0) ),
% 2.39/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_2370,plain,
% 2.39/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 2.39/1.01      | ~ v1_xboole_0(X2_51)
% 2.39/1.01      | v1_xboole_0(X0_51) ),
% 2.39/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3152,plain,
% 2.39/1.01      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 2.39/1.01      | v1_xboole_0(X2_51) != iProver_top
% 2.39/1.01      | v1_xboole_0(X0_51) = iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_2370]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3807,plain,
% 2.39/1.01      ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top
% 2.39/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 2.39/1.01      inference(superposition,[status(thm)],[c_3164,c_3152]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_4202,plain,
% 2.39/1.01      ( sK6 = sK4 | v1_xboole_0(sK4) = iProver_top ),
% 2.39/1.01      inference(superposition,[status(thm)],[c_3177,c_3807]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_2363,negated_conjecture,
% 2.39/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.39/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3158,plain,
% 2.39/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_2363]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3217,plain,
% 2.39/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.39/1.01      inference(light_normalisation,[status(thm)],[c_3158,c_2364]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3811,plain,
% 2.39/1.01      ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top
% 2.39/1.01      | v1_xboole_0(sK6) = iProver_top ),
% 2.39/1.01      inference(superposition,[status(thm)],[c_3217,c_3152]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_4201,plain,
% 2.39/1.01      ( sK6 = sK4 | v1_xboole_0(sK6) = iProver_top ),
% 2.39/1.01      inference(superposition,[status(thm)],[c_3177,c_3811]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_0,plain,
% 2.39/1.01      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.39/1.01      inference(cnf_transformation,[],[f32]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_2371,plain,
% 2.39/1.01      ( ~ v1_xboole_0(X0_51) | ~ v1_xboole_0(X1_51) | X1_51 = X0_51 ),
% 2.39/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3151,plain,
% 2.39/1.01      ( X0_51 = X1_51
% 2.39/1.01      | v1_xboole_0(X0_51) != iProver_top
% 2.39/1.01      | v1_xboole_0(X1_51) != iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_2371]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_5043,plain,
% 2.39/1.01      ( sK6 = X0_51 | sK6 = sK4 | v1_xboole_0(X0_51) != iProver_top ),
% 2.39/1.01      inference(superposition,[status(thm)],[c_4201,c_3151]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_5193,plain,
% 2.39/1.01      ( sK6 = sK4 ),
% 2.39/1.01      inference(superposition,[status(thm)],[c_4202,c_5043]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_8,negated_conjecture,
% 2.39/1.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 2.39/1.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 2.39/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_2365,negated_conjecture,
% 2.39/1.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 2.39/1.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 2.39/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3157,plain,
% 2.39/1.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) = iProver_top
% 2.39/1.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_2365]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3236,plain,
% 2.39/1.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) = iProver_top
% 2.39/1.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
% 2.39/1.01      inference(light_normalisation,[status(thm)],[c_3157,c_2364]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_5206,plain,
% 2.39/1.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) = iProver_top
% 2.39/1.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
% 2.39/1.01      inference(demodulation,[status(thm)],[c_5193,c_3236]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_5518,plain,
% 2.39/1.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) = iProver_top ),
% 2.39/1.01      inference(demodulation,[status(thm)],[c_5515,c_5206]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_7,negated_conjecture,
% 2.39/1.01      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 2.39/1.01      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 2.39/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_2366,negated_conjecture,
% 2.39/1.01      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5)
% 2.39/1.01      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) ),
% 2.39/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3156,plain,
% 2.39/1.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK2,sK6),sK5) != iProver_top
% 2.39/1.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
% 2.39/1.01      inference(predicate_to_equality,[status(thm)],[c_2366]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_3241,plain,
% 2.39/1.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK6),sK5) != iProver_top
% 2.39/1.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
% 2.39/1.01      inference(light_normalisation,[status(thm)],[c_3156,c_2364]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_5207,plain,
% 2.39/1.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,sK4),sK5) != iProver_top
% 2.39/1.01      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
% 2.39/1.01      inference(demodulation,[status(thm)],[c_5193,c_3241]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_5519,plain,
% 2.39/1.01      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK4,sK2),sK5) != iProver_top ),
% 2.39/1.01      inference(demodulation,[status(thm)],[c_5515,c_5207]) ).
% 2.39/1.01  
% 2.39/1.01  cnf(c_5523,plain,
% 2.39/1.01      ( $false ),
% 2.39/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_5518,c_5519]) ).
% 2.39/1.01  
% 2.39/1.01  
% 2.39/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.39/1.01  
% 2.39/1.01  ------                               Statistics
% 2.39/1.01  
% 2.39/1.01  ------ General
% 2.39/1.01  
% 2.39/1.01  abstr_ref_over_cycles:                  0
% 2.39/1.01  abstr_ref_under_cycles:                 0
% 2.39/1.01  gc_basic_clause_elim:                   0
% 2.39/1.01  forced_gc_time:                         0
% 2.39/1.01  parsing_time:                           0.015
% 2.39/1.01  unif_index_cands_time:                  0.
% 2.39/1.01  unif_index_add_time:                    0.
% 2.39/1.01  orderings_time:                         0.
% 2.39/1.01  out_proof_time:                         0.013
% 2.39/1.01  total_time:                             0.196
% 2.39/1.01  num_of_symbols:                         56
% 2.39/1.01  num_of_terms:                           2898
% 2.39/1.01  
% 2.39/1.01  ------ Preprocessing
% 2.39/1.01  
% 2.39/1.01  num_of_splits:                          0
% 2.39/1.01  num_of_split_atoms:                     0
% 2.39/1.01  num_of_reused_defs:                     0
% 2.39/1.01  num_eq_ax_congr_red:                    4
% 2.39/1.01  num_of_sem_filtered_clauses:            1
% 2.39/1.01  num_of_subtypes:                        5
% 2.39/1.01  monotx_restored_types:                  1
% 2.39/1.01  sat_num_of_epr_types:                   0
% 2.39/1.01  sat_num_of_non_cyclic_types:            0
% 2.39/1.01  sat_guarded_non_collapsed_types:        0
% 2.39/1.01  num_pure_diseq_elim:                    0
% 2.39/1.01  simp_replaced_by:                       0
% 2.39/1.01  res_preprocessed:                       161
% 2.39/1.01  prep_upred:                             0
% 2.39/1.01  prep_unflattend:                        54
% 2.39/1.01  smt_new_axioms:                         0
% 2.39/1.01  pred_elim_cands:                        9
% 2.39/1.01  pred_elim:                              1
% 2.39/1.01  pred_elim_cl:                           2
% 2.39/1.01  pred_elim_cycles:                       7
% 2.39/1.01  merged_defs:                            8
% 2.39/1.01  merged_defs_ncl:                        0
% 2.39/1.01  bin_hyper_res:                          8
% 2.39/1.01  prep_cycles:                            4
% 2.39/1.01  pred_elim_time:                         0.05
% 2.39/1.01  splitting_time:                         0.
% 2.39/1.01  sem_filter_time:                        0.
% 2.39/1.01  monotx_time:                            0.
% 2.39/1.01  subtype_inf_time:                       0.001
% 2.39/1.01  
% 2.39/1.01  ------ Problem properties
% 2.39/1.01  
% 2.39/1.01  clauses:                                28
% 2.39/1.01  conjectures:                            22
% 2.39/1.01  epr:                                    16
% 2.39/1.01  horn:                                   24
% 2.39/1.01  ground:                                 23
% 2.39/1.01  unary:                                  20
% 2.39/1.01  binary:                                 3
% 2.39/1.01  lits:                                   61
% 2.39/1.01  lits_eq:                                5
% 2.39/1.01  fd_pure:                                0
% 2.39/1.01  fd_pseudo:                              0
% 2.39/1.01  fd_cond:                                0
% 2.39/1.01  fd_pseudo_cond:                         1
% 2.39/1.01  ac_symbols:                             0
% 2.39/1.01  
% 2.39/1.01  ------ Propositional Solver
% 2.39/1.01  
% 2.39/1.01  prop_solver_calls:                      27
% 2.39/1.01  prop_fast_solver_calls:                 1770
% 2.39/1.01  smt_solver_calls:                       0
% 2.39/1.01  smt_fast_solver_calls:                  0
% 2.39/1.01  prop_num_of_clauses:                    1134
% 2.39/1.01  prop_preprocess_simplified:             4594
% 2.39/1.01  prop_fo_subsumed:                       88
% 2.39/1.01  prop_solver_time:                       0.
% 2.39/1.01  smt_solver_time:                        0.
% 2.39/1.01  smt_fast_solver_time:                   0.
% 2.39/1.01  prop_fast_solver_time:                  0.
% 2.39/1.01  prop_unsat_core_time:                   0.
% 2.39/1.01  
% 2.39/1.01  ------ QBF
% 2.39/1.01  
% 2.39/1.01  qbf_q_res:                              0
% 2.39/1.01  qbf_num_tautologies:                    0
% 2.39/1.01  qbf_prep_cycles:                        0
% 2.39/1.01  
% 2.39/1.01  ------ BMC1
% 2.39/1.01  
% 2.39/1.01  bmc1_current_bound:                     -1
% 2.39/1.01  bmc1_last_solved_bound:                 -1
% 2.39/1.01  bmc1_unsat_core_size:                   -1
% 2.39/1.01  bmc1_unsat_core_parents_size:           -1
% 2.39/1.01  bmc1_merge_next_fun:                    0
% 2.39/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.39/1.01  
% 2.39/1.01  ------ Instantiation
% 2.39/1.01  
% 2.39/1.01  inst_num_of_clauses:                    343
% 2.39/1.01  inst_num_in_passive:                    27
% 2.39/1.01  inst_num_in_active:                     258
% 2.39/1.01  inst_num_in_unprocessed:                58
% 2.39/1.01  inst_num_of_loops:                      270
% 2.39/1.01  inst_num_of_learning_restarts:          0
% 2.39/1.01  inst_num_moves_active_passive:          8
% 2.39/1.01  inst_lit_activity:                      0
% 2.39/1.01  inst_lit_activity_moves:                0
% 2.39/1.01  inst_num_tautologies:                   0
% 2.39/1.01  inst_num_prop_implied:                  0
% 2.39/1.01  inst_num_existing_simplified:           0
% 2.39/1.01  inst_num_eq_res_simplified:             0
% 2.39/1.01  inst_num_child_elim:                    0
% 2.39/1.01  inst_num_of_dismatching_blockings:      59
% 2.39/1.01  inst_num_of_non_proper_insts:           387
% 2.39/1.01  inst_num_of_duplicates:                 0
% 2.39/1.01  inst_inst_num_from_inst_to_res:         0
% 2.39/1.01  inst_dismatching_checking_time:         0.
% 2.39/1.01  
% 2.39/1.01  ------ Resolution
% 2.39/1.01  
% 2.39/1.01  res_num_of_clauses:                     0
% 2.39/1.01  res_num_in_passive:                     0
% 2.39/1.01  res_num_in_active:                      0
% 2.39/1.01  res_num_of_loops:                       165
% 2.39/1.01  res_forward_subset_subsumed:            88
% 2.39/1.01  res_backward_subset_subsumed:           0
% 2.39/1.01  res_forward_subsumed:                   0
% 2.39/1.01  res_backward_subsumed:                  0
% 2.39/1.01  res_forward_subsumption_resolution:     6
% 2.39/1.01  res_backward_subsumption_resolution:    0
% 2.39/1.01  res_clause_to_clause_subsumption:       109
% 2.39/1.01  res_orphan_elimination:                 0
% 2.39/1.01  res_tautology_del:                      69
% 2.39/1.01  res_num_eq_res_simplified:              0
% 2.39/1.01  res_num_sel_changes:                    0
% 2.39/1.01  res_moves_from_active_to_pass:          0
% 2.39/1.01  
% 2.39/1.01  ------ Superposition
% 2.39/1.01  
% 2.39/1.01  sup_time_total:                         0.
% 2.39/1.01  sup_time_generating:                    0.
% 2.39/1.01  sup_time_sim_full:                      0.
% 2.39/1.01  sup_time_sim_immed:                     0.
% 2.39/1.01  
% 2.39/1.01  sup_num_of_clauses:                     43
% 2.39/1.01  sup_num_in_active:                      35
% 2.39/1.01  sup_num_in_passive:                     8
% 2.39/1.01  sup_num_of_loops:                       53
% 2.39/1.01  sup_fw_superposition:                   25
% 2.39/1.01  sup_bw_superposition:                   15
% 2.39/1.01  sup_immediate_simplified:               6
% 2.39/1.01  sup_given_eliminated:                   1
% 2.39/1.01  comparisons_done:                       0
% 2.39/1.01  comparisons_avoided:                    3
% 2.39/1.01  
% 2.39/1.01  ------ Simplifications
% 2.39/1.01  
% 2.39/1.01  
% 2.39/1.01  sim_fw_subset_subsumed:                 2
% 2.39/1.01  sim_bw_subset_subsumed:                 6
% 2.39/1.01  sim_fw_subsumed:                        0
% 2.39/1.01  sim_bw_subsumed:                        0
% 2.39/1.01  sim_fw_subsumption_res:                 2
% 2.39/1.01  sim_bw_subsumption_res:                 0
% 2.39/1.01  sim_tautology_del:                      2
% 2.39/1.01  sim_eq_tautology_del:                   4
% 2.39/1.01  sim_eq_res_simp:                        0
% 2.39/1.01  sim_fw_demodulated:                     0
% 2.39/1.01  sim_bw_demodulated:                     14
% 2.39/1.01  sim_light_normalised:                   10
% 2.39/1.01  sim_joinable_taut:                      0
% 2.39/1.01  sim_joinable_simp:                      0
% 2.39/1.01  sim_ac_normalised:                      0
% 2.39/1.01  sim_smt_subsumption:                    0
% 2.39/1.01  
%------------------------------------------------------------------------------
