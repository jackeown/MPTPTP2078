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
% DateTime   : Thu Dec  3 12:23:05 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  168 (1703 expanded)
%              Number of clauses        :   95 ( 299 expanded)
%              Number of leaves         :   20 ( 714 expanded)
%              Depth                    :   22
%              Number of atoms          :  997 (35785 expanded)
%              Number of equality atoms :  222 (2276 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f44,plain,(
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
          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK8),X5) )
        & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
          | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK8),X5) )
        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK8)
        & X0 = X3
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK7)
              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK7) )
            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK7)
              | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK7) )
            & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
            & X0 = X3
            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X6) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK7,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
                ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK6,X2),X5)
                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK6,X2),X5)
                  | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) )
                & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK6,X6)
                & X0 = X3
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X6) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
                      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK5,X2,X6),X5) )
                    & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)
                      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK5,X2,X6),X5) )
                    & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK5),u1_struct_0(X1),X4,X6)
                    & sK5 = X0
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                    & v1_funct_2(X6,u1_struct_0(sK5),u1_struct_0(X1))
                    & v1_funct_1(X6) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
                        ( ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK4),X5)
                          | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,X6),X5) )
                        & ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK4),X5)
                          | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,X6),X5) )
                        & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                        & X0 = X3
                        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X6) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
                            ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X4,X2),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X3,X2,X6),X5) )
                            & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X4,X2),X5)
                              | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X3,X2,X6),X5) )
                            & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK3),u1_struct_0(X3),u1_struct_0(sK3),X4,X6)
                            & X0 = X3
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK3))
                            & v1_funct_1(X6) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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
                              ( ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK2,X1,X4,X2),X5)
                                | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,X3,X2,X6),X5) )
                              & ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK2,X1,X4,X2),X5)
                                | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,X3,X2,X6),X5) )
                              & r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6)
                              & sK2 = X3
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7)
      | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) )
    & ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7)
      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) )
    & r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8)
    & sK2 = sK5
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f37,f44,f43,f42,f41,f40,f39,f38])).

fof(f66,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f60,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f61,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f33])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f31])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK1(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f80,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    sK2 = sK5 ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7)
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_11,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2932,plain,
    ( m1_pre_topc(X0_57,X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3764,plain,
    ( m1_pre_topc(X0_57,X0_57) = iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2932])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2916,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_3779,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2916])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2921,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_3774,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2921])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2933,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_pre_topc(X2_57,X3_57)
    | ~ m1_pre_topc(X2_57,X0_57)
    | ~ m1_pre_topc(X0_57,X3_57)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ v1_funct_1(X0_56)
    | v2_struct_0(X3_57)
    | v2_struct_0(X1_57)
    | ~ v2_pre_topc(X1_57)
    | ~ v2_pre_topc(X3_57)
    | ~ l1_pre_topc(X1_57)
    | ~ l1_pre_topc(X3_57)
    | k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_56,u1_struct_0(X2_57)) = k3_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_56) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3763,plain,
    ( k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_56,u1_struct_0(X2_57)) = k3_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_56)
    | v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X0_57,X3_57) != iProver_top
    | m1_pre_topc(X2_57,X3_57) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2933])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2931,plain,
    ( ~ m1_pre_topc(X0_57,X1_57)
    | ~ m1_pre_topc(X1_57,X2_57)
    | m1_pre_topc(X0_57,X2_57)
    | ~ v2_pre_topc(X2_57)
    | ~ l1_pre_topc(X2_57) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3765,plain,
    ( m1_pre_topc(X0_57,X1_57) != iProver_top
    | m1_pre_topc(X1_57,X2_57) != iProver_top
    | m1_pre_topc(X0_57,X2_57) = iProver_top
    | v2_pre_topc(X2_57) != iProver_top
    | l1_pre_topc(X2_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2931])).

cnf(c_3918,plain,
    ( k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_56,u1_struct_0(X2_57)) = k3_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_56)
    | v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_pre_topc(X0_57,X3_57) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X3_57) = iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X3_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X3_57) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3763,c_3765])).

cnf(c_5727,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK3,sK2,X0_57,sK6)
    | v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_57) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3774,c_3918])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_39,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_40,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_41,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_46,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_47,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5977,plain,
    ( l1_pre_topc(X1_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK3,sK2,X0_57,sK6)
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_57) != iProver_top
    | v2_pre_topc(X1_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5727,c_39,c_40,c_41,c_46,c_47])).

cnf(c_5978,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK3,sK2,X0_57,sK6)
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_5977])).

cnf(c_5989,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) = k3_tmap_1(X0_57,sK3,sK2,sK4,sK6)
    | m1_pre_topc(sK2,X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_3779,c_5978])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2934,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57))
    | ~ m1_pre_topc(X2_57,X0_57)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
    | ~ v1_funct_1(X0_56)
    | v2_struct_0(X1_57)
    | v2_struct_0(X0_57)
    | ~ v2_pre_topc(X1_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57)
    | ~ l1_pre_topc(X1_57)
    | k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_56,u1_struct_0(X2_57)) = k2_tmap_1(X0_57,X1_57,X0_56,X2_57) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3762,plain,
    ( k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_56,u1_struct_0(X2_57)) = k2_tmap_1(X0_57,X1_57,X0_56,X2_57)
    | v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
    | m1_pre_topc(X2_57,X0_57) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_pre_topc(X1_57) != iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2934])).

cnf(c_4990,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0_57)) = k2_tmap_1(sK2,sK3,sK6,X0_57)
    | v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_57,sK2) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3774,c_3762])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_36,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_37,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_38,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5243,plain,
    ( m1_pre_topc(X0_57,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0_57)) = k2_tmap_1(sK2,sK3,sK6,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4990,c_36,c_37,c_38,c_39,c_40,c_41,c_46,c_47])).

cnf(c_5244,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0_57)) = k2_tmap_1(sK2,sK3,sK6,X0_57)
    | m1_pre_topc(X0_57,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5243])).

cnf(c_5251,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) = k2_tmap_1(sK2,sK3,sK6,sK4) ),
    inference(superposition,[status(thm)],[c_3779,c_5244])).

cnf(c_6015,plain,
    ( k3_tmap_1(X0_57,sK3,sK2,sK4,sK6) = k2_tmap_1(sK2,sK3,sK6,sK4)
    | m1_pre_topc(sK2,X0_57) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5989,c_5251])).

cnf(c_6107,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,sK6) = k2_tmap_1(sK2,sK3,sK6,sK4)
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3764,c_6015])).

cnf(c_6184,plain,
    ( k3_tmap_1(sK2,sK3,sK2,sK4,sK6) = k2_tmap_1(sK2,sK3,sK6,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6107,c_36,c_37,c_38])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f53])).

cnf(c_15,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_497,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | X3 = X0
    | u1_struct_0(sK5) != X4
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK3) != X5
    | u1_struct_0(sK3) != X2
    | sK8 != X3
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_498,plain,
    ( ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK3))
    | sK8 = sK6 ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_500,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | sK8 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_498,c_25,c_24,c_23,c_19,c_18,c_17])).

cnf(c_2907,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | sK8 = sK6 ),
    inference(subtyping,[status(esa)],[c_500])).

cnf(c_3788,plain,
    ( sK8 = sK6
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2907])).

cnf(c_6,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2935,plain,
    ( m1_subset_1(sK1(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
    | v2_struct_0(X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3761,plain,
    ( m1_subset_1(sK1(X0_57),k1_zfmisc_1(u1_struct_0(X0_57))) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2935])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_444,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | X2 != X0
    | k1_xboole_0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_445,plain,
    ( r2_hidden(sK0(X0,k1_xboole_0),X0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | X2 != X0
    | sK0(X2,k1_xboole_0) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_445])).

cnf(c_475,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_2908,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
    | ~ v1_xboole_0(X1_56)
    | k1_xboole_0 = X0_56 ),
    inference(subtyping,[status(esa)],[c_475])).

cnf(c_3787,plain,
    ( k1_xboole_0 = X0_56
    | m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) != iProver_top
    | v1_xboole_0(X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2908])).

cnf(c_4781,plain,
    ( sK1(X0_57) = k1_xboole_0
    | v2_struct_0(X0_57) = iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_57)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3761,c_3787])).

cnf(c_4975,plain,
    ( sK1(sK3) = k1_xboole_0
    | sK8 = sK6
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3788,c_4781])).

cnf(c_4976,plain,
    ( v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK1(sK3) = k1_xboole_0
    | sK8 = sK6 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4975])).

cnf(c_5498,plain,
    ( sK8 = sK6
    | sK1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4975,c_32,c_31,c_30,c_4976])).

cnf(c_5499,plain,
    ( sK1(sK3) = k1_xboole_0
    | sK8 = sK6 ),
    inference(renaming,[status(thm)],[c_5498])).

cnf(c_5,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2936,plain,
    ( v2_struct_0(X0_57)
    | ~ v2_pre_topc(X0_57)
    | ~ l1_pre_topc(X0_57)
    | ~ v1_xboole_0(sK1(X0_57)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3760,plain,
    ( v2_struct_0(X0_57) = iProver_top
    | v2_pre_topc(X0_57) != iProver_top
    | l1_pre_topc(X0_57) != iProver_top
    | v1_xboole_0(sK1(X0_57)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2936])).

cnf(c_5503,plain,
    ( sK8 = sK6
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5499,c_3760])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_86,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5527,plain,
    ( sK8 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5503,c_39,c_40,c_41,c_86])).

cnf(c_14,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2929,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3767,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) = iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2929])).

cnf(c_16,negated_conjecture,
    ( sK2 = sK5 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2928,negated_conjecture,
    ( sK2 = sK5 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3863,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK4,sK8),sK7) = iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3767,c_2928])).

cnf(c_5535,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK4,sK6),sK7) = iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5527,c_3863])).

cnf(c_6187,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6184,c_5535])).

cnf(c_13,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2930,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)
    | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3766,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2930])).

cnf(c_3868,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK4,sK8),sK7) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3766,c_2928])).

cnf(c_5534,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK4,sK6),sK7) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5527,c_3868])).

cnf(c_6188,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6184,c_5534])).

cnf(c_6192,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6187,c_6188])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.50/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.01  
% 2.50/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.50/1.01  
% 2.50/1.01  ------  iProver source info
% 2.50/1.01  
% 2.50/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.50/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.50/1.01  git: non_committed_changes: false
% 2.50/1.01  git: last_make_outside_of_git: false
% 2.50/1.01  
% 2.50/1.01  ------ 
% 2.50/1.01  
% 2.50/1.01  ------ Input Options
% 2.50/1.01  
% 2.50/1.01  --out_options                           all
% 2.50/1.01  --tptp_safe_out                         true
% 2.50/1.01  --problem_path                          ""
% 2.50/1.01  --include_path                          ""
% 2.50/1.01  --clausifier                            res/vclausify_rel
% 2.50/1.01  --clausifier_options                    --mode clausify
% 2.50/1.01  --stdin                                 false
% 2.50/1.01  --stats_out                             all
% 2.50/1.01  
% 2.50/1.01  ------ General Options
% 2.50/1.01  
% 2.50/1.01  --fof                                   false
% 2.50/1.01  --time_out_real                         305.
% 2.50/1.01  --time_out_virtual                      -1.
% 2.50/1.01  --symbol_type_check                     false
% 2.50/1.01  --clausify_out                          false
% 2.50/1.01  --sig_cnt_out                           false
% 2.50/1.01  --trig_cnt_out                          false
% 2.50/1.01  --trig_cnt_out_tolerance                1.
% 2.50/1.01  --trig_cnt_out_sk_spl                   false
% 2.50/1.01  --abstr_cl_out                          false
% 2.50/1.01  
% 2.50/1.01  ------ Global Options
% 2.50/1.01  
% 2.50/1.01  --schedule                              default
% 2.50/1.01  --add_important_lit                     false
% 2.50/1.01  --prop_solver_per_cl                    1000
% 2.50/1.01  --min_unsat_core                        false
% 2.50/1.01  --soft_assumptions                      false
% 2.50/1.01  --soft_lemma_size                       3
% 2.50/1.01  --prop_impl_unit_size                   0
% 2.50/1.01  --prop_impl_unit                        []
% 2.50/1.01  --share_sel_clauses                     true
% 2.50/1.01  --reset_solvers                         false
% 2.50/1.01  --bc_imp_inh                            [conj_cone]
% 2.50/1.01  --conj_cone_tolerance                   3.
% 2.50/1.01  --extra_neg_conj                        none
% 2.50/1.01  --large_theory_mode                     true
% 2.50/1.01  --prolific_symb_bound                   200
% 2.50/1.01  --lt_threshold                          2000
% 2.50/1.01  --clause_weak_htbl                      true
% 2.50/1.01  --gc_record_bc_elim                     false
% 2.50/1.01  
% 2.50/1.01  ------ Preprocessing Options
% 2.50/1.01  
% 2.50/1.01  --preprocessing_flag                    true
% 2.50/1.01  --time_out_prep_mult                    0.1
% 2.50/1.01  --splitting_mode                        input
% 2.50/1.01  --splitting_grd                         true
% 2.50/1.01  --splitting_cvd                         false
% 2.50/1.01  --splitting_cvd_svl                     false
% 2.50/1.01  --splitting_nvd                         32
% 2.50/1.01  --sub_typing                            true
% 2.50/1.01  --prep_gs_sim                           true
% 2.50/1.01  --prep_unflatten                        true
% 2.50/1.01  --prep_res_sim                          true
% 2.50/1.01  --prep_upred                            true
% 2.50/1.01  --prep_sem_filter                       exhaustive
% 2.50/1.01  --prep_sem_filter_out                   false
% 2.50/1.01  --pred_elim                             true
% 2.50/1.01  --res_sim_input                         true
% 2.50/1.01  --eq_ax_congr_red                       true
% 2.50/1.01  --pure_diseq_elim                       true
% 2.50/1.01  --brand_transform                       false
% 2.50/1.01  --non_eq_to_eq                          false
% 2.50/1.01  --prep_def_merge                        true
% 2.50/1.01  --prep_def_merge_prop_impl              false
% 2.50/1.01  --prep_def_merge_mbd                    true
% 2.50/1.01  --prep_def_merge_tr_red                 false
% 2.50/1.01  --prep_def_merge_tr_cl                  false
% 2.50/1.01  --smt_preprocessing                     true
% 2.50/1.01  --smt_ac_axioms                         fast
% 2.50/1.01  --preprocessed_out                      false
% 2.50/1.01  --preprocessed_stats                    false
% 2.50/1.01  
% 2.50/1.01  ------ Abstraction refinement Options
% 2.50/1.01  
% 2.50/1.01  --abstr_ref                             []
% 2.50/1.01  --abstr_ref_prep                        false
% 2.50/1.01  --abstr_ref_until_sat                   false
% 2.50/1.01  --abstr_ref_sig_restrict                funpre
% 2.50/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/1.01  --abstr_ref_under                       []
% 2.50/1.01  
% 2.50/1.01  ------ SAT Options
% 2.50/1.01  
% 2.50/1.01  --sat_mode                              false
% 2.50/1.01  --sat_fm_restart_options                ""
% 2.50/1.01  --sat_gr_def                            false
% 2.50/1.01  --sat_epr_types                         true
% 2.50/1.01  --sat_non_cyclic_types                  false
% 2.50/1.01  --sat_finite_models                     false
% 2.50/1.01  --sat_fm_lemmas                         false
% 2.50/1.01  --sat_fm_prep                           false
% 2.50/1.01  --sat_fm_uc_incr                        true
% 2.50/1.01  --sat_out_model                         small
% 2.50/1.01  --sat_out_clauses                       false
% 2.50/1.01  
% 2.50/1.01  ------ QBF Options
% 2.50/1.01  
% 2.50/1.01  --qbf_mode                              false
% 2.50/1.01  --qbf_elim_univ                         false
% 2.50/1.01  --qbf_dom_inst                          none
% 2.50/1.01  --qbf_dom_pre_inst                      false
% 2.50/1.01  --qbf_sk_in                             false
% 2.50/1.01  --qbf_pred_elim                         true
% 2.50/1.01  --qbf_split                             512
% 2.50/1.01  
% 2.50/1.01  ------ BMC1 Options
% 2.50/1.01  
% 2.50/1.01  --bmc1_incremental                      false
% 2.50/1.01  --bmc1_axioms                           reachable_all
% 2.50/1.01  --bmc1_min_bound                        0
% 2.50/1.01  --bmc1_max_bound                        -1
% 2.50/1.01  --bmc1_max_bound_default                -1
% 2.50/1.01  --bmc1_symbol_reachability              true
% 2.50/1.01  --bmc1_property_lemmas                  false
% 2.50/1.01  --bmc1_k_induction                      false
% 2.50/1.01  --bmc1_non_equiv_states                 false
% 2.50/1.01  --bmc1_deadlock                         false
% 2.50/1.01  --bmc1_ucm                              false
% 2.50/1.01  --bmc1_add_unsat_core                   none
% 2.50/1.01  --bmc1_unsat_core_children              false
% 2.50/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/1.01  --bmc1_out_stat                         full
% 2.50/1.01  --bmc1_ground_init                      false
% 2.50/1.01  --bmc1_pre_inst_next_state              false
% 2.50/1.01  --bmc1_pre_inst_state                   false
% 2.50/1.01  --bmc1_pre_inst_reach_state             false
% 2.50/1.01  --bmc1_out_unsat_core                   false
% 2.50/1.01  --bmc1_aig_witness_out                  false
% 2.50/1.01  --bmc1_verbose                          false
% 2.50/1.01  --bmc1_dump_clauses_tptp                false
% 2.50/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.50/1.01  --bmc1_dump_file                        -
% 2.50/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.50/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.50/1.01  --bmc1_ucm_extend_mode                  1
% 2.50/1.01  --bmc1_ucm_init_mode                    2
% 2.50/1.01  --bmc1_ucm_cone_mode                    none
% 2.50/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.50/1.01  --bmc1_ucm_relax_model                  4
% 2.50/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.50/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/1.01  --bmc1_ucm_layered_model                none
% 2.50/1.01  --bmc1_ucm_max_lemma_size               10
% 2.50/1.01  
% 2.50/1.01  ------ AIG Options
% 2.50/1.01  
% 2.50/1.01  --aig_mode                              false
% 2.50/1.01  
% 2.50/1.01  ------ Instantiation Options
% 2.50/1.01  
% 2.50/1.01  --instantiation_flag                    true
% 2.50/1.01  --inst_sos_flag                         false
% 2.50/1.01  --inst_sos_phase                        true
% 2.50/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/1.01  --inst_lit_sel_side                     num_symb
% 2.50/1.01  --inst_solver_per_active                1400
% 2.50/1.01  --inst_solver_calls_frac                1.
% 2.50/1.01  --inst_passive_queue_type               priority_queues
% 2.50/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/1.01  --inst_passive_queues_freq              [25;2]
% 2.50/1.01  --inst_dismatching                      true
% 2.50/1.01  --inst_eager_unprocessed_to_passive     true
% 2.50/1.01  --inst_prop_sim_given                   true
% 2.50/1.01  --inst_prop_sim_new                     false
% 2.50/1.01  --inst_subs_new                         false
% 2.50/1.01  --inst_eq_res_simp                      false
% 2.50/1.01  --inst_subs_given                       false
% 2.50/1.01  --inst_orphan_elimination               true
% 2.50/1.01  --inst_learning_loop_flag               true
% 2.50/1.01  --inst_learning_start                   3000
% 2.50/1.01  --inst_learning_factor                  2
% 2.50/1.01  --inst_start_prop_sim_after_learn       3
% 2.50/1.01  --inst_sel_renew                        solver
% 2.50/1.01  --inst_lit_activity_flag                true
% 2.50/1.01  --inst_restr_to_given                   false
% 2.50/1.01  --inst_activity_threshold               500
% 2.50/1.01  --inst_out_proof                        true
% 2.50/1.01  
% 2.50/1.01  ------ Resolution Options
% 2.50/1.01  
% 2.50/1.01  --resolution_flag                       true
% 2.50/1.01  --res_lit_sel                           adaptive
% 2.50/1.01  --res_lit_sel_side                      none
% 2.50/1.01  --res_ordering                          kbo
% 2.50/1.01  --res_to_prop_solver                    active
% 2.50/1.01  --res_prop_simpl_new                    false
% 2.50/1.01  --res_prop_simpl_given                  true
% 2.50/1.01  --res_passive_queue_type                priority_queues
% 2.50/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/1.01  --res_passive_queues_freq               [15;5]
% 2.50/1.01  --res_forward_subs                      full
% 2.50/1.01  --res_backward_subs                     full
% 2.50/1.01  --res_forward_subs_resolution           true
% 2.50/1.01  --res_backward_subs_resolution          true
% 2.50/1.01  --res_orphan_elimination                true
% 2.50/1.01  --res_time_limit                        2.
% 2.50/1.01  --res_out_proof                         true
% 2.50/1.01  
% 2.50/1.01  ------ Superposition Options
% 2.50/1.01  
% 2.50/1.01  --superposition_flag                    true
% 2.50/1.01  --sup_passive_queue_type                priority_queues
% 2.50/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.50/1.01  --demod_completeness_check              fast
% 2.50/1.01  --demod_use_ground                      true
% 2.50/1.01  --sup_to_prop_solver                    passive
% 2.50/1.01  --sup_prop_simpl_new                    true
% 2.50/1.01  --sup_prop_simpl_given                  true
% 2.50/1.01  --sup_fun_splitting                     false
% 2.50/1.01  --sup_smt_interval                      50000
% 2.50/1.01  
% 2.50/1.01  ------ Superposition Simplification Setup
% 2.50/1.01  
% 2.50/1.01  --sup_indices_passive                   []
% 2.50/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.01  --sup_full_bw                           [BwDemod]
% 2.50/1.01  --sup_immed_triv                        [TrivRules]
% 2.50/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.01  --sup_immed_bw_main                     []
% 2.50/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/1.01  
% 2.50/1.01  ------ Combination Options
% 2.50/1.01  
% 2.50/1.01  --comb_res_mult                         3
% 2.50/1.01  --comb_sup_mult                         2
% 2.50/1.01  --comb_inst_mult                        10
% 2.50/1.01  
% 2.50/1.01  ------ Debug Options
% 2.50/1.01  
% 2.50/1.01  --dbg_backtrace                         false
% 2.50/1.01  --dbg_dump_prop_clauses                 false
% 2.50/1.01  --dbg_dump_prop_clauses_file            -
% 2.50/1.01  --dbg_out_stat                          false
% 2.50/1.01  ------ Parsing...
% 2.50/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.50/1.01  
% 2.50/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.50/1.01  
% 2.50/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.50/1.01  
% 2.50/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.50/1.01  ------ Proving...
% 2.50/1.01  ------ Problem Properties 
% 2.50/1.01  
% 2.50/1.01  
% 2.50/1.01  clauses                                 31
% 2.50/1.01  conjectures                             22
% 2.50/1.01  EPR                                     17
% 2.50/1.01  Horn                                    26
% 2.50/1.01  unary                                   21
% 2.50/1.01  binary                                  4
% 2.50/1.01  lits                                    69
% 2.50/1.01  lits eq                                 5
% 2.50/1.01  fd_pure                                 0
% 2.50/1.01  fd_pseudo                               0
% 2.50/1.01  fd_cond                                 1
% 2.50/1.01  fd_pseudo_cond                          0
% 2.50/1.01  AC symbols                              0
% 2.50/1.01  
% 2.50/1.01  ------ Schedule dynamic 5 is on 
% 2.50/1.01  
% 2.50/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.50/1.01  
% 2.50/1.01  
% 2.50/1.01  ------ 
% 2.50/1.01  Current options:
% 2.50/1.01  ------ 
% 2.50/1.01  
% 2.50/1.01  ------ Input Options
% 2.50/1.01  
% 2.50/1.01  --out_options                           all
% 2.50/1.01  --tptp_safe_out                         true
% 2.50/1.01  --problem_path                          ""
% 2.50/1.01  --include_path                          ""
% 2.50/1.01  --clausifier                            res/vclausify_rel
% 2.50/1.01  --clausifier_options                    --mode clausify
% 2.50/1.01  --stdin                                 false
% 2.50/1.01  --stats_out                             all
% 2.50/1.01  
% 2.50/1.01  ------ General Options
% 2.50/1.01  
% 2.50/1.01  --fof                                   false
% 2.50/1.01  --time_out_real                         305.
% 2.50/1.01  --time_out_virtual                      -1.
% 2.50/1.01  --symbol_type_check                     false
% 2.50/1.01  --clausify_out                          false
% 2.50/1.01  --sig_cnt_out                           false
% 2.50/1.01  --trig_cnt_out                          false
% 2.50/1.01  --trig_cnt_out_tolerance                1.
% 2.50/1.01  --trig_cnt_out_sk_spl                   false
% 2.50/1.01  --abstr_cl_out                          false
% 2.50/1.01  
% 2.50/1.01  ------ Global Options
% 2.50/1.01  
% 2.50/1.01  --schedule                              default
% 2.50/1.01  --add_important_lit                     false
% 2.50/1.01  --prop_solver_per_cl                    1000
% 2.50/1.01  --min_unsat_core                        false
% 2.50/1.01  --soft_assumptions                      false
% 2.50/1.01  --soft_lemma_size                       3
% 2.50/1.01  --prop_impl_unit_size                   0
% 2.50/1.01  --prop_impl_unit                        []
% 2.50/1.01  --share_sel_clauses                     true
% 2.50/1.01  --reset_solvers                         false
% 2.50/1.01  --bc_imp_inh                            [conj_cone]
% 2.50/1.01  --conj_cone_tolerance                   3.
% 2.50/1.01  --extra_neg_conj                        none
% 2.50/1.01  --large_theory_mode                     true
% 2.50/1.01  --prolific_symb_bound                   200
% 2.50/1.01  --lt_threshold                          2000
% 2.50/1.01  --clause_weak_htbl                      true
% 2.50/1.01  --gc_record_bc_elim                     false
% 2.50/1.01  
% 2.50/1.01  ------ Preprocessing Options
% 2.50/1.01  
% 2.50/1.01  --preprocessing_flag                    true
% 2.50/1.01  --time_out_prep_mult                    0.1
% 2.50/1.01  --splitting_mode                        input
% 2.50/1.01  --splitting_grd                         true
% 2.50/1.01  --splitting_cvd                         false
% 2.50/1.01  --splitting_cvd_svl                     false
% 2.50/1.01  --splitting_nvd                         32
% 2.50/1.01  --sub_typing                            true
% 2.50/1.01  --prep_gs_sim                           true
% 2.50/1.01  --prep_unflatten                        true
% 2.50/1.01  --prep_res_sim                          true
% 2.50/1.01  --prep_upred                            true
% 2.50/1.01  --prep_sem_filter                       exhaustive
% 2.50/1.01  --prep_sem_filter_out                   false
% 2.50/1.01  --pred_elim                             true
% 2.50/1.01  --res_sim_input                         true
% 2.50/1.01  --eq_ax_congr_red                       true
% 2.50/1.01  --pure_diseq_elim                       true
% 2.50/1.01  --brand_transform                       false
% 2.50/1.01  --non_eq_to_eq                          false
% 2.50/1.01  --prep_def_merge                        true
% 2.50/1.01  --prep_def_merge_prop_impl              false
% 2.50/1.01  --prep_def_merge_mbd                    true
% 2.50/1.01  --prep_def_merge_tr_red                 false
% 2.50/1.01  --prep_def_merge_tr_cl                  false
% 2.50/1.01  --smt_preprocessing                     true
% 2.50/1.01  --smt_ac_axioms                         fast
% 2.50/1.01  --preprocessed_out                      false
% 2.50/1.01  --preprocessed_stats                    false
% 2.50/1.01  
% 2.50/1.01  ------ Abstraction refinement Options
% 2.50/1.01  
% 2.50/1.01  --abstr_ref                             []
% 2.50/1.01  --abstr_ref_prep                        false
% 2.50/1.01  --abstr_ref_until_sat                   false
% 2.50/1.01  --abstr_ref_sig_restrict                funpre
% 2.50/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/1.01  --abstr_ref_under                       []
% 2.50/1.01  
% 2.50/1.01  ------ SAT Options
% 2.50/1.01  
% 2.50/1.01  --sat_mode                              false
% 2.50/1.01  --sat_fm_restart_options                ""
% 2.50/1.01  --sat_gr_def                            false
% 2.50/1.01  --sat_epr_types                         true
% 2.50/1.01  --sat_non_cyclic_types                  false
% 2.50/1.01  --sat_finite_models                     false
% 2.50/1.01  --sat_fm_lemmas                         false
% 2.50/1.01  --sat_fm_prep                           false
% 2.50/1.01  --sat_fm_uc_incr                        true
% 2.50/1.01  --sat_out_model                         small
% 2.50/1.01  --sat_out_clauses                       false
% 2.50/1.01  
% 2.50/1.01  ------ QBF Options
% 2.50/1.01  
% 2.50/1.01  --qbf_mode                              false
% 2.50/1.01  --qbf_elim_univ                         false
% 2.50/1.01  --qbf_dom_inst                          none
% 2.50/1.01  --qbf_dom_pre_inst                      false
% 2.50/1.01  --qbf_sk_in                             false
% 2.50/1.01  --qbf_pred_elim                         true
% 2.50/1.01  --qbf_split                             512
% 2.50/1.01  
% 2.50/1.01  ------ BMC1 Options
% 2.50/1.01  
% 2.50/1.01  --bmc1_incremental                      false
% 2.50/1.01  --bmc1_axioms                           reachable_all
% 2.50/1.01  --bmc1_min_bound                        0
% 2.50/1.01  --bmc1_max_bound                        -1
% 2.50/1.01  --bmc1_max_bound_default                -1
% 2.50/1.01  --bmc1_symbol_reachability              true
% 2.50/1.01  --bmc1_property_lemmas                  false
% 2.50/1.01  --bmc1_k_induction                      false
% 2.50/1.01  --bmc1_non_equiv_states                 false
% 2.50/1.01  --bmc1_deadlock                         false
% 2.50/1.01  --bmc1_ucm                              false
% 2.50/1.01  --bmc1_add_unsat_core                   none
% 2.50/1.01  --bmc1_unsat_core_children              false
% 2.50/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/1.01  --bmc1_out_stat                         full
% 2.50/1.01  --bmc1_ground_init                      false
% 2.50/1.01  --bmc1_pre_inst_next_state              false
% 2.50/1.01  --bmc1_pre_inst_state                   false
% 2.50/1.01  --bmc1_pre_inst_reach_state             false
% 2.50/1.01  --bmc1_out_unsat_core                   false
% 2.50/1.01  --bmc1_aig_witness_out                  false
% 2.50/1.01  --bmc1_verbose                          false
% 2.50/1.01  --bmc1_dump_clauses_tptp                false
% 2.50/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.50/1.01  --bmc1_dump_file                        -
% 2.50/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.50/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.50/1.01  --bmc1_ucm_extend_mode                  1
% 2.50/1.01  --bmc1_ucm_init_mode                    2
% 2.50/1.01  --bmc1_ucm_cone_mode                    none
% 2.50/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.50/1.01  --bmc1_ucm_relax_model                  4
% 2.50/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.50/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/1.01  --bmc1_ucm_layered_model                none
% 2.50/1.01  --bmc1_ucm_max_lemma_size               10
% 2.50/1.01  
% 2.50/1.01  ------ AIG Options
% 2.50/1.01  
% 2.50/1.01  --aig_mode                              false
% 2.50/1.01  
% 2.50/1.01  ------ Instantiation Options
% 2.50/1.01  
% 2.50/1.01  --instantiation_flag                    true
% 2.50/1.01  --inst_sos_flag                         false
% 2.50/1.01  --inst_sos_phase                        true
% 2.50/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/1.01  --inst_lit_sel_side                     none
% 2.50/1.01  --inst_solver_per_active                1400
% 2.50/1.01  --inst_solver_calls_frac                1.
% 2.50/1.01  --inst_passive_queue_type               priority_queues
% 2.50/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/1.01  --inst_passive_queues_freq              [25;2]
% 2.50/1.01  --inst_dismatching                      true
% 2.50/1.01  --inst_eager_unprocessed_to_passive     true
% 2.50/1.01  --inst_prop_sim_given                   true
% 2.50/1.01  --inst_prop_sim_new                     false
% 2.50/1.01  --inst_subs_new                         false
% 2.50/1.01  --inst_eq_res_simp                      false
% 2.50/1.01  --inst_subs_given                       false
% 2.50/1.01  --inst_orphan_elimination               true
% 2.50/1.01  --inst_learning_loop_flag               true
% 2.50/1.01  --inst_learning_start                   3000
% 2.50/1.01  --inst_learning_factor                  2
% 2.50/1.01  --inst_start_prop_sim_after_learn       3
% 2.50/1.01  --inst_sel_renew                        solver
% 2.50/1.01  --inst_lit_activity_flag                true
% 2.50/1.01  --inst_restr_to_given                   false
% 2.50/1.01  --inst_activity_threshold               500
% 2.50/1.01  --inst_out_proof                        true
% 2.50/1.01  
% 2.50/1.01  ------ Resolution Options
% 2.50/1.01  
% 2.50/1.01  --resolution_flag                       false
% 2.50/1.01  --res_lit_sel                           adaptive
% 2.50/1.01  --res_lit_sel_side                      none
% 2.50/1.01  --res_ordering                          kbo
% 2.50/1.01  --res_to_prop_solver                    active
% 2.50/1.01  --res_prop_simpl_new                    false
% 2.50/1.01  --res_prop_simpl_given                  true
% 2.50/1.01  --res_passive_queue_type                priority_queues
% 2.50/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/1.01  --res_passive_queues_freq               [15;5]
% 2.50/1.01  --res_forward_subs                      full
% 2.50/1.01  --res_backward_subs                     full
% 2.50/1.01  --res_forward_subs_resolution           true
% 2.50/1.01  --res_backward_subs_resolution          true
% 2.50/1.01  --res_orphan_elimination                true
% 2.50/1.01  --res_time_limit                        2.
% 2.50/1.01  --res_out_proof                         true
% 2.50/1.01  
% 2.50/1.01  ------ Superposition Options
% 2.50/1.01  
% 2.50/1.01  --superposition_flag                    true
% 2.50/1.01  --sup_passive_queue_type                priority_queues
% 2.50/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.50/1.01  --demod_completeness_check              fast
% 2.50/1.01  --demod_use_ground                      true
% 2.50/1.01  --sup_to_prop_solver                    passive
% 2.50/1.01  --sup_prop_simpl_new                    true
% 2.50/1.01  --sup_prop_simpl_given                  true
% 2.50/1.01  --sup_fun_splitting                     false
% 2.50/1.01  --sup_smt_interval                      50000
% 2.50/1.01  
% 2.50/1.01  ------ Superposition Simplification Setup
% 2.50/1.01  
% 2.50/1.01  --sup_indices_passive                   []
% 2.50/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.01  --sup_full_bw                           [BwDemod]
% 2.50/1.01  --sup_immed_triv                        [TrivRules]
% 2.50/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.01  --sup_immed_bw_main                     []
% 2.50/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/1.01  
% 2.50/1.01  ------ Combination Options
% 2.50/1.01  
% 2.50/1.01  --comb_res_mult                         3
% 2.50/1.01  --comb_sup_mult                         2
% 2.50/1.01  --comb_inst_mult                        10
% 2.50/1.01  
% 2.50/1.01  ------ Debug Options
% 2.50/1.01  
% 2.50/1.01  --dbg_backtrace                         false
% 2.50/1.01  --dbg_dump_prop_clauses                 false
% 2.50/1.01  --dbg_dump_prop_clauses_file            -
% 2.50/1.01  --dbg_out_stat                          false
% 2.50/1.01  
% 2.50/1.01  
% 2.50/1.01  
% 2.50/1.01  
% 2.50/1.01  ------ Proving...
% 2.50/1.01  
% 2.50/1.01  
% 2.50/1.01  % SZS status Theorem for theBenchmark.p
% 2.50/1.01  
% 2.50/1.01   Resolution empty clause
% 2.50/1.01  
% 2.50/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.50/1.01  
% 2.50/1.01  fof(f9,axiom,(
% 2.50/1.01    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f26,plain,(
% 2.50/1.01    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.50/1.01    inference(ennf_transformation,[],[f9])).
% 2.50/1.01  
% 2.50/1.01  fof(f57,plain,(
% 2.50/1.01    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f26])).
% 2.50/1.01  
% 2.50/1.01  fof(f11,conjecture,(
% 2.50/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 2.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f12,negated_conjecture,(
% 2.50/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 2.50/1.01    inference(negated_conjecture,[],[f11])).
% 2.50/1.01  
% 2.50/1.01  fof(f29,plain,(
% 2.50/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.50/1.01    inference(ennf_transformation,[],[f12])).
% 2.50/1.01  
% 2.50/1.01  fof(f30,plain,(
% 2.50/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.50/1.01    inference(flattening,[],[f29])).
% 2.50/1.01  
% 2.50/1.01  fof(f36,plain,(
% 2.50/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.50/1.01    inference(nnf_transformation,[],[f30])).
% 2.50/1.01  
% 2.50/1.01  fof(f37,plain,(
% 2.50/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.50/1.01    inference(flattening,[],[f36])).
% 2.50/1.01  
% 2.50/1.01  fof(f44,plain,(
% 2.50/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK8),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK8),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK8) & X0 = X3 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 2.50/1.01    introduced(choice_axiom,[])).
% 2.50/1.01  
% 2.50/1.01  fof(f43,plain,(
% 2.50/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK7) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK7)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK7) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK7)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK7,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 2.50/1.01    introduced(choice_axiom,[])).
% 2.50/1.01  
% 2.50/1.01  fof(f42,plain,(
% 2.50/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK6,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK6,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK6,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 2.50/1.01    introduced(choice_axiom,[])).
% 2.50/1.01  
% 2.50/1.01  fof(f41,plain,(
% 2.50/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK5,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK5,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK5),u1_struct_0(X1),X4,X6) & sK5 = X0 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 2.50/1.01    introduced(choice_axiom,[])).
% 2.50/1.01  
% 2.50/1.01  fof(f40,plain,(
% 2.50/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK4),X5) | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,X6),X5)) & (r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK4),X5) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.50/1.01    introduced(choice_axiom,[])).
% 2.50/1.01  
% 2.50/1.01  fof(f39,plain,(
% 2.50/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k2_tmap_1(X0,sK3,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK3),u1_struct_0(X3),u1_struct_0(sK3),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 2.50/1.01    introduced(choice_axiom,[])).
% 2.50/1.01  
% 2.50/1.01  fof(f38,plain,(
% 2.50/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK2,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK2,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK2,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK2 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.50/1.01    introduced(choice_axiom,[])).
% 2.50/1.01  
% 2.50/1.01  fof(f45,plain,(
% 2.50/1.01    (((((((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)) & (r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)) & r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8) & sK2 = sK5 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.50/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f37,f44,f43,f42,f41,f40,f39,f38])).
% 2.50/1.01  
% 2.50/1.01  fof(f66,plain,(
% 2.50/1.01    m1_pre_topc(sK4,sK2)),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f71,plain,(
% 2.50/1.01    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f8,axiom,(
% 2.50/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f24,plain,(
% 2.50/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.50/1.01    inference(ennf_transformation,[],[f8])).
% 2.50/1.01  
% 2.50/1.01  fof(f25,plain,(
% 2.50/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.50/1.01    inference(flattening,[],[f24])).
% 2.50/1.01  
% 2.50/1.01  fof(f56,plain,(
% 2.50/1.01    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f25])).
% 2.50/1.01  
% 2.50/1.01  fof(f10,axiom,(
% 2.50/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f27,plain,(
% 2.50/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.50/1.01    inference(ennf_transformation,[],[f10])).
% 2.50/1.01  
% 2.50/1.01  fof(f28,plain,(
% 2.50/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.50/1.01    inference(flattening,[],[f27])).
% 2.50/1.01  
% 2.50/1.01  fof(f58,plain,(
% 2.50/1.01    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f28])).
% 2.50/1.01  
% 2.50/1.01  fof(f62,plain,(
% 2.50/1.01    ~v2_struct_0(sK3)),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f63,plain,(
% 2.50/1.01    v2_pre_topc(sK3)),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f64,plain,(
% 2.50/1.01    l1_pre_topc(sK3)),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f69,plain,(
% 2.50/1.01    v1_funct_1(sK6)),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f70,plain,(
% 2.50/1.01    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f7,axiom,(
% 2.50/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f22,plain,(
% 2.50/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.50/1.01    inference(ennf_transformation,[],[f7])).
% 2.50/1.01  
% 2.50/1.01  fof(f23,plain,(
% 2.50/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.50/1.01    inference(flattening,[],[f22])).
% 2.50/1.01  
% 2.50/1.01  fof(f55,plain,(
% 2.50/1.01    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f23])).
% 2.50/1.01  
% 2.50/1.01  fof(f59,plain,(
% 2.50/1.01    ~v2_struct_0(sK2)),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f60,plain,(
% 2.50/1.01    v2_pre_topc(sK2)),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f61,plain,(
% 2.50/1.01    l1_pre_topc(sK2)),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f6,axiom,(
% 2.50/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f20,plain,(
% 2.50/1.01    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.50/1.01    inference(ennf_transformation,[],[f6])).
% 2.50/1.01  
% 2.50/1.01  fof(f21,plain,(
% 2.50/1.01    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.50/1.01    inference(flattening,[],[f20])).
% 2.50/1.01  
% 2.50/1.01  fof(f35,plain,(
% 2.50/1.01    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.50/1.01    inference(nnf_transformation,[],[f21])).
% 2.50/1.01  
% 2.50/1.01  fof(f53,plain,(
% 2.50/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f35])).
% 2.50/1.01  
% 2.50/1.01  fof(f79,plain,(
% 2.50/1.01    r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8)),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f75,plain,(
% 2.50/1.01    v1_funct_1(sK8)),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f76,plain,(
% 2.50/1.01    v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3))),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f77,plain,(
% 2.50/1.01    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f5,axiom,(
% 2.50/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f14,plain,(
% 2.50/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.50/1.01    inference(pure_predicate_removal,[],[f5])).
% 2.50/1.01  
% 2.50/1.01  fof(f18,plain,(
% 2.50/1.01    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.50/1.01    inference(ennf_transformation,[],[f14])).
% 2.50/1.01  
% 2.50/1.01  fof(f19,plain,(
% 2.50/1.01    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.50/1.01    inference(flattening,[],[f18])).
% 2.50/1.01  
% 2.50/1.01  fof(f33,plain,(
% 2.50/1.01    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.50/1.01    introduced(choice_axiom,[])).
% 2.50/1.01  
% 2.50/1.01  fof(f34,plain,(
% 2.50/1.01    ! [X0] : ((~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.50/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f33])).
% 2.50/1.01  
% 2.50/1.01  fof(f51,plain,(
% 2.50/1.01    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f34])).
% 2.50/1.01  
% 2.50/1.01  fof(f4,axiom,(
% 2.50/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f17,plain,(
% 2.50/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.50/1.01    inference(ennf_transformation,[],[f4])).
% 2.50/1.01  
% 2.50/1.01  fof(f50,plain,(
% 2.50/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f17])).
% 2.50/1.01  
% 2.50/1.01  fof(f1,axiom,(
% 2.50/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f13,plain,(
% 2.50/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 2.50/1.01    inference(unused_predicate_definition_removal,[],[f1])).
% 2.50/1.01  
% 2.50/1.01  fof(f15,plain,(
% 2.50/1.01    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 2.50/1.01    inference(ennf_transformation,[],[f13])).
% 2.50/1.01  
% 2.50/1.01  fof(f31,plain,(
% 2.50/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.50/1.01    introduced(choice_axiom,[])).
% 2.50/1.01  
% 2.50/1.01  fof(f32,plain,(
% 2.50/1.01    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.50/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f31])).
% 2.50/1.01  
% 2.50/1.01  fof(f46,plain,(
% 2.50/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f32])).
% 2.50/1.01  
% 2.50/1.01  fof(f3,axiom,(
% 2.50/1.01    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f16,plain,(
% 2.50/1.01    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.50/1.01    inference(ennf_transformation,[],[f3])).
% 2.50/1.01  
% 2.50/1.01  fof(f49,plain,(
% 2.50/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f16])).
% 2.50/1.01  
% 2.50/1.01  fof(f52,plain,(
% 2.50/1.01    ( ! [X0] : (~v1_xboole_0(sK1(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.50/1.01    inference(cnf_transformation,[],[f34])).
% 2.50/1.01  
% 2.50/1.01  fof(f2,axiom,(
% 2.50/1.01    v1_xboole_0(k1_xboole_0)),
% 2.50/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.50/1.01  
% 2.50/1.01  fof(f48,plain,(
% 2.50/1.01    v1_xboole_0(k1_xboole_0)),
% 2.50/1.01    inference(cnf_transformation,[],[f2])).
% 2.50/1.01  
% 2.50/1.01  fof(f80,plain,(
% 2.50/1.01    r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f78,plain,(
% 2.50/1.01    sK2 = sK5),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  fof(f81,plain,(
% 2.50/1.01    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) | ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)),
% 2.50/1.01    inference(cnf_transformation,[],[f45])).
% 2.50/1.01  
% 2.50/1.01  cnf(c_11,plain,
% 2.50/1.01      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 2.50/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2932,plain,
% 2.50/1.01      ( m1_pre_topc(X0_57,X0_57) | ~ l1_pre_topc(X0_57) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3764,plain,
% 2.50/1.01      ( m1_pre_topc(X0_57,X0_57) = iProver_top
% 2.50/1.01      | l1_pre_topc(X0_57) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2932]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_28,negated_conjecture,
% 2.50/1.01      ( m1_pre_topc(sK4,sK2) ),
% 2.50/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2916,negated_conjecture,
% 2.50/1.01      ( m1_pre_topc(sK4,sK2) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_28]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3779,plain,
% 2.50/1.01      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2916]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_23,negated_conjecture,
% 2.50/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 2.50/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2921,negated_conjecture,
% 2.50/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_23]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3774,plain,
% 2.50/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2921]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_10,plain,
% 2.50/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.50/1.01      | ~ m1_pre_topc(X3,X4)
% 2.50/1.01      | ~ m1_pre_topc(X3,X1)
% 2.50/1.01      | ~ m1_pre_topc(X1,X4)
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.50/1.01      | ~ v1_funct_1(X0)
% 2.50/1.01      | v2_struct_0(X4)
% 2.50/1.01      | v2_struct_0(X2)
% 2.50/1.01      | ~ v2_pre_topc(X4)
% 2.50/1.01      | ~ v2_pre_topc(X2)
% 2.50/1.01      | ~ l1_pre_topc(X4)
% 2.50/1.01      | ~ l1_pre_topc(X2)
% 2.50/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.50/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2933,plain,
% 2.50/1.01      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 2.50/1.01      | ~ m1_pre_topc(X2_57,X3_57)
% 2.50/1.01      | ~ m1_pre_topc(X2_57,X0_57)
% 2.50/1.01      | ~ m1_pre_topc(X0_57,X3_57)
% 2.50/1.01      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 2.50/1.01      | ~ v1_funct_1(X0_56)
% 2.50/1.01      | v2_struct_0(X3_57)
% 2.50/1.01      | v2_struct_0(X1_57)
% 2.50/1.01      | ~ v2_pre_topc(X1_57)
% 2.50/1.01      | ~ v2_pre_topc(X3_57)
% 2.50/1.01      | ~ l1_pre_topc(X1_57)
% 2.50/1.01      | ~ l1_pre_topc(X3_57)
% 2.50/1.01      | k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_56,u1_struct_0(X2_57)) = k3_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_56) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3763,plain,
% 2.50/1.01      ( k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_56,u1_struct_0(X2_57)) = k3_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_56)
% 2.50/1.01      | v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
% 2.50/1.01      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 2.50/1.01      | m1_pre_topc(X0_57,X3_57) != iProver_top
% 2.50/1.01      | m1_pre_topc(X2_57,X3_57) != iProver_top
% 2.50/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
% 2.50/1.01      | v1_funct_1(X0_56) != iProver_top
% 2.50/1.01      | v2_struct_0(X1_57) = iProver_top
% 2.50/1.01      | v2_struct_0(X3_57) = iProver_top
% 2.50/1.01      | v2_pre_topc(X1_57) != iProver_top
% 2.50/1.01      | v2_pre_topc(X3_57) != iProver_top
% 2.50/1.01      | l1_pre_topc(X1_57) != iProver_top
% 2.50/1.01      | l1_pre_topc(X3_57) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2933]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_12,plain,
% 2.50/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.50/1.01      | ~ m1_pre_topc(X1,X2)
% 2.50/1.01      | m1_pre_topc(X0,X2)
% 2.50/1.01      | ~ v2_pre_topc(X2)
% 2.50/1.01      | ~ l1_pre_topc(X2) ),
% 2.50/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2931,plain,
% 2.50/1.01      ( ~ m1_pre_topc(X0_57,X1_57)
% 2.50/1.01      | ~ m1_pre_topc(X1_57,X2_57)
% 2.50/1.01      | m1_pre_topc(X0_57,X2_57)
% 2.50/1.01      | ~ v2_pre_topc(X2_57)
% 2.50/1.01      | ~ l1_pre_topc(X2_57) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3765,plain,
% 2.50/1.01      ( m1_pre_topc(X0_57,X1_57) != iProver_top
% 2.50/1.01      | m1_pre_topc(X1_57,X2_57) != iProver_top
% 2.50/1.01      | m1_pre_topc(X0_57,X2_57) = iProver_top
% 2.50/1.01      | v2_pre_topc(X2_57) != iProver_top
% 2.50/1.01      | l1_pre_topc(X2_57) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2931]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3918,plain,
% 2.50/1.01      ( k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_56,u1_struct_0(X2_57)) = k3_tmap_1(X3_57,X1_57,X0_57,X2_57,X0_56)
% 2.50/1.01      | v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
% 2.50/1.01      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 2.50/1.01      | m1_pre_topc(X0_57,X3_57) != iProver_top
% 2.50/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
% 2.50/1.01      | v1_funct_1(X0_56) != iProver_top
% 2.50/1.01      | v2_struct_0(X1_57) = iProver_top
% 2.50/1.01      | v2_struct_0(X3_57) = iProver_top
% 2.50/1.01      | v2_pre_topc(X1_57) != iProver_top
% 2.50/1.01      | v2_pre_topc(X3_57) != iProver_top
% 2.50/1.01      | l1_pre_topc(X1_57) != iProver_top
% 2.50/1.01      | l1_pre_topc(X3_57) != iProver_top ),
% 2.50/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_3763,c_3765]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_5727,plain,
% 2.50/1.01      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK3,sK2,X0_57,sK6)
% 2.50/1.01      | v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 2.50/1.01      | m1_pre_topc(X0_57,sK2) != iProver_top
% 2.50/1.01      | m1_pre_topc(sK2,X1_57) != iProver_top
% 2.50/1.01      | v1_funct_1(sK6) != iProver_top
% 2.50/1.01      | v2_struct_0(X1_57) = iProver_top
% 2.50/1.01      | v2_struct_0(sK3) = iProver_top
% 2.50/1.01      | v2_pre_topc(X1_57) != iProver_top
% 2.50/1.01      | v2_pre_topc(sK3) != iProver_top
% 2.50/1.01      | l1_pre_topc(X1_57) != iProver_top
% 2.50/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_3774,c_3918]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_32,negated_conjecture,
% 2.50/1.01      ( ~ v2_struct_0(sK3) ),
% 2.50/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_39,plain,
% 2.50/1.01      ( v2_struct_0(sK3) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_31,negated_conjecture,
% 2.50/1.01      ( v2_pre_topc(sK3) ),
% 2.50/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_40,plain,
% 2.50/1.01      ( v2_pre_topc(sK3) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_30,negated_conjecture,
% 2.50/1.01      ( l1_pre_topc(sK3) ),
% 2.50/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_41,plain,
% 2.50/1.01      ( l1_pre_topc(sK3) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_25,negated_conjecture,
% 2.50/1.01      ( v1_funct_1(sK6) ),
% 2.50/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_46,plain,
% 2.50/1.01      ( v1_funct_1(sK6) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_24,negated_conjecture,
% 2.50/1.01      ( v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 2.50/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_47,plain,
% 2.50/1.01      ( v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_5977,plain,
% 2.50/1.01      ( l1_pre_topc(X1_57) != iProver_top
% 2.50/1.01      | v2_struct_0(X1_57) = iProver_top
% 2.50/1.01      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK3,sK2,X0_57,sK6)
% 2.50/1.01      | m1_pre_topc(X0_57,sK2) != iProver_top
% 2.50/1.01      | m1_pre_topc(sK2,X1_57) != iProver_top
% 2.50/1.01      | v2_pre_topc(X1_57) != iProver_top ),
% 2.50/1.01      inference(global_propositional_subsumption,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_5727,c_39,c_40,c_41,c_46,c_47]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_5978,plain,
% 2.50/1.01      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0_57)) = k3_tmap_1(X1_57,sK3,sK2,X0_57,sK6)
% 2.50/1.01      | m1_pre_topc(X0_57,sK2) != iProver_top
% 2.50/1.01      | m1_pre_topc(sK2,X1_57) != iProver_top
% 2.50/1.01      | v2_struct_0(X1_57) = iProver_top
% 2.50/1.01      | v2_pre_topc(X1_57) != iProver_top
% 2.50/1.01      | l1_pre_topc(X1_57) != iProver_top ),
% 2.50/1.01      inference(renaming,[status(thm)],[c_5977]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_5989,plain,
% 2.50/1.01      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) = k3_tmap_1(X0_57,sK3,sK2,sK4,sK6)
% 2.50/1.01      | m1_pre_topc(sK2,X0_57) != iProver_top
% 2.50/1.01      | v2_struct_0(X0_57) = iProver_top
% 2.50/1.01      | v2_pre_topc(X0_57) != iProver_top
% 2.50/1.01      | l1_pre_topc(X0_57) != iProver_top ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_3779,c_5978]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_9,plain,
% 2.50/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.50/1.01      | ~ m1_pre_topc(X3,X1)
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.50/1.01      | ~ v1_funct_1(X0)
% 2.50/1.01      | v2_struct_0(X1)
% 2.50/1.01      | v2_struct_0(X2)
% 2.50/1.01      | ~ v2_pre_topc(X1)
% 2.50/1.01      | ~ v2_pre_topc(X2)
% 2.50/1.01      | ~ l1_pre_topc(X1)
% 2.50/1.01      | ~ l1_pre_topc(X2)
% 2.50/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.50/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2934,plain,
% 2.50/1.01      ( ~ v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57))
% 2.50/1.01      | ~ m1_pre_topc(X2_57,X0_57)
% 2.50/1.01      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57))))
% 2.50/1.01      | ~ v1_funct_1(X0_56)
% 2.50/1.01      | v2_struct_0(X1_57)
% 2.50/1.01      | v2_struct_0(X0_57)
% 2.50/1.01      | ~ v2_pre_topc(X1_57)
% 2.50/1.01      | ~ v2_pre_topc(X0_57)
% 2.50/1.01      | ~ l1_pre_topc(X0_57)
% 2.50/1.01      | ~ l1_pre_topc(X1_57)
% 2.50/1.01      | k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_56,u1_struct_0(X2_57)) = k2_tmap_1(X0_57,X1_57,X0_56,X2_57) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3762,plain,
% 2.50/1.01      ( k2_partfun1(u1_struct_0(X0_57),u1_struct_0(X1_57),X0_56,u1_struct_0(X2_57)) = k2_tmap_1(X0_57,X1_57,X0_56,X2_57)
% 2.50/1.01      | v1_funct_2(X0_56,u1_struct_0(X0_57),u1_struct_0(X1_57)) != iProver_top
% 2.50/1.01      | m1_pre_topc(X2_57,X0_57) != iProver_top
% 2.50/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_57),u1_struct_0(X1_57)))) != iProver_top
% 2.50/1.01      | v1_funct_1(X0_56) != iProver_top
% 2.50/1.01      | v2_struct_0(X1_57) = iProver_top
% 2.50/1.01      | v2_struct_0(X0_57) = iProver_top
% 2.50/1.01      | v2_pre_topc(X1_57) != iProver_top
% 2.50/1.01      | v2_pre_topc(X0_57) != iProver_top
% 2.50/1.01      | l1_pre_topc(X0_57) != iProver_top
% 2.50/1.01      | l1_pre_topc(X1_57) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2934]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_4990,plain,
% 2.50/1.01      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0_57)) = k2_tmap_1(sK2,sK3,sK6,X0_57)
% 2.50/1.01      | v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 2.50/1.01      | m1_pre_topc(X0_57,sK2) != iProver_top
% 2.50/1.01      | v1_funct_1(sK6) != iProver_top
% 2.50/1.01      | v2_struct_0(sK2) = iProver_top
% 2.50/1.01      | v2_struct_0(sK3) = iProver_top
% 2.50/1.01      | v2_pre_topc(sK2) != iProver_top
% 2.50/1.01      | v2_pre_topc(sK3) != iProver_top
% 2.50/1.01      | l1_pre_topc(sK2) != iProver_top
% 2.50/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_3774,c_3762]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_35,negated_conjecture,
% 2.50/1.01      ( ~ v2_struct_0(sK2) ),
% 2.50/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_36,plain,
% 2.50/1.01      ( v2_struct_0(sK2) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_34,negated_conjecture,
% 2.50/1.01      ( v2_pre_topc(sK2) ),
% 2.50/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_37,plain,
% 2.50/1.01      ( v2_pre_topc(sK2) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_33,negated_conjecture,
% 2.50/1.01      ( l1_pre_topc(sK2) ),
% 2.50/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_38,plain,
% 2.50/1.01      ( l1_pre_topc(sK2) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_5243,plain,
% 2.50/1.01      ( m1_pre_topc(X0_57,sK2) != iProver_top
% 2.50/1.01      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0_57)) = k2_tmap_1(sK2,sK3,sK6,X0_57) ),
% 2.50/1.01      inference(global_propositional_subsumption,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_4990,c_36,c_37,c_38,c_39,c_40,c_41,c_46,c_47]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_5244,plain,
% 2.50/1.01      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0_57)) = k2_tmap_1(sK2,sK3,sK6,X0_57)
% 2.50/1.01      | m1_pre_topc(X0_57,sK2) != iProver_top ),
% 2.50/1.01      inference(renaming,[status(thm)],[c_5243]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_5251,plain,
% 2.50/1.01      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) = k2_tmap_1(sK2,sK3,sK6,sK4) ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_3779,c_5244]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_6015,plain,
% 2.50/1.01      ( k3_tmap_1(X0_57,sK3,sK2,sK4,sK6) = k2_tmap_1(sK2,sK3,sK6,sK4)
% 2.50/1.01      | m1_pre_topc(sK2,X0_57) != iProver_top
% 2.50/1.01      | v2_struct_0(X0_57) = iProver_top
% 2.50/1.01      | v2_pre_topc(X0_57) != iProver_top
% 2.50/1.01      | l1_pre_topc(X0_57) != iProver_top ),
% 2.50/1.01      inference(light_normalisation,[status(thm)],[c_5989,c_5251]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_6107,plain,
% 2.50/1.01      ( k3_tmap_1(sK2,sK3,sK2,sK4,sK6) = k2_tmap_1(sK2,sK3,sK6,sK4)
% 2.50/1.01      | v2_struct_0(sK2) = iProver_top
% 2.50/1.01      | v2_pre_topc(sK2) != iProver_top
% 2.50/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_3764,c_6015]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_6184,plain,
% 2.50/1.01      ( k3_tmap_1(sK2,sK3,sK2,sK4,sK6) = k2_tmap_1(sK2,sK3,sK6,sK4) ),
% 2.50/1.01      inference(global_propositional_subsumption,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_6107,c_36,c_37,c_38]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_8,plain,
% 2.50/1.01      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 2.50/1.01      | ~ v1_funct_2(X5,X2,X3)
% 2.50/1.01      | ~ v1_funct_2(X4,X0,X1)
% 2.50/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.50/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.50/1.01      | ~ v1_funct_1(X5)
% 2.50/1.01      | ~ v1_funct_1(X4)
% 2.50/1.01      | v1_xboole_0(X1)
% 2.50/1.01      | v1_xboole_0(X3)
% 2.50/1.01      | X4 = X5 ),
% 2.50/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_15,negated_conjecture,
% 2.50/1.01      ( r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK5),u1_struct_0(sK3),sK6,sK8) ),
% 2.50/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_497,plain,
% 2.50/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.50/1.01      | ~ v1_funct_2(X3,X4,X5)
% 2.50/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.50/1.01      | ~ v1_funct_1(X0)
% 2.50/1.01      | ~ v1_funct_1(X3)
% 2.50/1.01      | v1_xboole_0(X2)
% 2.50/1.01      | v1_xboole_0(X5)
% 2.50/1.01      | X3 = X0
% 2.50/1.01      | u1_struct_0(sK5) != X4
% 2.50/1.01      | u1_struct_0(sK2) != X1
% 2.50/1.01      | u1_struct_0(sK3) != X5
% 2.50/1.01      | u1_struct_0(sK3) != X2
% 2.50/1.01      | sK8 != X3
% 2.50/1.01      | sK6 != X0 ),
% 2.50/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_15]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_498,plain,
% 2.50/1.01      ( ~ v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3))
% 2.50/1.01      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
% 2.50/1.01      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 2.50/1.01      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 2.50/1.01      | ~ v1_funct_1(sK8)
% 2.50/1.01      | ~ v1_funct_1(sK6)
% 2.50/1.01      | v1_xboole_0(u1_struct_0(sK3))
% 2.50/1.01      | sK8 = sK6 ),
% 2.50/1.01      inference(unflattening,[status(thm)],[c_497]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_19,negated_conjecture,
% 2.50/1.01      ( v1_funct_1(sK8) ),
% 2.50/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_18,negated_conjecture,
% 2.50/1.01      ( v1_funct_2(sK8,u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 2.50/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_17,negated_conjecture,
% 2.50/1.01      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 2.50/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_500,plain,
% 2.50/1.01      ( v1_xboole_0(u1_struct_0(sK3)) | sK8 = sK6 ),
% 2.50/1.01      inference(global_propositional_subsumption,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_498,c_25,c_24,c_23,c_19,c_18,c_17]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2907,plain,
% 2.50/1.01      ( v1_xboole_0(u1_struct_0(sK3)) | sK8 = sK6 ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_500]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3788,plain,
% 2.50/1.01      ( sK8 = sK6 | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2907]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_6,plain,
% 2.50/1.01      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.50/1.01      | v2_struct_0(X0)
% 2.50/1.01      | ~ v2_pre_topc(X0)
% 2.50/1.01      | ~ l1_pre_topc(X0) ),
% 2.50/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2935,plain,
% 2.50/1.01      ( m1_subset_1(sK1(X0_57),k1_zfmisc_1(u1_struct_0(X0_57)))
% 2.50/1.01      | v2_struct_0(X0_57)
% 2.50/1.01      | ~ v2_pre_topc(X0_57)
% 2.50/1.01      | ~ l1_pre_topc(X0_57) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3761,plain,
% 2.50/1.01      ( m1_subset_1(sK1(X0_57),k1_zfmisc_1(u1_struct_0(X0_57))) = iProver_top
% 2.50/1.01      | v2_struct_0(X0_57) = iProver_top
% 2.50/1.01      | v2_pre_topc(X0_57) != iProver_top
% 2.50/1.01      | l1_pre_topc(X0_57) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2935]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_4,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.50/1.01      | ~ r2_hidden(X2,X0)
% 2.50/1.01      | ~ v1_xboole_0(X1) ),
% 2.50/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_1,plain,
% 2.50/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.50/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3,plain,
% 2.50/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.50/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_444,plain,
% 2.50/1.01      ( r2_hidden(sK0(X0,X1),X0)
% 2.50/1.01      | X2 != X0
% 2.50/1.01      | k1_xboole_0 != X1
% 2.50/1.01      | k1_xboole_0 = X2 ),
% 2.50/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_3]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_445,plain,
% 2.50/1.01      ( r2_hidden(sK0(X0,k1_xboole_0),X0) | k1_xboole_0 = X0 ),
% 2.50/1.01      inference(unflattening,[status(thm)],[c_444]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_474,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.50/1.01      | ~ v1_xboole_0(X1)
% 2.50/1.01      | X2 != X0
% 2.50/1.01      | sK0(X2,k1_xboole_0) != X3
% 2.50/1.01      | k1_xboole_0 = X2 ),
% 2.50/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_445]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_475,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.50/1.01      | ~ v1_xboole_0(X1)
% 2.50/1.01      | k1_xboole_0 = X0 ),
% 2.50/1.01      inference(unflattening,[status(thm)],[c_474]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2908,plain,
% 2.50/1.01      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
% 2.50/1.01      | ~ v1_xboole_0(X1_56)
% 2.50/1.01      | k1_xboole_0 = X0_56 ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_475]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3787,plain,
% 2.50/1.01      ( k1_xboole_0 = X0_56
% 2.50/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) != iProver_top
% 2.50/1.01      | v1_xboole_0(X1_56) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2908]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_4781,plain,
% 2.50/1.01      ( sK1(X0_57) = k1_xboole_0
% 2.50/1.01      | v2_struct_0(X0_57) = iProver_top
% 2.50/1.01      | v2_pre_topc(X0_57) != iProver_top
% 2.50/1.01      | l1_pre_topc(X0_57) != iProver_top
% 2.50/1.01      | v1_xboole_0(u1_struct_0(X0_57)) != iProver_top ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_3761,c_3787]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_4975,plain,
% 2.50/1.01      ( sK1(sK3) = k1_xboole_0
% 2.50/1.01      | sK8 = sK6
% 2.50/1.01      | v2_struct_0(sK3) = iProver_top
% 2.50/1.01      | v2_pre_topc(sK3) != iProver_top
% 2.50/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_3788,c_4781]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_4976,plain,
% 2.50/1.01      ( v2_struct_0(sK3)
% 2.50/1.01      | ~ v2_pre_topc(sK3)
% 2.50/1.01      | ~ l1_pre_topc(sK3)
% 2.50/1.01      | sK1(sK3) = k1_xboole_0
% 2.50/1.01      | sK8 = sK6 ),
% 2.50/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_4975]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_5498,plain,
% 2.50/1.01      ( sK8 = sK6 | sK1(sK3) = k1_xboole_0 ),
% 2.50/1.01      inference(global_propositional_subsumption,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_4975,c_32,c_31,c_30,c_4976]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_5499,plain,
% 2.50/1.01      ( sK1(sK3) = k1_xboole_0 | sK8 = sK6 ),
% 2.50/1.01      inference(renaming,[status(thm)],[c_5498]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_5,plain,
% 2.50/1.01      ( v2_struct_0(X0)
% 2.50/1.01      | ~ v2_pre_topc(X0)
% 2.50/1.01      | ~ l1_pre_topc(X0)
% 2.50/1.01      | ~ v1_xboole_0(sK1(X0)) ),
% 2.50/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2936,plain,
% 2.50/1.01      ( v2_struct_0(X0_57)
% 2.50/1.01      | ~ v2_pre_topc(X0_57)
% 2.50/1.01      | ~ l1_pre_topc(X0_57)
% 2.50/1.01      | ~ v1_xboole_0(sK1(X0_57)) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3760,plain,
% 2.50/1.01      ( v2_struct_0(X0_57) = iProver_top
% 2.50/1.01      | v2_pre_topc(X0_57) != iProver_top
% 2.50/1.01      | l1_pre_topc(X0_57) != iProver_top
% 2.50/1.01      | v1_xboole_0(sK1(X0_57)) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2936]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_5503,plain,
% 2.50/1.01      ( sK8 = sK6
% 2.50/1.01      | v2_struct_0(sK3) = iProver_top
% 2.50/1.01      | v2_pre_topc(sK3) != iProver_top
% 2.50/1.01      | l1_pre_topc(sK3) != iProver_top
% 2.50/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.50/1.01      inference(superposition,[status(thm)],[c_5499,c_3760]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2,plain,
% 2.50/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.50/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_86,plain,
% 2.50/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_5527,plain,
% 2.50/1.01      ( sK8 = sK6 ),
% 2.50/1.01      inference(global_propositional_subsumption,
% 2.50/1.01                [status(thm)],
% 2.50/1.01                [c_5503,c_39,c_40,c_41,c_86]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_14,negated_conjecture,
% 2.50/1.01      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)
% 2.50/1.01      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) ),
% 2.50/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2929,negated_conjecture,
% 2.50/1.01      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)
% 2.50/1.01      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3767,plain,
% 2.50/1.01      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) = iProver_top
% 2.50/1.01      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2929]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_16,negated_conjecture,
% 2.50/1.01      ( sK2 = sK5 ),
% 2.50/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2928,negated_conjecture,
% 2.50/1.01      ( sK2 = sK5 ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3863,plain,
% 2.50/1.01      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK4,sK8),sK7) = iProver_top
% 2.50/1.01      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
% 2.50/1.01      inference(light_normalisation,[status(thm)],[c_3767,c_2928]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_5535,plain,
% 2.50/1.01      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK4,sK6),sK7) = iProver_top
% 2.50/1.01      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
% 2.50/1.01      inference(demodulation,[status(thm)],[c_5527,c_3863]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_6187,plain,
% 2.50/1.01      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) = iProver_top ),
% 2.50/1.01      inference(demodulation,[status(thm)],[c_6184,c_5535]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_13,negated_conjecture,
% 2.50/1.01      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)
% 2.50/1.01      | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) ),
% 2.50/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_2930,negated_conjecture,
% 2.50/1.01      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7)
% 2.50/1.01      | ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) ),
% 2.50/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3766,plain,
% 2.50/1.01      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK4,sK8),sK7) != iProver_top
% 2.50/1.01      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
% 2.50/1.01      inference(predicate_to_equality,[status(thm)],[c_2930]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_3868,plain,
% 2.50/1.01      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK4,sK8),sK7) != iProver_top
% 2.50/1.01      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
% 2.50/1.01      inference(light_normalisation,[status(thm)],[c_3766,c_2928]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_5534,plain,
% 2.50/1.01      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK2,sK4,sK6),sK7) != iProver_top
% 2.50/1.01      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
% 2.50/1.01      inference(demodulation,[status(thm)],[c_5527,c_3868]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_6188,plain,
% 2.50/1.01      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k2_tmap_1(sK2,sK3,sK6,sK4),sK7) != iProver_top ),
% 2.50/1.01      inference(demodulation,[status(thm)],[c_6184,c_5534]) ).
% 2.50/1.01  
% 2.50/1.01  cnf(c_6192,plain,
% 2.50/1.01      ( $false ),
% 2.50/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_6187,c_6188]) ).
% 2.50/1.01  
% 2.50/1.01  
% 2.50/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.50/1.01  
% 2.50/1.01  ------                               Statistics
% 2.50/1.01  
% 2.50/1.01  ------ General
% 2.50/1.01  
% 2.50/1.01  abstr_ref_over_cycles:                  0
% 2.50/1.01  abstr_ref_under_cycles:                 0
% 2.50/1.01  gc_basic_clause_elim:                   0
% 2.50/1.01  forced_gc_time:                         0
% 2.50/1.01  parsing_time:                           0.01
% 2.50/1.01  unif_index_cands_time:                  0.
% 2.50/1.01  unif_index_add_time:                    0.
% 2.50/1.01  orderings_time:                         0.
% 2.50/1.01  out_proof_time:                         0.01
% 2.50/1.01  total_time:                             0.174
% 2.50/1.01  num_of_symbols:                         66
% 2.50/1.01  num_of_terms:                           3233
% 2.50/1.01  
% 2.50/1.01  ------ Preprocessing
% 2.50/1.01  
% 2.50/1.01  num_of_splits:                          0
% 2.50/1.01  num_of_split_atoms:                     0
% 2.50/1.01  num_of_reused_defs:                     0
% 2.50/1.01  num_eq_ax_congr_red:                    10
% 2.50/1.01  num_of_sem_filtered_clauses:            1
% 2.50/1.01  num_of_subtypes:                        4
% 2.50/1.01  monotx_restored_types:                  0
% 2.50/1.01  sat_num_of_epr_types:                   0
% 2.50/1.01  sat_num_of_non_cyclic_types:            0
% 2.50/1.01  sat_guarded_non_collapsed_types:        1
% 2.50/1.01  num_pure_diseq_elim:                    0
% 2.50/1.01  simp_replaced_by:                       0
% 2.50/1.01  res_preprocessed:                       174
% 2.50/1.01  prep_upred:                             0
% 2.50/1.01  prep_unflattend:                        71
% 2.50/1.01  smt_new_axioms:                         0
% 2.50/1.01  pred_elim_cands:                        9
% 2.50/1.01  pred_elim:                              3
% 2.50/1.01  pred_elim_cl:                           5
% 2.50/1.01  pred_elim_cycles:                       11
% 2.50/1.01  merged_defs:                            8
% 2.50/1.01  merged_defs_ncl:                        0
% 2.50/1.01  bin_hyper_res:                          8
% 2.50/1.01  prep_cycles:                            4
% 2.50/1.01  pred_elim_time:                         0.064
% 2.50/1.01  splitting_time:                         0.
% 2.50/1.01  sem_filter_time:                        0.
% 2.50/1.01  monotx_time:                            0.
% 2.50/1.01  subtype_inf_time:                       0.
% 2.50/1.01  
% 2.50/1.01  ------ Problem properties
% 2.50/1.01  
% 2.50/1.01  clauses:                                31
% 2.50/1.01  conjectures:                            22
% 2.50/1.01  epr:                                    17
% 2.50/1.01  horn:                                   26
% 2.50/1.01  ground:                                 24
% 2.50/1.01  unary:                                  21
% 2.50/1.01  binary:                                 4
% 2.50/1.01  lits:                                   69
% 2.50/1.01  lits_eq:                                5
% 2.50/1.01  fd_pure:                                0
% 2.50/1.01  fd_pseudo:                              0
% 2.50/1.01  fd_cond:                                1
% 2.50/1.01  fd_pseudo_cond:                         0
% 2.50/1.01  ac_symbols:                             0
% 2.50/1.01  
% 2.50/1.01  ------ Propositional Solver
% 2.50/1.01  
% 2.50/1.01  prop_solver_calls:                      27
% 2.50/1.01  prop_fast_solver_calls:                 1976
% 2.50/1.01  smt_solver_calls:                       0
% 2.50/1.01  smt_fast_solver_calls:                  0
% 2.50/1.01  prop_num_of_clauses:                    1162
% 2.50/1.01  prop_preprocess_simplified:             5210
% 2.50/1.01  prop_fo_subsumed:                       92
% 2.50/1.01  prop_solver_time:                       0.
% 2.50/1.01  smt_solver_time:                        0.
% 2.50/1.01  smt_fast_solver_time:                   0.
% 2.50/1.01  prop_fast_solver_time:                  0.
% 2.50/1.01  prop_unsat_core_time:                   0.
% 2.50/1.01  
% 2.50/1.01  ------ QBF
% 2.50/1.01  
% 2.50/1.01  qbf_q_res:                              0
% 2.50/1.01  qbf_num_tautologies:                    0
% 2.50/1.01  qbf_prep_cycles:                        0
% 2.50/1.01  
% 2.50/1.01  ------ BMC1
% 2.50/1.01  
% 2.50/1.01  bmc1_current_bound:                     -1
% 2.50/1.01  bmc1_last_solved_bound:                 -1
% 2.50/1.01  bmc1_unsat_core_size:                   -1
% 2.50/1.01  bmc1_unsat_core_parents_size:           -1
% 2.50/1.01  bmc1_merge_next_fun:                    0
% 2.50/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.50/1.01  
% 2.50/1.01  ------ Instantiation
% 2.50/1.01  
% 2.50/1.01  inst_num_of_clauses:                    345
% 2.50/1.01  inst_num_in_passive:                    40
% 2.50/1.01  inst_num_in_active:                     265
% 2.50/1.01  inst_num_in_unprocessed:                41
% 2.50/1.01  inst_num_of_loops:                      280
% 2.50/1.01  inst_num_of_learning_restarts:          0
% 2.50/1.01  inst_num_moves_active_passive:          12
% 2.50/1.01  inst_lit_activity:                      0
% 2.50/1.01  inst_lit_activity_moves:                0
% 2.50/1.01  inst_num_tautologies:                   0
% 2.50/1.01  inst_num_prop_implied:                  0
% 2.50/1.01  inst_num_existing_simplified:           0
% 2.50/1.01  inst_num_eq_res_simplified:             0
% 2.50/1.01  inst_num_child_elim:                    0
% 2.50/1.01  inst_num_of_dismatching_blockings:      67
% 2.50/1.01  inst_num_of_non_proper_insts:           373
% 2.50/1.01  inst_num_of_duplicates:                 0
% 2.50/1.01  inst_inst_num_from_inst_to_res:         0
% 2.50/1.01  inst_dismatching_checking_time:         0.
% 2.50/1.01  
% 2.50/1.01  ------ Resolution
% 2.50/1.01  
% 2.50/1.01  res_num_of_clauses:                     0
% 2.50/1.01  res_num_in_passive:                     0
% 2.50/1.01  res_num_in_active:                      0
% 2.50/1.01  res_num_of_loops:                       178
% 2.50/1.01  res_forward_subset_subsumed:            79
% 2.50/1.01  res_backward_subset_subsumed:           4
% 2.50/1.01  res_forward_subsumed:                   0
% 2.50/1.01  res_backward_subsumed:                  0
% 2.50/1.01  res_forward_subsumption_resolution:     7
% 2.50/1.01  res_backward_subsumption_resolution:    0
% 2.50/1.01  res_clause_to_clause_subsumption:       215
% 2.50/1.01  res_orphan_elimination:                 0
% 2.50/1.01  res_tautology_del:                      82
% 2.50/1.01  res_num_eq_res_simplified:              0
% 2.50/1.01  res_num_sel_changes:                    0
% 2.50/1.01  res_moves_from_active_to_pass:          0
% 2.50/1.01  
% 2.50/1.01  ------ Superposition
% 2.50/1.01  
% 2.50/1.01  sup_time_total:                         0.
% 2.50/1.01  sup_time_generating:                    0.
% 2.50/1.01  sup_time_sim_full:                      0.
% 2.50/1.01  sup_time_sim_immed:                     0.
% 2.50/1.01  
% 2.50/1.01  sup_num_of_clauses:                     45
% 2.50/1.01  sup_num_in_active:                      43
% 2.50/1.01  sup_num_in_passive:                     2
% 2.50/1.01  sup_num_of_loops:                       55
% 2.50/1.01  sup_fw_superposition:                   33
% 2.50/1.01  sup_bw_superposition:                   3
% 2.50/1.01  sup_immediate_simplified:               7
% 2.50/1.01  sup_given_eliminated:                   0
% 2.50/1.01  comparisons_done:                       0
% 2.50/1.01  comparisons_avoided:                    3
% 2.50/1.01  
% 2.50/1.01  ------ Simplifications
% 2.50/1.01  
% 2.50/1.01  
% 2.50/1.01  sim_fw_subset_subsumed:                 4
% 2.50/1.01  sim_bw_subset_subsumed:                 2
% 2.50/1.01  sim_fw_subsumed:                        0
% 2.50/1.01  sim_bw_subsumed:                        0
% 2.50/1.01  sim_fw_subsumption_res:                 2
% 2.50/1.01  sim_bw_subsumption_res:                 0
% 2.50/1.01  sim_tautology_del:                      3
% 2.50/1.01  sim_eq_tautology_del:                   0
% 2.50/1.01  sim_eq_res_simp:                        0
% 2.50/1.01  sim_fw_demodulated:                     0
% 2.50/1.01  sim_bw_demodulated:                     11
% 2.50/1.01  sim_light_normalised:                   9
% 2.50/1.01  sim_joinable_taut:                      0
% 2.50/1.01  sim_joinable_simp:                      0
% 2.50/1.01  sim_ac_normalised:                      0
% 2.50/1.01  sim_smt_subsumption:                    0
% 2.50/1.01  
%------------------------------------------------------------------------------
