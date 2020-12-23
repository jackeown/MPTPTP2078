%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:01 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  190 (3319 expanded)
%              Number of clauses        :  114 ( 667 expanded)
%              Number of leaves         :   19 (1302 expanded)
%              Depth                    :   20
%              Number of atoms          :  983 (63455 expanded)
%              Number of equality atoms :  283 (4460 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,
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

fof(f55,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f47,f54,f53,f52,f51,f50,f49,f48])).

fof(f99,plain,(
    r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f98,plain,(
    sK1 = sK4 ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f95,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,(
    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f97,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f104,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f65])).

fof(f88,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

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

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f100,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f101,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1785,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( sK1 = sK4 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1856,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1785,c_26])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_1791,plain,
    ( X0 = X1
    | r1_funct_2(X2,X3,X4,X5,X0,X1) != iProver_top
    | v1_funct_2(X1,X4,X5) != iProver_top
    | v1_funct_2(X0,X2,X3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4715,plain,
    ( sK7 = sK5
    | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1856,c_1791])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_56,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_57,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_58,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_62,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1783,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1846,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1783,c_26])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1784,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1853,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1784,c_26])).

cnf(c_5527,plain,
    ( sK7 = sK5
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4715,c_56,c_57,c_58,c_62,c_1846,c_1853])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1801,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1804,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_256,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_257,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_256])).

cnf(c_353,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_257])).

cnf(c_1765,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_9385,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1804,c_1765])).

cnf(c_9740,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1801,c_9385])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1800,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1802,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5261,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1800,c_1802])).

cnf(c_9792,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9740,c_5261])).

cnf(c_11165,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | sK7 = sK5 ),
    inference(superposition,[status(thm)],[c_5527,c_9792])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1798,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3570,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1853,c_1798])).

cnf(c_5264,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3570,c_1802])).

cnf(c_9796,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9740,c_5264])).

cnf(c_11174,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7
    | sK7 = sK5
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11165,c_9796])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_11353,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7
    | sK7 = sK5
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11174,c_7])).

cnf(c_4234,plain,
    ( r1_tarski(k1_xboole_0,sK7) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4237,plain,
    ( r1_tarski(k1_xboole_0,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4234])).

cnf(c_11182,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7
    | sK7 = sK5
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_11165,c_5264])).

cnf(c_11299,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7
    | sK7 = sK5
    | r1_tarski(k1_xboole_0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11182,c_7])).

cnf(c_15258,plain,
    ( sK7 = sK5
    | k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11353,c_4237,c_11299])).

cnf(c_15259,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7
    | sK7 = sK5 ),
    inference(renaming,[status(thm)],[c_15258])).

cnf(c_1778,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3569,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_1798])).

cnf(c_5263,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3569,c_1802])).

cnf(c_9795,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9740,c_5263])).

cnf(c_11175,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5
    | sK7 = sK5
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11165,c_9795])).

cnf(c_11346,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5
    | sK7 = sK5
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11175,c_7])).

cnf(c_4406,plain,
    ( r1_tarski(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4409,plain,
    ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4406])).

cnf(c_11183,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5
    | sK7 = sK5
    | r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_11165,c_5263])).

cnf(c_11292,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5
    | sK7 = sK5
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11183,c_7])).

cnf(c_14963,plain,
    ( sK7 = sK5
    | k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11346,c_4409,c_11292])).

cnf(c_14964,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5
    | sK7 = sK5 ),
    inference(renaming,[status(thm)],[c_14963])).

cnf(c_15277,plain,
    ( sK7 = sK5 ),
    inference(superposition,[status(thm)],[c_15259,c_14964])).

cnf(c_36,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1775,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1831,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1775,c_26])).

cnf(c_38,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1773,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f77])).

cnf(c_1789,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X4) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_pre_topc(X0,X4) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X4) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1788,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X0,X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2018,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_pre_topc(X0,X4) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X4) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X4) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1789,c_1788])).

cnf(c_7067,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
    | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1853,c_2018])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_49,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_50,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_51,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_7815,plain,
    ( v2_pre_topc(X1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7067,c_49,c_50,c_51,c_62,c_1846])).

cnf(c_7816,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7815])).

cnf(c_7827,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k3_tmap_1(X0,sK2,sK1,sK3,sK7)
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_7816])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_1790,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3691,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0)
    | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1853,c_1790])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_46,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_47,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_48,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_5818,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3691,c_46,c_47,c_48,c_49,c_50,c_51,c_62,c_1846])).

cnf(c_5819,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0)
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5818])).

cnf(c_5826,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
    inference(superposition,[status(thm)],[c_1773,c_5819])).

cnf(c_7845,plain,
    ( k3_tmap_1(X0,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7827,c_5826])).

cnf(c_8911,plain,
    ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1831,c_7845])).

cnf(c_8914,plain,
    ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8911,c_46,c_47,c_48])).

cnf(c_24,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1786,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1919,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1786,c_26])).

cnf(c_8917,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8914,c_1919])).

cnf(c_15952,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15277,c_8917])).

cnf(c_23,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1787,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1924,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1787,c_26])).

cnf(c_8918,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8914,c_1924])).

cnf(c_15953,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15277,c_8918])).

cnf(c_15975,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15952,c_15953])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.86/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.86/0.99  
% 3.86/0.99  ------  iProver source info
% 3.86/0.99  
% 3.86/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.86/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.86/0.99  git: non_committed_changes: false
% 3.86/0.99  git: last_make_outside_of_git: false
% 3.86/0.99  
% 3.86/0.99  ------ 
% 3.86/0.99  ------ Parsing...
% 3.86/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.86/0.99  ------ Proving...
% 3.86/0.99  ------ Problem Properties 
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  clauses                                 45
% 3.86/0.99  conjectures                             23
% 3.86/0.99  EPR                                     20
% 3.86/0.99  Horn                                    38
% 3.86/0.99  unary                                   25
% 3.86/0.99  binary                                  8
% 3.86/0.99  lits                                    110
% 3.86/0.99  lits eq                                 10
% 3.86/0.99  fd_pure                                 0
% 3.86/0.99  fd_pseudo                               0
% 3.86/0.99  fd_cond                                 1
% 3.86/0.99  fd_pseudo_cond                          2
% 3.86/0.99  AC symbols                              0
% 3.86/0.99  
% 3.86/0.99  ------ Input Options Time Limit: Unbounded
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  ------ 
% 3.86/0.99  Current options:
% 3.86/0.99  ------ 
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  ------ Proving...
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  % SZS status Theorem for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99   Resolution empty clause
% 3.86/0.99  
% 3.86/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  fof(f15,conjecture,(
% 3.86/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f16,negated_conjecture,(
% 3.86/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 3.86/0.99    inference(negated_conjecture,[],[f15])).
% 3.86/0.99  
% 3.86/0.99  fof(f33,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f16])).
% 3.86/0.99  
% 3.86/0.99  fof(f34,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.86/0.99    inference(flattening,[],[f33])).
% 3.86/0.99  
% 3.86/0.99  fof(f46,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.86/0.99    inference(nnf_transformation,[],[f34])).
% 3.86/0.99  
% 3.86/0.99  fof(f47,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.86/0.99    inference(flattening,[],[f46])).
% 3.86/0.99  
% 3.86/0.99  fof(f54,plain,(
% 3.86/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK7),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK7),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK7) & X0 = X3 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f53,plain,(
% 3.86/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK6) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK6)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK6) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK6)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f52,plain,(
% 3.86/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK5,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK5,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK5,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f51,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK4),u1_struct_0(X1),X4,X6) & sK4 = X0 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f50,plain,(
% 3.86/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK3),X5) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X6),X5)) & (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK3),X5) | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f49,plain,(
% 3.86/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X3),u1_struct_0(sK2),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f48,plain,(
% 3.86/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK1,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK1,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK1),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK1 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f55,plain,(
% 3.86/0.99    (((((((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)) & (r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)) & r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) & sK1 = sK4 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f47,f54,f53,f52,f51,f50,f49,f48])).
% 3.86/0.99  
% 3.86/0.99  fof(f99,plain,(
% 3.86/0.99    r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f98,plain,(
% 3.86/0.99    sK1 = sK4),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f11,axiom,(
% 3.86/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f25,plain,(
% 3.86/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.86/0.99    inference(ennf_transformation,[],[f11])).
% 3.86/0.99  
% 3.86/0.99  fof(f26,plain,(
% 3.86/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.86/0.99    inference(flattening,[],[f25])).
% 3.86/0.99  
% 3.86/0.99  fof(f45,plain,(
% 3.86/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.86/0.99    inference(nnf_transformation,[],[f26])).
% 3.86/0.99  
% 3.86/0.99  fof(f74,plain,(
% 3.86/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f45])).
% 3.86/0.99  
% 3.86/0.99  fof(f89,plain,(
% 3.86/0.99    v1_funct_1(sK5)),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f90,plain,(
% 3.86/0.99    v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f91,plain,(
% 3.86/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f95,plain,(
% 3.86/0.99    v1_funct_1(sK7)),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f96,plain,(
% 3.86/0.99    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2))),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f97,plain,(
% 3.86/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f2,axiom,(
% 3.86/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f39,plain,(
% 3.86/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.99    inference(nnf_transformation,[],[f2])).
% 3.86/0.99  
% 3.86/0.99  fof(f40,plain,(
% 3.86/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.99    inference(flattening,[],[f39])).
% 3.86/0.99  
% 3.86/0.99  fof(f60,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.86/0.99    inference(cnf_transformation,[],[f40])).
% 3.86/0.99  
% 3.86/0.99  fof(f102,plain,(
% 3.86/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.86/0.99    inference(equality_resolution,[],[f60])).
% 3.86/0.99  
% 3.86/0.99  fof(f1,axiom,(
% 3.86/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f18,plain,(
% 3.86/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f1])).
% 3.86/0.99  
% 3.86/0.99  fof(f35,plain,(
% 3.86/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.86/0.99    inference(nnf_transformation,[],[f18])).
% 3.86/0.99  
% 3.86/0.99  fof(f36,plain,(
% 3.86/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.86/0.99    inference(rectify,[],[f35])).
% 3.86/0.99  
% 3.86/0.99  fof(f37,plain,(
% 3.86/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f38,plain,(
% 3.86/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 3.86/0.99  
% 3.86/0.99  fof(f57,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f38])).
% 3.86/0.99  
% 3.86/0.99  fof(f6,axiom,(
% 3.86/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f19,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.86/0.99    inference(ennf_transformation,[],[f6])).
% 3.86/0.99  
% 3.86/0.99  fof(f68,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f19])).
% 3.86/0.99  
% 3.86/0.99  fof(f5,axiom,(
% 3.86/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f43,plain,(
% 3.86/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.86/0.99    inference(nnf_transformation,[],[f5])).
% 3.86/0.99  
% 3.86/0.99  fof(f67,plain,(
% 3.86/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f43])).
% 3.86/0.99  
% 3.86/0.99  fof(f3,axiom,(
% 3.86/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f62,plain,(
% 3.86/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f3])).
% 3.86/0.99  
% 3.86/0.99  fof(f61,plain,(
% 3.86/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f40])).
% 3.86/0.99  
% 3.86/0.99  fof(f66,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f43])).
% 3.86/0.99  
% 3.86/0.99  fof(f4,axiom,(
% 3.86/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f41,plain,(
% 3.86/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.86/0.99    inference(nnf_transformation,[],[f4])).
% 3.86/0.99  
% 3.86/0.99  fof(f42,plain,(
% 3.86/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.86/0.99    inference(flattening,[],[f41])).
% 3.86/0.99  
% 3.86/0.99  fof(f65,plain,(
% 3.86/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.86/0.99    inference(cnf_transformation,[],[f42])).
% 3.86/0.99  
% 3.86/0.99  fof(f104,plain,(
% 3.86/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.86/0.99    inference(equality_resolution,[],[f65])).
% 3.86/0.99  
% 3.86/0.99  fof(f88,plain,(
% 3.86/0.99    m1_pre_topc(sK4,sK1)),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f86,plain,(
% 3.86/0.99    m1_pre_topc(sK3,sK1)),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f13,axiom,(
% 3.86/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f29,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f13])).
% 3.86/0.99  
% 3.86/0.99  fof(f30,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.86/0.99    inference(flattening,[],[f29])).
% 3.86/0.99  
% 3.86/0.99  fof(f77,plain,(
% 3.86/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f30])).
% 3.86/0.99  
% 3.86/0.99  fof(f14,axiom,(
% 3.86/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f31,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f14])).
% 3.86/0.99  
% 3.86/0.99  fof(f32,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.86/0.99    inference(flattening,[],[f31])).
% 3.86/0.99  
% 3.86/0.99  fof(f78,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f32])).
% 3.86/0.99  
% 3.86/0.99  fof(f82,plain,(
% 3.86/0.99    ~v2_struct_0(sK2)),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f83,plain,(
% 3.86/0.99    v2_pre_topc(sK2)),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f84,plain,(
% 3.86/0.99    l1_pre_topc(sK2)),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f12,axiom,(
% 3.86/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f27,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f12])).
% 3.86/0.99  
% 3.86/0.99  fof(f28,plain,(
% 3.86/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.86/0.99    inference(flattening,[],[f27])).
% 3.86/0.99  
% 3.86/0.99  fof(f76,plain,(
% 3.86/0.99    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f28])).
% 3.86/0.99  
% 3.86/0.99  fof(f79,plain,(
% 3.86/0.99    ~v2_struct_0(sK1)),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f80,plain,(
% 3.86/0.99    v2_pre_topc(sK1)),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f81,plain,(
% 3.86/0.99    l1_pre_topc(sK1)),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f100,plain,(
% 3.86/0.99    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f101,plain,(
% 3.86/0.99    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)),
% 3.86/0.99    inference(cnf_transformation,[],[f55])).
% 3.86/0.99  
% 3.86/0.99  cnf(c_25,negated_conjecture,
% 3.86/0.99      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) ),
% 3.86/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1785,plain,
% 3.86/0.99      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_26,negated_conjecture,
% 3.86/0.99      ( sK1 = sK4 ),
% 3.86/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1856,plain,
% 3.86/0.99      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK2),sK5,sK7) = iProver_top ),
% 3.86/0.99      inference(light_normalisation,[status(thm)],[c_1785,c_26]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_19,plain,
% 3.86/0.99      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 3.86/0.99      | ~ v1_funct_2(X5,X2,X3)
% 3.86/0.99      | ~ v1_funct_2(X4,X0,X1)
% 3.86/0.99      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.86/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.86/0.99      | ~ v1_funct_1(X5)
% 3.86/0.99      | ~ v1_funct_1(X4)
% 3.86/0.99      | v1_xboole_0(X1)
% 3.86/0.99      | v1_xboole_0(X3)
% 3.86/0.99      | X4 = X5 ),
% 3.86/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1791,plain,
% 3.86/0.99      ( X0 = X1
% 3.86/0.99      | r1_funct_2(X2,X3,X4,X5,X0,X1) != iProver_top
% 3.86/0.99      | v1_funct_2(X1,X4,X5) != iProver_top
% 3.86/0.99      | v1_funct_2(X0,X2,X3) != iProver_top
% 3.86/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.86/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.86/0.99      | v1_funct_1(X1) != iProver_top
% 3.86/0.99      | v1_funct_1(X0) != iProver_top
% 3.86/0.99      | v1_xboole_0(X3) = iProver_top
% 3.86/0.99      | v1_xboole_0(X5) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4715,plain,
% 3.86/0.99      ( sK7 = sK5
% 3.86/0.99      | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 3.86/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 3.86/0.99      | v1_funct_1(sK7) != iProver_top
% 3.86/0.99      | v1_funct_1(sK5) != iProver_top
% 3.86/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1856,c_1791]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_35,negated_conjecture,
% 3.86/0.99      ( v1_funct_1(sK5) ),
% 3.86/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_56,plain,
% 3.86/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_34,negated_conjecture,
% 3.86/0.99      ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_57,plain,
% 3.86/0.99      ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_33,negated_conjecture,
% 3.86/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 3.86/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_58,plain,
% 3.86/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_29,negated_conjecture,
% 3.86/0.99      ( v1_funct_1(sK7) ),
% 3.86/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_62,plain,
% 3.86/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_28,negated_conjecture,
% 3.86/0.99      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1783,plain,
% 3.86/0.99      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1846,plain,
% 3.86/0.99      ( v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 3.86/0.99      inference(light_normalisation,[status(thm)],[c_1783,c_26]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_27,negated_conjecture,
% 3.86/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 3.86/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1784,plain,
% 3.86/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1853,plain,
% 3.86/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 3.86/0.99      inference(light_normalisation,[status(thm)],[c_1784,c_26]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5527,plain,
% 3.86/0.99      ( sK7 = sK5 | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_4715,c_56,c_57,c_58,c_62,c_1846,c_1853]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f102]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1801,plain,
% 3.86/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1,plain,
% 3.86/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1804,plain,
% 3.86/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.86/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_12,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.86/0.99      | ~ r2_hidden(X2,X0)
% 3.86/0.99      | ~ v1_xboole_0(X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_10,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_256,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.86/0.99      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_257,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_256]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_353,plain,
% 3.86/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.86/0.99      inference(bin_hyper_res,[status(thm)],[c_12,c_257]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1765,plain,
% 3.86/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.86/0.99      | r1_tarski(X1,X2) != iProver_top
% 3.86/0.99      | v1_xboole_0(X2) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_353]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9385,plain,
% 3.86/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.86/0.99      | r1_tarski(X0,X2) = iProver_top
% 3.86/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1804,c_1765]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9740,plain,
% 3.86/0.99      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1801,c_9385]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6,plain,
% 3.86/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1800,plain,
% 3.86/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.86/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1802,plain,
% 3.86/0.99      ( X0 = X1
% 3.86/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.86/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5261,plain,
% 3.86/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1800,c_1802]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9792,plain,
% 3.86/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_9740,c_5261]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11165,plain,
% 3.86/0.99      ( u1_struct_0(sK2) = k1_xboole_0 | sK7 = sK5 ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_5527,c_9792]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1798,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.86/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3570,plain,
% 3.86/0.99      ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1853,c_1798]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5264,plain,
% 3.86/0.99      ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7
% 3.86/0.99      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),sK7) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3570,c_1802]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9796,plain,
% 3.86/0.99      ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7
% 3.86/0.99      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_9740,c_5264]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11174,plain,
% 3.86/0.99      ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7
% 3.86/0.99      | sK7 = sK5
% 3.86/0.99      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_11165,c_9796]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7,plain,
% 3.86/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.86/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11353,plain,
% 3.86/0.99      ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7
% 3.86/0.99      | sK7 = sK5
% 3.86/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.86/0.99      inference(demodulation,[status(thm)],[c_11174,c_7]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4234,plain,
% 3.86/0.99      ( r1_tarski(k1_xboole_0,sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4237,plain,
% 3.86/0.99      ( r1_tarski(k1_xboole_0,sK7) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_4234]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11182,plain,
% 3.86/0.99      ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7
% 3.86/0.99      | sK7 = sK5
% 3.86/0.99      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0),sK7) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_11165,c_5264]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11299,plain,
% 3.86/0.99      ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7
% 3.86/0.99      | sK7 = sK5
% 3.86/0.99      | r1_tarski(k1_xboole_0,sK7) != iProver_top ),
% 3.86/0.99      inference(demodulation,[status(thm)],[c_11182,c_7]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_15258,plain,
% 3.86/0.99      ( sK7 = sK5 | k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7 ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_11353,c_4237,c_11299]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_15259,plain,
% 3.86/0.99      ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK7 | sK7 = sK5 ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_15258]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1778,plain,
% 3.86/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3569,plain,
% 3.86/0.99      ( r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1778,c_1798]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5263,plain,
% 3.86/0.99      ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5
% 3.86/0.99      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),sK5) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_3569,c_1802]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9795,plain,
% 3.86/0.99      ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5
% 3.86/0.99      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_9740,c_5263]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11175,plain,
% 3.86/0.99      ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5
% 3.86/0.99      | sK7 = sK5
% 3.86/0.99      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_11165,c_9795]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11346,plain,
% 3.86/0.99      ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5
% 3.86/0.99      | sK7 = sK5
% 3.86/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.86/0.99      inference(demodulation,[status(thm)],[c_11175,c_7]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4406,plain,
% 3.86/0.99      ( r1_tarski(k1_xboole_0,sK5) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4409,plain,
% 3.86/0.99      ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_4406]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11183,plain,
% 3.86/0.99      ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5
% 3.86/0.99      | sK7 = sK5
% 3.86/0.99      | r1_tarski(k2_zfmisc_1(u1_struct_0(sK1),k1_xboole_0),sK5) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_11165,c_5263]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11292,plain,
% 3.86/0.99      ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5
% 3.86/0.99      | sK7 = sK5
% 3.86/0.99      | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 3.86/0.99      inference(demodulation,[status(thm)],[c_11183,c_7]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_14963,plain,
% 3.86/0.99      ( sK7 = sK5 | k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5 ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_11346,c_4409,c_11292]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_14964,plain,
% 3.86/0.99      ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK5 | sK7 = sK5 ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_14963]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_15277,plain,
% 3.86/0.99      ( sK7 = sK5 ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_15259,c_14964]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_36,negated_conjecture,
% 3.86/0.99      ( m1_pre_topc(sK4,sK1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1775,plain,
% 3.86/0.99      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1831,plain,
% 3.86/0.99      ( m1_pre_topc(sK1,sK1) = iProver_top ),
% 3.86/0.99      inference(light_normalisation,[status(thm)],[c_1775,c_26]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_38,negated_conjecture,
% 3.86/0.99      ( m1_pre_topc(sK3,sK1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1773,plain,
% 3.86/0.99      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_21,plain,
% 3.86/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.86/0.99      | ~ m1_pre_topc(X3,X4)
% 3.86/0.99      | ~ m1_pre_topc(X3,X1)
% 3.86/0.99      | ~ m1_pre_topc(X1,X4)
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.86/0.99      | v2_struct_0(X4)
% 3.86/0.99      | v2_struct_0(X2)
% 3.86/0.99      | ~ v2_pre_topc(X2)
% 3.86/0.99      | ~ v2_pre_topc(X4)
% 3.86/0.99      | ~ l1_pre_topc(X2)
% 3.86/0.99      | ~ l1_pre_topc(X4)
% 3.86/0.99      | ~ v1_funct_1(X0)
% 3.86/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1789,plain,
% 3.86/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 3.86/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.86/0.99      | m1_pre_topc(X3,X4) != iProver_top
% 3.86/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 3.86/0.99      | m1_pre_topc(X0,X4) != iProver_top
% 3.86/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.86/0.99      | v2_struct_0(X4) = iProver_top
% 3.86/0.99      | v2_struct_0(X1) = iProver_top
% 3.86/0.99      | v2_pre_topc(X1) != iProver_top
% 3.86/0.99      | v2_pre_topc(X4) != iProver_top
% 3.86/0.99      | l1_pre_topc(X1) != iProver_top
% 3.86/0.99      | l1_pre_topc(X4) != iProver_top
% 3.86/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_22,plain,
% 3.86/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.86/0.99      | ~ m1_pre_topc(X1,X2)
% 3.86/0.99      | m1_pre_topc(X0,X2)
% 3.86/0.99      | ~ v2_pre_topc(X2)
% 3.86/0.99      | ~ l1_pre_topc(X2) ),
% 3.86/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1788,plain,
% 3.86/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.86/0.99      | m1_pre_topc(X1,X2) != iProver_top
% 3.86/0.99      | m1_pre_topc(X0,X2) = iProver_top
% 3.86/0.99      | v2_pre_topc(X2) != iProver_top
% 3.86/0.99      | l1_pre_topc(X2) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2018,plain,
% 3.86/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 3.86/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.86/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 3.86/0.99      | m1_pre_topc(X0,X4) != iProver_top
% 3.86/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.86/0.99      | v2_struct_0(X4) = iProver_top
% 3.86/0.99      | v2_struct_0(X1) = iProver_top
% 3.86/0.99      | v2_pre_topc(X4) != iProver_top
% 3.86/0.99      | v2_pre_topc(X1) != iProver_top
% 3.86/0.99      | l1_pre_topc(X4) != iProver_top
% 3.86/0.99      | l1_pre_topc(X1) != iProver_top
% 3.86/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.86/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1789,c_1788]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7067,plain,
% 3.86/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
% 3.86/0.99      | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.86/0.99      | m1_pre_topc(sK1,X1) != iProver_top
% 3.86/0.99      | v2_struct_0(X1) = iProver_top
% 3.86/0.99      | v2_struct_0(sK2) = iProver_top
% 3.86/0.99      | v2_pre_topc(X1) != iProver_top
% 3.86/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.86/0.99      | l1_pre_topc(X1) != iProver_top
% 3.86/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.86/0.99      | v1_funct_1(sK7) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1853,c_2018]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_42,negated_conjecture,
% 3.86/0.99      ( ~ v2_struct_0(sK2) ),
% 3.86/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_49,plain,
% 3.86/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_41,negated_conjecture,
% 3.86/0.99      ( v2_pre_topc(sK2) ),
% 3.86/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_50,plain,
% 3.86/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_40,negated_conjecture,
% 3.86/0.99      ( l1_pre_topc(sK2) ),
% 3.86/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_51,plain,
% 3.86/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7815,plain,
% 3.86/0.99      ( v2_pre_topc(X1) != iProver_top
% 3.86/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
% 3.86/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.86/0.99      | m1_pre_topc(sK1,X1) != iProver_top
% 3.86/0.99      | v2_struct_0(X1) = iProver_top
% 3.86/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_7067,c_49,c_50,c_51,c_62,c_1846]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7816,plain,
% 3.86/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
% 3.86/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.86/0.99      | m1_pre_topc(sK1,X1) != iProver_top
% 3.86/0.99      | v2_struct_0(X1) = iProver_top
% 3.86/0.99      | v2_pre_topc(X1) != iProver_top
% 3.86/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_7815]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7827,plain,
% 3.86/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k3_tmap_1(X0,sK2,sK1,sK3,sK7)
% 3.86/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 3.86/0.99      | v2_struct_0(X0) = iProver_top
% 3.86/0.99      | v2_pre_topc(X0) != iProver_top
% 3.86/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1773,c_7816]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_20,plain,
% 3.86/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.86/0.99      | ~ m1_pre_topc(X3,X1)
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.86/0.99      | v2_struct_0(X1)
% 3.86/0.99      | v2_struct_0(X2)
% 3.86/0.99      | ~ v2_pre_topc(X2)
% 3.86/0.99      | ~ v2_pre_topc(X1)
% 3.86/0.99      | ~ l1_pre_topc(X2)
% 3.86/0.99      | ~ l1_pre_topc(X1)
% 3.86/0.99      | ~ v1_funct_1(X0)
% 3.86/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.86/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1790,plain,
% 3.86/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 3.86/0.99      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.86/0.99      | m1_pre_topc(X3,X0) != iProver_top
% 3.86/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.86/0.99      | v2_struct_0(X1) = iProver_top
% 3.86/0.99      | v2_struct_0(X0) = iProver_top
% 3.86/0.99      | v2_pre_topc(X1) != iProver_top
% 3.86/0.99      | v2_pre_topc(X0) != iProver_top
% 3.86/0.99      | l1_pre_topc(X1) != iProver_top
% 3.86/0.99      | l1_pre_topc(X0) != iProver_top
% 3.86/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3691,plain,
% 3.86/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0)
% 3.86/0.99      | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 3.86/0.99      | m1_pre_topc(X0,sK1) != iProver_top
% 3.86/0.99      | v2_struct_0(sK1) = iProver_top
% 3.86/0.99      | v2_struct_0(sK2) = iProver_top
% 3.86/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.86/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.86/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.86/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.86/0.99      | v1_funct_1(sK7) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1853,c_1790]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_45,negated_conjecture,
% 3.86/0.99      ( ~ v2_struct_0(sK1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_46,plain,
% 3.86/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_44,negated_conjecture,
% 3.86/0.99      ( v2_pre_topc(sK1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_47,plain,
% 3.86/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_43,negated_conjecture,
% 3.86/0.99      ( l1_pre_topc(sK1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_48,plain,
% 3.86/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5818,plain,
% 3.86/0.99      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.86/0.99      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_3691,c_46,c_47,c_48,c_49,c_50,c_51,c_62,c_1846]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5819,plain,
% 3.86/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0)
% 3.86/0.99      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_5818]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_5826,plain,
% 3.86/0.99      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1773,c_5819]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7845,plain,
% 3.86/0.99      ( k3_tmap_1(X0,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
% 3.86/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 3.86/0.99      | v2_struct_0(X0) = iProver_top
% 3.86/0.99      | v2_pre_topc(X0) != iProver_top
% 3.86/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.86/0.99      inference(light_normalisation,[status(thm)],[c_7827,c_5826]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8911,plain,
% 3.86/0.99      ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
% 3.86/0.99      | v2_struct_0(sK1) = iProver_top
% 3.86/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.86/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1831,c_7845]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8914,plain,
% 3.86/0.99      ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_8911,c_46,c_47,c_48]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_24,negated_conjecture,
% 3.86/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
% 3.86/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
% 3.86/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1786,plain,
% 3.86/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) = iProver_top
% 3.86/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1919,plain,
% 3.86/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) = iProver_top
% 3.86/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 3.86/0.99      inference(light_normalisation,[status(thm)],[c_1786,c_26]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8917,plain,
% 3.86/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) = iProver_top
% 3.86/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 3.86/0.99      inference(demodulation,[status(thm)],[c_8914,c_1919]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_15952,plain,
% 3.86/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 3.86/0.99      inference(demodulation,[status(thm)],[c_15277,c_8917]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_23,negated_conjecture,
% 3.86/0.99      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
% 3.86/0.99      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
% 3.86/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1787,plain,
% 3.86/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) != iProver_top
% 3.86/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1924,plain,
% 3.86/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) != iProver_top
% 3.86/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 3.86/0.99      inference(light_normalisation,[status(thm)],[c_1787,c_26]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8918,plain,
% 3.86/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) != iProver_top
% 3.86/0.99      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 3.86/0.99      inference(demodulation,[status(thm)],[c_8914,c_1924]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_15953,plain,
% 3.86/0.99      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 3.86/0.99      inference(demodulation,[status(thm)],[c_15277,c_8918]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_15975,plain,
% 3.86/0.99      ( $false ),
% 3.86/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_15952,c_15953]) ).
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  ------                               Statistics
% 3.86/0.99  
% 3.86/0.99  ------ Selected
% 3.86/0.99  
% 3.86/0.99  total_time:                             0.446
% 3.86/0.99  
%------------------------------------------------------------------------------
