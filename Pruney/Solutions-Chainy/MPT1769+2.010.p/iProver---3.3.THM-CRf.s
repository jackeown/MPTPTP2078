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
% DateTime   : Thu Dec  3 12:23:03 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  180 (2657 expanded)
%              Number of clauses        :  109 ( 501 expanded)
%              Number of leaves         :   18 (1086 expanded)
%              Depth                    :   20
%              Number of atoms          :  995 (53655 expanded)
%              Number of equality atoms :  254 (3406 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

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

fof(f31,plain,(
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

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f33,f40,f39,f38,f37,f36,f35,f34])).

fof(f77,plain,(
    r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
    sK1 = sK4 ),
    inference(cnf_transformation,[],[f41])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK0(X0,X1,X2),X2)
            & r2_hidden(sK0(X0,X1,X2),X1)
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f28])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f8])).

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

fof(f55,plain,(
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

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f54,plain,(
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

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f79,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f52])).

cnf(c_17,negated_conjecture,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_522,plain,
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
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_523,plain,
    ( ~ v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(u1_struct_0(sK2))
    | sK7 = sK5 ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_525,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | sK7 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_27,c_26,c_25,c_21,c_20,c_19])).

cnf(c_3484,plain,
    ( sK7 = sK5
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3513,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3512,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3510,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5197,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3512,c_3510])).

cnf(c_6029,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3513,c_5197])).

cnf(c_3504,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( sK1 = sK4 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3560,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3504,c_18])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3511,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4471,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3560,c_3511])).

cnf(c_3498,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4470,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3498,c_3511])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r2_hidden(sK0(X1,X2,X0),X2)
    | r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_246,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_247,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_246])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(sK0(X1,X0,X2),X0)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_247])).

cnf(c_1191,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_1192,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_1191])).

cnf(c_1265,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_328,c_1192])).

cnf(c_3482,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1265])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_332,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_247])).

cnf(c_3485,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_7755,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(X2,X0) = iProver_top
    | v1_xboole_0(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3482,c_3485])).

cnf(c_7775,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK5) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4470,c_7755])).

cnf(c_7938,plain,
    ( r1_tarski(sK7,X0) != iProver_top
    | r1_tarski(sK7,sK5) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4471,c_7775])).

cnf(c_8055,plain,
    ( r1_tarski(sK7,sK5) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4471,c_7938])).

cnf(c_8069,plain,
    ( r1_tarski(sK7,sK5) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6029,c_8055])).

cnf(c_8720,plain,
    ( sK7 = sK5
    | r1_tarski(sK7,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3484,c_8069])).

cnf(c_5199,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3498,c_3510])).

cnf(c_5276,plain,
    ( sK7 = sK5
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3484,c_5199])).

cnf(c_7777,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK7) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4471,c_7755])).

cnf(c_8158,plain,
    ( r1_tarski(sK5,X0) != iProver_top
    | r1_tarski(sK5,sK7) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4470,c_7777])).

cnf(c_8572,plain,
    ( r1_tarski(sK5,sK7) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3513,c_8158])).

cnf(c_8054,plain,
    ( r1_tarski(sK7,sK5) = iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3513,c_7938])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3514,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8347,plain,
    ( sK7 = sK5
    | r1_tarski(sK5,sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8054,c_3514])).

cnf(c_5200,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3560,c_3510])).

cnf(c_5281,plain,
    ( sK7 = sK5
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3484,c_5200])).

cnf(c_8370,plain,
    ( r1_tarski(sK5,sK7) != iProver_top
    | sK7 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8347,c_5281])).

cnf(c_8371,plain,
    ( sK7 = sK5
    | r1_tarski(sK5,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_8370])).

cnf(c_8698,plain,
    ( sK7 = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_8572,c_8371])).

cnf(c_8776,plain,
    ( sK7 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8720,c_5276,c_8698])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3495,plain,
    ( m1_pre_topc(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3540,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3495,c_18])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3493,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f55])).

cnf(c_3508,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(X0,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3507,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X0,X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3668,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_3508,c_3507])).

cnf(c_5647,plain,
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
    inference(superposition,[status(thm)],[c_3560,c_3668])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_41,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_42,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_43,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_54,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3503,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3549,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3503,c_18])).

cnf(c_6281,plain,
    ( v2_pre_topc(X1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5647,c_41,c_42,c_43,c_54,c_3549])).

cnf(c_6282,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6281])).

cnf(c_6293,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k3_tmap_1(X0,sK2,sK1,sK3,sK7)
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3493,c_6282])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f54])).

cnf(c_3509,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4989,plain,
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
    inference(superposition,[status(thm)],[c_3560,c_3509])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_38,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_39,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_40,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5561,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4989,c_38,c_39,c_40,c_41,c_42,c_43,c_54,c_3549])).

cnf(c_5562,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0)
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5561])).

cnf(c_5569,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
    inference(superposition,[status(thm)],[c_3493,c_5562])).

cnf(c_6311,plain,
    ( k3_tmap_1(X0,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
    | m1_pre_topc(sK1,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6293,c_5569])).

cnf(c_7144,plain,
    ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
    | v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3540,c_6311])).

cnf(c_7147,plain,
    ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7144,c_38,c_39,c_40])).

cnf(c_16,negated_conjecture,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3505,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3605,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3505,c_18])).

cnf(c_7150,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) = iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7147,c_3605])).

cnf(c_8787,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8776,c_7150])).

cnf(c_15,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
    | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3506,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3618,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3506,c_18])).

cnf(c_7151,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) != iProver_top
    | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7147,c_3618])).

cnf(c_8788,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8776,c_7151])).

cnf(c_8806,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8787,c_8788])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.78/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.02  
% 2.78/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/1.02  
% 2.78/1.02  ------  iProver source info
% 2.78/1.02  
% 2.78/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.78/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/1.02  git: non_committed_changes: false
% 2.78/1.02  git: last_make_outside_of_git: false
% 2.78/1.02  
% 2.78/1.02  ------ 
% 2.78/1.02  
% 2.78/1.02  ------ Input Options
% 2.78/1.02  
% 2.78/1.02  --out_options                           all
% 2.78/1.02  --tptp_safe_out                         true
% 2.78/1.02  --problem_path                          ""
% 2.78/1.02  --include_path                          ""
% 2.78/1.02  --clausifier                            res/vclausify_rel
% 2.78/1.02  --clausifier_options                    --mode clausify
% 2.78/1.02  --stdin                                 false
% 2.78/1.02  --stats_out                             all
% 2.78/1.02  
% 2.78/1.02  ------ General Options
% 2.78/1.02  
% 2.78/1.02  --fof                                   false
% 2.78/1.02  --time_out_real                         305.
% 2.78/1.02  --time_out_virtual                      -1.
% 2.78/1.02  --symbol_type_check                     false
% 2.78/1.02  --clausify_out                          false
% 2.78/1.02  --sig_cnt_out                           false
% 2.78/1.02  --trig_cnt_out                          false
% 2.78/1.02  --trig_cnt_out_tolerance                1.
% 2.78/1.02  --trig_cnt_out_sk_spl                   false
% 2.78/1.02  --abstr_cl_out                          false
% 2.78/1.02  
% 2.78/1.02  ------ Global Options
% 2.78/1.02  
% 2.78/1.02  --schedule                              default
% 2.78/1.02  --add_important_lit                     false
% 2.78/1.02  --prop_solver_per_cl                    1000
% 2.78/1.02  --min_unsat_core                        false
% 2.78/1.02  --soft_assumptions                      false
% 2.78/1.02  --soft_lemma_size                       3
% 2.78/1.02  --prop_impl_unit_size                   0
% 2.78/1.02  --prop_impl_unit                        []
% 2.78/1.02  --share_sel_clauses                     true
% 2.78/1.02  --reset_solvers                         false
% 2.78/1.02  --bc_imp_inh                            [conj_cone]
% 2.78/1.02  --conj_cone_tolerance                   3.
% 2.78/1.02  --extra_neg_conj                        none
% 2.78/1.02  --large_theory_mode                     true
% 2.78/1.02  --prolific_symb_bound                   200
% 2.78/1.02  --lt_threshold                          2000
% 2.78/1.02  --clause_weak_htbl                      true
% 2.78/1.02  --gc_record_bc_elim                     false
% 2.78/1.02  
% 2.78/1.02  ------ Preprocessing Options
% 2.78/1.02  
% 2.78/1.02  --preprocessing_flag                    true
% 2.78/1.02  --time_out_prep_mult                    0.1
% 2.78/1.02  --splitting_mode                        input
% 2.78/1.02  --splitting_grd                         true
% 2.78/1.02  --splitting_cvd                         false
% 2.78/1.02  --splitting_cvd_svl                     false
% 2.78/1.02  --splitting_nvd                         32
% 2.78/1.02  --sub_typing                            true
% 2.78/1.02  --prep_gs_sim                           true
% 2.78/1.02  --prep_unflatten                        true
% 2.78/1.02  --prep_res_sim                          true
% 2.78/1.02  --prep_upred                            true
% 2.78/1.02  --prep_sem_filter                       exhaustive
% 2.78/1.02  --prep_sem_filter_out                   false
% 2.78/1.02  --pred_elim                             true
% 2.78/1.02  --res_sim_input                         true
% 2.78/1.02  --eq_ax_congr_red                       true
% 2.78/1.02  --pure_diseq_elim                       true
% 2.78/1.02  --brand_transform                       false
% 2.78/1.02  --non_eq_to_eq                          false
% 2.78/1.02  --prep_def_merge                        true
% 2.78/1.02  --prep_def_merge_prop_impl              false
% 2.78/1.02  --prep_def_merge_mbd                    true
% 2.78/1.02  --prep_def_merge_tr_red                 false
% 2.78/1.02  --prep_def_merge_tr_cl                  false
% 2.78/1.02  --smt_preprocessing                     true
% 2.78/1.02  --smt_ac_axioms                         fast
% 2.78/1.02  --preprocessed_out                      false
% 2.78/1.02  --preprocessed_stats                    false
% 2.78/1.02  
% 2.78/1.02  ------ Abstraction refinement Options
% 2.78/1.02  
% 2.78/1.02  --abstr_ref                             []
% 2.78/1.02  --abstr_ref_prep                        false
% 2.78/1.02  --abstr_ref_until_sat                   false
% 2.78/1.02  --abstr_ref_sig_restrict                funpre
% 2.78/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.02  --abstr_ref_under                       []
% 2.78/1.02  
% 2.78/1.02  ------ SAT Options
% 2.78/1.02  
% 2.78/1.02  --sat_mode                              false
% 2.78/1.02  --sat_fm_restart_options                ""
% 2.78/1.02  --sat_gr_def                            false
% 2.78/1.02  --sat_epr_types                         true
% 2.78/1.02  --sat_non_cyclic_types                  false
% 2.78/1.02  --sat_finite_models                     false
% 2.78/1.02  --sat_fm_lemmas                         false
% 2.78/1.02  --sat_fm_prep                           false
% 2.78/1.02  --sat_fm_uc_incr                        true
% 2.78/1.02  --sat_out_model                         small
% 2.78/1.02  --sat_out_clauses                       false
% 2.78/1.02  
% 2.78/1.02  ------ QBF Options
% 2.78/1.02  
% 2.78/1.02  --qbf_mode                              false
% 2.78/1.02  --qbf_elim_univ                         false
% 2.78/1.02  --qbf_dom_inst                          none
% 2.78/1.02  --qbf_dom_pre_inst                      false
% 2.78/1.02  --qbf_sk_in                             false
% 2.78/1.02  --qbf_pred_elim                         true
% 2.78/1.02  --qbf_split                             512
% 2.78/1.02  
% 2.78/1.02  ------ BMC1 Options
% 2.78/1.02  
% 2.78/1.02  --bmc1_incremental                      false
% 2.78/1.02  --bmc1_axioms                           reachable_all
% 2.78/1.02  --bmc1_min_bound                        0
% 2.78/1.02  --bmc1_max_bound                        -1
% 2.78/1.02  --bmc1_max_bound_default                -1
% 2.78/1.02  --bmc1_symbol_reachability              true
% 2.78/1.02  --bmc1_property_lemmas                  false
% 2.78/1.02  --bmc1_k_induction                      false
% 2.78/1.02  --bmc1_non_equiv_states                 false
% 2.78/1.02  --bmc1_deadlock                         false
% 2.78/1.02  --bmc1_ucm                              false
% 2.78/1.02  --bmc1_add_unsat_core                   none
% 2.78/1.02  --bmc1_unsat_core_children              false
% 2.78/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.02  --bmc1_out_stat                         full
% 2.78/1.02  --bmc1_ground_init                      false
% 2.78/1.02  --bmc1_pre_inst_next_state              false
% 2.78/1.02  --bmc1_pre_inst_state                   false
% 2.78/1.02  --bmc1_pre_inst_reach_state             false
% 2.78/1.02  --bmc1_out_unsat_core                   false
% 2.78/1.02  --bmc1_aig_witness_out                  false
% 2.78/1.02  --bmc1_verbose                          false
% 2.78/1.02  --bmc1_dump_clauses_tptp                false
% 2.78/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.02  --bmc1_dump_file                        -
% 2.78/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.02  --bmc1_ucm_extend_mode                  1
% 2.78/1.02  --bmc1_ucm_init_mode                    2
% 2.78/1.02  --bmc1_ucm_cone_mode                    none
% 2.78/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.02  --bmc1_ucm_relax_model                  4
% 2.78/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.02  --bmc1_ucm_layered_model                none
% 2.78/1.02  --bmc1_ucm_max_lemma_size               10
% 2.78/1.02  
% 2.78/1.02  ------ AIG Options
% 2.78/1.02  
% 2.78/1.02  --aig_mode                              false
% 2.78/1.02  
% 2.78/1.02  ------ Instantiation Options
% 2.78/1.02  
% 2.78/1.02  --instantiation_flag                    true
% 2.78/1.02  --inst_sos_flag                         false
% 2.78/1.02  --inst_sos_phase                        true
% 2.78/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.02  --inst_lit_sel_side                     num_symb
% 2.78/1.02  --inst_solver_per_active                1400
% 2.78/1.02  --inst_solver_calls_frac                1.
% 2.78/1.02  --inst_passive_queue_type               priority_queues
% 2.78/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.02  --inst_passive_queues_freq              [25;2]
% 2.78/1.02  --inst_dismatching                      true
% 2.78/1.02  --inst_eager_unprocessed_to_passive     true
% 2.78/1.02  --inst_prop_sim_given                   true
% 2.78/1.02  --inst_prop_sim_new                     false
% 2.78/1.02  --inst_subs_new                         false
% 2.78/1.02  --inst_eq_res_simp                      false
% 2.78/1.02  --inst_subs_given                       false
% 2.78/1.02  --inst_orphan_elimination               true
% 2.78/1.02  --inst_learning_loop_flag               true
% 2.78/1.02  --inst_learning_start                   3000
% 2.78/1.02  --inst_learning_factor                  2
% 2.78/1.02  --inst_start_prop_sim_after_learn       3
% 2.78/1.02  --inst_sel_renew                        solver
% 2.78/1.02  --inst_lit_activity_flag                true
% 2.78/1.02  --inst_restr_to_given                   false
% 2.78/1.02  --inst_activity_threshold               500
% 2.78/1.02  --inst_out_proof                        true
% 2.78/1.02  
% 2.78/1.02  ------ Resolution Options
% 2.78/1.02  
% 2.78/1.02  --resolution_flag                       true
% 2.78/1.02  --res_lit_sel                           adaptive
% 2.78/1.02  --res_lit_sel_side                      none
% 2.78/1.02  --res_ordering                          kbo
% 2.78/1.02  --res_to_prop_solver                    active
% 2.78/1.02  --res_prop_simpl_new                    false
% 2.78/1.02  --res_prop_simpl_given                  true
% 2.78/1.02  --res_passive_queue_type                priority_queues
% 2.78/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.02  --res_passive_queues_freq               [15;5]
% 2.78/1.02  --res_forward_subs                      full
% 2.78/1.02  --res_backward_subs                     full
% 2.78/1.02  --res_forward_subs_resolution           true
% 2.78/1.02  --res_backward_subs_resolution          true
% 2.78/1.02  --res_orphan_elimination                true
% 2.78/1.02  --res_time_limit                        2.
% 2.78/1.02  --res_out_proof                         true
% 2.78/1.02  
% 2.78/1.02  ------ Superposition Options
% 2.78/1.02  
% 2.78/1.02  --superposition_flag                    true
% 2.78/1.02  --sup_passive_queue_type                priority_queues
% 2.78/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.02  --demod_completeness_check              fast
% 2.78/1.02  --demod_use_ground                      true
% 2.78/1.02  --sup_to_prop_solver                    passive
% 2.78/1.02  --sup_prop_simpl_new                    true
% 2.78/1.02  --sup_prop_simpl_given                  true
% 2.78/1.02  --sup_fun_splitting                     false
% 2.78/1.02  --sup_smt_interval                      50000
% 2.78/1.03  
% 2.78/1.03  ------ Superposition Simplification Setup
% 2.78/1.03  
% 2.78/1.03  --sup_indices_passive                   []
% 2.78/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.03  --sup_full_bw                           [BwDemod]
% 2.78/1.03  --sup_immed_triv                        [TrivRules]
% 2.78/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.03  --sup_immed_bw_main                     []
% 2.78/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.03  
% 2.78/1.03  ------ Combination Options
% 2.78/1.03  
% 2.78/1.03  --comb_res_mult                         3
% 2.78/1.03  --comb_sup_mult                         2
% 2.78/1.03  --comb_inst_mult                        10
% 2.78/1.03  
% 2.78/1.03  ------ Debug Options
% 2.78/1.03  
% 2.78/1.03  --dbg_backtrace                         false
% 2.78/1.03  --dbg_dump_prop_clauses                 false
% 2.78/1.03  --dbg_dump_prop_clauses_file            -
% 2.78/1.03  --dbg_out_stat                          false
% 2.78/1.03  ------ Parsing...
% 2.78/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/1.03  
% 2.78/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.78/1.03  
% 2.78/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/1.03  
% 2.78/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/1.03  ------ Proving...
% 2.78/1.03  ------ Problem Properties 
% 2.78/1.03  
% 2.78/1.03  
% 2.78/1.03  clauses                                 35
% 2.78/1.03  conjectures                             22
% 2.78/1.03  EPR                                     18
% 2.78/1.03  Horn                                    29
% 2.78/1.03  unary                                   21
% 2.78/1.03  binary                                  5
% 2.78/1.03  lits                                    81
% 2.78/1.03  lits eq                                 5
% 2.78/1.03  fd_pure                                 0
% 2.78/1.03  fd_pseudo                               0
% 2.78/1.03  fd_cond                                 0
% 2.78/1.03  fd_pseudo_cond                          1
% 2.78/1.03  AC symbols                              0
% 2.78/1.03  
% 2.78/1.03  ------ Schedule dynamic 5 is on 
% 2.78/1.03  
% 2.78/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.78/1.03  
% 2.78/1.03  
% 2.78/1.03  ------ 
% 2.78/1.03  Current options:
% 2.78/1.03  ------ 
% 2.78/1.03  
% 2.78/1.03  ------ Input Options
% 2.78/1.03  
% 2.78/1.03  --out_options                           all
% 2.78/1.03  --tptp_safe_out                         true
% 2.78/1.03  --problem_path                          ""
% 2.78/1.03  --include_path                          ""
% 2.78/1.03  --clausifier                            res/vclausify_rel
% 2.78/1.03  --clausifier_options                    --mode clausify
% 2.78/1.03  --stdin                                 false
% 2.78/1.03  --stats_out                             all
% 2.78/1.03  
% 2.78/1.03  ------ General Options
% 2.78/1.03  
% 2.78/1.03  --fof                                   false
% 2.78/1.03  --time_out_real                         305.
% 2.78/1.03  --time_out_virtual                      -1.
% 2.78/1.03  --symbol_type_check                     false
% 2.78/1.03  --clausify_out                          false
% 2.78/1.03  --sig_cnt_out                           false
% 2.78/1.03  --trig_cnt_out                          false
% 2.78/1.03  --trig_cnt_out_tolerance                1.
% 2.78/1.03  --trig_cnt_out_sk_spl                   false
% 2.78/1.03  --abstr_cl_out                          false
% 2.78/1.03  
% 2.78/1.03  ------ Global Options
% 2.78/1.03  
% 2.78/1.03  --schedule                              default
% 2.78/1.03  --add_important_lit                     false
% 2.78/1.03  --prop_solver_per_cl                    1000
% 2.78/1.03  --min_unsat_core                        false
% 2.78/1.03  --soft_assumptions                      false
% 2.78/1.03  --soft_lemma_size                       3
% 2.78/1.03  --prop_impl_unit_size                   0
% 2.78/1.03  --prop_impl_unit                        []
% 2.78/1.03  --share_sel_clauses                     true
% 2.78/1.03  --reset_solvers                         false
% 2.78/1.03  --bc_imp_inh                            [conj_cone]
% 2.78/1.03  --conj_cone_tolerance                   3.
% 2.78/1.03  --extra_neg_conj                        none
% 2.78/1.03  --large_theory_mode                     true
% 2.78/1.03  --prolific_symb_bound                   200
% 2.78/1.03  --lt_threshold                          2000
% 2.78/1.03  --clause_weak_htbl                      true
% 2.78/1.03  --gc_record_bc_elim                     false
% 2.78/1.03  
% 2.78/1.03  ------ Preprocessing Options
% 2.78/1.03  
% 2.78/1.03  --preprocessing_flag                    true
% 2.78/1.03  --time_out_prep_mult                    0.1
% 2.78/1.03  --splitting_mode                        input
% 2.78/1.03  --splitting_grd                         true
% 2.78/1.03  --splitting_cvd                         false
% 2.78/1.03  --splitting_cvd_svl                     false
% 2.78/1.03  --splitting_nvd                         32
% 2.78/1.03  --sub_typing                            true
% 2.78/1.03  --prep_gs_sim                           true
% 2.78/1.03  --prep_unflatten                        true
% 2.78/1.03  --prep_res_sim                          true
% 2.78/1.03  --prep_upred                            true
% 2.78/1.03  --prep_sem_filter                       exhaustive
% 2.78/1.03  --prep_sem_filter_out                   false
% 2.78/1.03  --pred_elim                             true
% 2.78/1.03  --res_sim_input                         true
% 2.78/1.03  --eq_ax_congr_red                       true
% 2.78/1.03  --pure_diseq_elim                       true
% 2.78/1.03  --brand_transform                       false
% 2.78/1.03  --non_eq_to_eq                          false
% 2.78/1.03  --prep_def_merge                        true
% 2.78/1.03  --prep_def_merge_prop_impl              false
% 2.78/1.03  --prep_def_merge_mbd                    true
% 2.78/1.03  --prep_def_merge_tr_red                 false
% 2.78/1.03  --prep_def_merge_tr_cl                  false
% 2.78/1.03  --smt_preprocessing                     true
% 2.78/1.03  --smt_ac_axioms                         fast
% 2.78/1.03  --preprocessed_out                      false
% 2.78/1.03  --preprocessed_stats                    false
% 2.78/1.03  
% 2.78/1.03  ------ Abstraction refinement Options
% 2.78/1.03  
% 2.78/1.03  --abstr_ref                             []
% 2.78/1.03  --abstr_ref_prep                        false
% 2.78/1.03  --abstr_ref_until_sat                   false
% 2.78/1.03  --abstr_ref_sig_restrict                funpre
% 2.78/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.03  --abstr_ref_under                       []
% 2.78/1.03  
% 2.78/1.03  ------ SAT Options
% 2.78/1.03  
% 2.78/1.03  --sat_mode                              false
% 2.78/1.03  --sat_fm_restart_options                ""
% 2.78/1.03  --sat_gr_def                            false
% 2.78/1.03  --sat_epr_types                         true
% 2.78/1.03  --sat_non_cyclic_types                  false
% 2.78/1.03  --sat_finite_models                     false
% 2.78/1.03  --sat_fm_lemmas                         false
% 2.78/1.03  --sat_fm_prep                           false
% 2.78/1.03  --sat_fm_uc_incr                        true
% 2.78/1.03  --sat_out_model                         small
% 2.78/1.03  --sat_out_clauses                       false
% 2.78/1.03  
% 2.78/1.03  ------ QBF Options
% 2.78/1.03  
% 2.78/1.03  --qbf_mode                              false
% 2.78/1.03  --qbf_elim_univ                         false
% 2.78/1.03  --qbf_dom_inst                          none
% 2.78/1.03  --qbf_dom_pre_inst                      false
% 2.78/1.03  --qbf_sk_in                             false
% 2.78/1.03  --qbf_pred_elim                         true
% 2.78/1.03  --qbf_split                             512
% 2.78/1.03  
% 2.78/1.03  ------ BMC1 Options
% 2.78/1.03  
% 2.78/1.03  --bmc1_incremental                      false
% 2.78/1.03  --bmc1_axioms                           reachable_all
% 2.78/1.03  --bmc1_min_bound                        0
% 2.78/1.03  --bmc1_max_bound                        -1
% 2.78/1.03  --bmc1_max_bound_default                -1
% 2.78/1.03  --bmc1_symbol_reachability              true
% 2.78/1.03  --bmc1_property_lemmas                  false
% 2.78/1.03  --bmc1_k_induction                      false
% 2.78/1.03  --bmc1_non_equiv_states                 false
% 2.78/1.03  --bmc1_deadlock                         false
% 2.78/1.03  --bmc1_ucm                              false
% 2.78/1.03  --bmc1_add_unsat_core                   none
% 2.78/1.03  --bmc1_unsat_core_children              false
% 2.78/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.03  --bmc1_out_stat                         full
% 2.78/1.03  --bmc1_ground_init                      false
% 2.78/1.03  --bmc1_pre_inst_next_state              false
% 2.78/1.03  --bmc1_pre_inst_state                   false
% 2.78/1.03  --bmc1_pre_inst_reach_state             false
% 2.78/1.03  --bmc1_out_unsat_core                   false
% 2.78/1.03  --bmc1_aig_witness_out                  false
% 2.78/1.03  --bmc1_verbose                          false
% 2.78/1.03  --bmc1_dump_clauses_tptp                false
% 2.78/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.03  --bmc1_dump_file                        -
% 2.78/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.03  --bmc1_ucm_extend_mode                  1
% 2.78/1.03  --bmc1_ucm_init_mode                    2
% 2.78/1.03  --bmc1_ucm_cone_mode                    none
% 2.78/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.03  --bmc1_ucm_relax_model                  4
% 2.78/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.03  --bmc1_ucm_layered_model                none
% 2.78/1.03  --bmc1_ucm_max_lemma_size               10
% 2.78/1.03  
% 2.78/1.03  ------ AIG Options
% 2.78/1.03  
% 2.78/1.03  --aig_mode                              false
% 2.78/1.03  
% 2.78/1.03  ------ Instantiation Options
% 2.78/1.03  
% 2.78/1.03  --instantiation_flag                    true
% 2.78/1.03  --inst_sos_flag                         false
% 2.78/1.03  --inst_sos_phase                        true
% 2.78/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.03  --inst_lit_sel_side                     none
% 2.78/1.03  --inst_solver_per_active                1400
% 2.78/1.03  --inst_solver_calls_frac                1.
% 2.78/1.03  --inst_passive_queue_type               priority_queues
% 2.78/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.03  --inst_passive_queues_freq              [25;2]
% 2.78/1.03  --inst_dismatching                      true
% 2.78/1.03  --inst_eager_unprocessed_to_passive     true
% 2.78/1.03  --inst_prop_sim_given                   true
% 2.78/1.03  --inst_prop_sim_new                     false
% 2.78/1.03  --inst_subs_new                         false
% 2.78/1.03  --inst_eq_res_simp                      false
% 2.78/1.03  --inst_subs_given                       false
% 2.78/1.03  --inst_orphan_elimination               true
% 2.78/1.03  --inst_learning_loop_flag               true
% 2.78/1.03  --inst_learning_start                   3000
% 2.78/1.03  --inst_learning_factor                  2
% 2.78/1.03  --inst_start_prop_sim_after_learn       3
% 2.78/1.03  --inst_sel_renew                        solver
% 2.78/1.03  --inst_lit_activity_flag                true
% 2.78/1.03  --inst_restr_to_given                   false
% 2.78/1.03  --inst_activity_threshold               500
% 2.78/1.03  --inst_out_proof                        true
% 2.78/1.03  
% 2.78/1.03  ------ Resolution Options
% 2.78/1.03  
% 2.78/1.03  --resolution_flag                       false
% 2.78/1.03  --res_lit_sel                           adaptive
% 2.78/1.03  --res_lit_sel_side                      none
% 2.78/1.03  --res_ordering                          kbo
% 2.78/1.03  --res_to_prop_solver                    active
% 2.78/1.03  --res_prop_simpl_new                    false
% 2.78/1.03  --res_prop_simpl_given                  true
% 2.78/1.03  --res_passive_queue_type                priority_queues
% 2.78/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.03  --res_passive_queues_freq               [15;5]
% 2.78/1.03  --res_forward_subs                      full
% 2.78/1.03  --res_backward_subs                     full
% 2.78/1.03  --res_forward_subs_resolution           true
% 2.78/1.03  --res_backward_subs_resolution          true
% 2.78/1.03  --res_orphan_elimination                true
% 2.78/1.03  --res_time_limit                        2.
% 2.78/1.03  --res_out_proof                         true
% 2.78/1.03  
% 2.78/1.03  ------ Superposition Options
% 2.78/1.03  
% 2.78/1.03  --superposition_flag                    true
% 2.78/1.03  --sup_passive_queue_type                priority_queues
% 2.78/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.03  --demod_completeness_check              fast
% 2.78/1.03  --demod_use_ground                      true
% 2.78/1.03  --sup_to_prop_solver                    passive
% 2.78/1.03  --sup_prop_simpl_new                    true
% 2.78/1.03  --sup_prop_simpl_given                  true
% 2.78/1.03  --sup_fun_splitting                     false
% 2.78/1.03  --sup_smt_interval                      50000
% 2.78/1.03  
% 2.78/1.03  ------ Superposition Simplification Setup
% 2.78/1.03  
% 2.78/1.03  --sup_indices_passive                   []
% 2.78/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.03  --sup_full_bw                           [BwDemod]
% 2.78/1.03  --sup_immed_triv                        [TrivRules]
% 2.78/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.03  --sup_immed_bw_main                     []
% 2.78/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.03  
% 2.78/1.03  ------ Combination Options
% 2.78/1.03  
% 2.78/1.03  --comb_res_mult                         3
% 2.78/1.03  --comb_sup_mult                         2
% 2.78/1.03  --comb_inst_mult                        10
% 2.78/1.03  
% 2.78/1.03  ------ Debug Options
% 2.78/1.03  
% 2.78/1.03  --dbg_backtrace                         false
% 2.78/1.03  --dbg_dump_prop_clauses                 false
% 2.78/1.03  --dbg_dump_prop_clauses_file            -
% 2.78/1.03  --dbg_out_stat                          false
% 2.78/1.03  
% 2.78/1.03  
% 2.78/1.03  
% 2.78/1.03  
% 2.78/1.03  ------ Proving...
% 2.78/1.03  
% 2.78/1.03  
% 2.78/1.03  % SZS status Theorem for theBenchmark.p
% 2.78/1.03  
% 2.78/1.03   Resolution empty clause
% 2.78/1.03  
% 2.78/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/1.03  
% 2.78/1.03  fof(f6,axiom,(
% 2.78/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 2.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.03  
% 2.78/1.03  fof(f16,plain,(
% 2.78/1.03    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 2.78/1.03    inference(ennf_transformation,[],[f6])).
% 2.78/1.03  
% 2.78/1.03  fof(f17,plain,(
% 2.78/1.03    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.78/1.03    inference(flattening,[],[f16])).
% 2.78/1.03  
% 2.78/1.03  fof(f31,plain,(
% 2.78/1.03    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 2.78/1.03    inference(nnf_transformation,[],[f17])).
% 2.78/1.03  
% 2.78/1.03  fof(f52,plain,(
% 2.78/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 2.78/1.03    inference(cnf_transformation,[],[f31])).
% 2.78/1.03  
% 2.78/1.03  fof(f10,conjecture,(
% 2.78/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 2.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.03  
% 2.78/1.03  fof(f11,negated_conjecture,(
% 2.78/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3) => (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <=> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5))))))))))),
% 2.78/1.03    inference(negated_conjecture,[],[f10])).
% 2.78/1.03  
% 2.78/1.03  fof(f24,plain,(
% 2.78/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & (r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3)) & (m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.78/1.03    inference(ennf_transformation,[],[f11])).
% 2.78/1.03  
% 2.78/1.03  fof(f25,plain,(
% 2.78/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5) <~> r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.78/1.03    inference(flattening,[],[f24])).
% 2.78/1.03  
% 2.78/1.03  fof(f32,plain,(
% 2.78/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5))) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.78/1.03    inference(nnf_transformation,[],[f25])).
% 2.78/1.03  
% 2.78/1.03  fof(f33,plain,(
% 2.78/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.78/1.03    inference(flattening,[],[f32])).
% 2.78/1.03  
% 2.78/1.03  fof(f40,plain,(
% 2.78/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) => ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK7),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,sK7),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,sK7) & X0 = X3 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 2.78/1.03    introduced(choice_axiom,[])).
% 2.78/1.03  
% 2.78/1.03  fof(f39,plain,(
% 2.78/1.03    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK6) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK6)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),sK6) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),sK6)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 2.78/1.03    introduced(choice_axiom,[])).
% 2.78/1.03  
% 2.78/1.03  fof(f38,plain,(
% 2.78/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK5,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK5,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),sK5,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.78/1.03    introduced(choice_axiom,[])).
% 2.78/1.03  
% 2.78/1.03  fof(f37,plain,(
% 2.78/1.03    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(sK4),u1_struct_0(X1),X4,X6) & sK4 = X0 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.78/1.03    introduced(choice_axiom,[])).
% 2.78/1.03  
% 2.78/1.03  fof(f36,plain,(
% 2.78/1.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK3),X5) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X6),X5)) & (r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,sK3),X5) | r2_funct_2(u1_struct_0(sK3),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK3,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.78/1.03    introduced(choice_axiom,[])).
% 2.78/1.03  
% 2.78/1.03  fof(f35,plain,(
% 2.78/1.03    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X0,sK2,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k3_tmap_1(X0,sK2,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X3),u1_struct_0(sK2),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK2)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(sK2)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK2)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.78/1.03    introduced(choice_axiom,[])).
% 2.78/1.03  
% 2.78/1.03  fof(f34,plain,(
% 2.78/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & X0 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK1,X1,X4,X2),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X6),X5)) & (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK1,X1,X4,X2),X5) | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(sK1,X1,X3,X2,X6),X5)) & r1_funct_2(u1_struct_0(sK1),u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X1),X4,X6) & sK1 = X3 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X6)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.78/1.03    introduced(choice_axiom,[])).
% 2.78/1.03  
% 2.78/1.03  fof(f41,plain,(
% 2.78/1.03    (((((((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)) & (r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)) & r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) & sK1 = sK4 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK6,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.78/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f33,f40,f39,f38,f37,f36,f35,f34])).
% 2.78/1.03  
% 2.78/1.03  fof(f77,plain,(
% 2.78/1.03    r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7)),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f67,plain,(
% 2.78/1.03    v1_funct_1(sK5)),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f68,plain,(
% 2.78/1.03    v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f69,plain,(
% 2.78/1.03    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f73,plain,(
% 2.78/1.03    v1_funct_1(sK7)),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f74,plain,(
% 2.78/1.03    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2))),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f75,plain,(
% 2.78/1.03    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f1,axiom,(
% 2.78/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.03  
% 2.78/1.03  fof(f26,plain,(
% 2.78/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.78/1.03    inference(nnf_transformation,[],[f1])).
% 2.78/1.03  
% 2.78/1.03  fof(f27,plain,(
% 2.78/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.78/1.03    inference(flattening,[],[f26])).
% 2.78/1.03  
% 2.78/1.03  fof(f43,plain,(
% 2.78/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.78/1.03    inference(cnf_transformation,[],[f27])).
% 2.78/1.03  
% 2.78/1.03  fof(f80,plain,(
% 2.78/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.78/1.03    inference(equality_resolution,[],[f43])).
% 2.78/1.03  
% 2.78/1.03  fof(f3,axiom,(
% 2.78/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.03  
% 2.78/1.03  fof(f30,plain,(
% 2.78/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.78/1.03    inference(nnf_transformation,[],[f3])).
% 2.78/1.03  
% 2.78/1.03  fof(f49,plain,(
% 2.78/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.78/1.03    inference(cnf_transformation,[],[f30])).
% 2.78/1.03  
% 2.78/1.03  fof(f5,axiom,(
% 2.78/1.03    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.03  
% 2.78/1.03  fof(f15,plain,(
% 2.78/1.03    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.78/1.03    inference(ennf_transformation,[],[f5])).
% 2.78/1.03  
% 2.78/1.03  fof(f51,plain,(
% 2.78/1.03    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.78/1.03    inference(cnf_transformation,[],[f15])).
% 2.78/1.03  
% 2.78/1.03  fof(f76,plain,(
% 2.78/1.03    sK1 = sK4),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f48,plain,(
% 2.78/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.78/1.03    inference(cnf_transformation,[],[f30])).
% 2.78/1.03  
% 2.78/1.03  fof(f2,axiom,(
% 2.78/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 2.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.03  
% 2.78/1.03  fof(f12,plain,(
% 2.78/1.03    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.78/1.03    inference(ennf_transformation,[],[f2])).
% 2.78/1.03  
% 2.78/1.03  fof(f13,plain,(
% 2.78/1.03    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.78/1.03    inference(flattening,[],[f12])).
% 2.78/1.03  
% 2.78/1.03  fof(f28,plain,(
% 2.78/1.03    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 2.78/1.03    introduced(choice_axiom,[])).
% 2.78/1.03  
% 2.78/1.03  fof(f29,plain,(
% 2.78/1.03    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.78/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f28])).
% 2.78/1.03  
% 2.78/1.03  fof(f46,plain,(
% 2.78/1.03    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.78/1.03    inference(cnf_transformation,[],[f29])).
% 2.78/1.03  
% 2.78/1.03  fof(f4,axiom,(
% 2.78/1.03    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.03  
% 2.78/1.03  fof(f14,plain,(
% 2.78/1.03    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.78/1.03    inference(ennf_transformation,[],[f4])).
% 2.78/1.03  
% 2.78/1.03  fof(f50,plain,(
% 2.78/1.03    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.78/1.03    inference(cnf_transformation,[],[f14])).
% 2.78/1.03  
% 2.78/1.03  fof(f44,plain,(
% 2.78/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.78/1.03    inference(cnf_transformation,[],[f27])).
% 2.78/1.03  
% 2.78/1.03  fof(f66,plain,(
% 2.78/1.03    m1_pre_topc(sK4,sK1)),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f64,plain,(
% 2.78/1.03    m1_pre_topc(sK3,sK1)),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f8,axiom,(
% 2.78/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 2.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.03  
% 2.78/1.03  fof(f20,plain,(
% 2.78/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.78/1.03    inference(ennf_transformation,[],[f8])).
% 2.78/1.03  
% 2.78/1.03  fof(f21,plain,(
% 2.78/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.78/1.03    inference(flattening,[],[f20])).
% 2.78/1.03  
% 2.78/1.03  fof(f55,plain,(
% 2.78/1.03    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.78/1.03    inference(cnf_transformation,[],[f21])).
% 2.78/1.03  
% 2.78/1.03  fof(f9,axiom,(
% 2.78/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.03  
% 2.78/1.03  fof(f22,plain,(
% 2.78/1.03    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.78/1.03    inference(ennf_transformation,[],[f9])).
% 2.78/1.03  
% 2.78/1.03  fof(f23,plain,(
% 2.78/1.03    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.78/1.03    inference(flattening,[],[f22])).
% 2.78/1.03  
% 2.78/1.03  fof(f56,plain,(
% 2.78/1.03    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.78/1.03    inference(cnf_transformation,[],[f23])).
% 2.78/1.03  
% 2.78/1.03  fof(f60,plain,(
% 2.78/1.03    ~v2_struct_0(sK2)),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f61,plain,(
% 2.78/1.03    v2_pre_topc(sK2)),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f62,plain,(
% 2.78/1.03    l1_pre_topc(sK2)),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f7,axiom,(
% 2.78/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/1.03  
% 2.78/1.03  fof(f18,plain,(
% 2.78/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.78/1.03    inference(ennf_transformation,[],[f7])).
% 2.78/1.03  
% 2.78/1.03  fof(f19,plain,(
% 2.78/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.78/1.03    inference(flattening,[],[f18])).
% 2.78/1.03  
% 2.78/1.03  fof(f54,plain,(
% 2.78/1.03    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.78/1.03    inference(cnf_transformation,[],[f19])).
% 2.78/1.03  
% 2.78/1.03  fof(f57,plain,(
% 2.78/1.03    ~v2_struct_0(sK1)),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f58,plain,(
% 2.78/1.03    v2_pre_topc(sK1)),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f59,plain,(
% 2.78/1.03    l1_pre_topc(sK1)),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f78,plain,(
% 2.78/1.03    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  fof(f79,plain,(
% 2.78/1.03    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)),
% 2.78/1.03    inference(cnf_transformation,[],[f41])).
% 2.78/1.03  
% 2.78/1.03  cnf(c_11,plain,
% 2.78/1.03      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 2.78/1.03      | ~ v1_funct_2(X5,X2,X3)
% 2.78/1.03      | ~ v1_funct_2(X4,X0,X1)
% 2.78/1.03      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.78/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.78/1.03      | ~ v1_funct_1(X5)
% 2.78/1.03      | ~ v1_funct_1(X4)
% 2.78/1.03      | v1_xboole_0(X1)
% 2.78/1.03      | v1_xboole_0(X3)
% 2.78/1.03      | X4 = X5 ),
% 2.78/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_17,negated_conjecture,
% 2.78/1.03      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),u1_struct_0(sK4),u1_struct_0(sK2),sK5,sK7) ),
% 2.78/1.03      inference(cnf_transformation,[],[f77]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_522,plain,
% 2.78/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/1.03      | ~ v1_funct_2(X3,X4,X5)
% 2.78/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.78/1.03      | ~ v1_funct_1(X0)
% 2.78/1.03      | ~ v1_funct_1(X3)
% 2.78/1.03      | v1_xboole_0(X2)
% 2.78/1.03      | v1_xboole_0(X5)
% 2.78/1.03      | X3 = X0
% 2.78/1.03      | u1_struct_0(sK4) != X4
% 2.78/1.03      | u1_struct_0(sK1) != X1
% 2.78/1.03      | u1_struct_0(sK2) != X5
% 2.78/1.03      | u1_struct_0(sK2) != X2
% 2.78/1.03      | sK7 != X3
% 2.78/1.03      | sK5 != X0 ),
% 2.78/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_523,plain,
% 2.78/1.03      ( ~ v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2))
% 2.78/1.03      | ~ v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.78/1.03      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
% 2.78/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.78/1.03      | ~ v1_funct_1(sK7)
% 2.78/1.03      | ~ v1_funct_1(sK5)
% 2.78/1.03      | v1_xboole_0(u1_struct_0(sK2))
% 2.78/1.03      | sK7 = sK5 ),
% 2.78/1.03      inference(unflattening,[status(thm)],[c_522]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_27,negated_conjecture,
% 2.78/1.03      ( v1_funct_1(sK5) ),
% 2.78/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_26,negated_conjecture,
% 2.78/1.03      ( v1_funct_2(sK5,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.78/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_25,negated_conjecture,
% 2.78/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.78/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_21,negated_conjecture,
% 2.78/1.03      ( v1_funct_1(sK7) ),
% 2.78/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_20,negated_conjecture,
% 2.78/1.03      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) ),
% 2.78/1.03      inference(cnf_transformation,[],[f74]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_19,negated_conjecture,
% 2.78/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
% 2.78/1.03      inference(cnf_transformation,[],[f75]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_525,plain,
% 2.78/1.03      ( v1_xboole_0(u1_struct_0(sK2)) | sK7 = sK5 ),
% 2.78/1.03      inference(global_propositional_subsumption,
% 2.78/1.03                [status(thm)],
% 2.78/1.03                [c_523,c_27,c_26,c_25,c_21,c_20,c_19]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3484,plain,
% 2.78/1.03      ( sK7 = sK5 | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f80]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3513,plain,
% 2.78/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_6,plain,
% 2.78/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.78/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3512,plain,
% 2.78/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.78/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_9,plain,
% 2.78/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.03      | ~ v1_xboole_0(X2)
% 2.78/1.03      | v1_xboole_0(X0) ),
% 2.78/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3510,plain,
% 2.78/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.78/1.03      | v1_xboole_0(X2) != iProver_top
% 2.78/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_5197,plain,
% 2.78/1.03      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.78/1.03      | v1_xboole_0(X2) != iProver_top
% 2.78/1.03      | v1_xboole_0(X0) = iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3512,c_3510]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_6029,plain,
% 2.78/1.03      ( v1_xboole_0(X0) != iProver_top
% 2.78/1.03      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3513,c_5197]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3504,plain,
% 2.78/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_18,negated_conjecture,
% 2.78/1.03      ( sK1 = sK4 ),
% 2.78/1.03      inference(cnf_transformation,[],[f76]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3560,plain,
% 2.78/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 2.78/1.03      inference(light_normalisation,[status(thm)],[c_3504,c_18]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_7,plain,
% 2.78/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.78/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3511,plain,
% 2.78/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.78/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_4471,plain,
% 2.78/1.03      ( r1_tarski(sK7,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3560,c_3511]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3498,plain,
% 2.78/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_4470,plain,
% 2.78/1.03      ( r1_tarski(sK5,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3498,c_3511]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_4,plain,
% 2.78/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.78/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.78/1.03      | r2_hidden(sK0(X1,X2,X0),X2)
% 2.78/1.03      | r1_tarski(X2,X0) ),
% 2.78/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_246,plain,
% 2.78/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.78/1.03      inference(prop_impl,[status(thm)],[c_6]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_247,plain,
% 2.78/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.78/1.03      inference(renaming,[status(thm)],[c_246]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_328,plain,
% 2.78/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.78/1.03      | r2_hidden(sK0(X1,X0,X2),X0)
% 2.78/1.03      | ~ r1_tarski(X2,X1)
% 2.78/1.03      | r1_tarski(X0,X2) ),
% 2.78/1.03      inference(bin_hyper_res,[status(thm)],[c_4,c_247]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_1191,plain,
% 2.78/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.78/1.03      inference(prop_impl,[status(thm)],[c_6]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_1192,plain,
% 2.78/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.78/1.03      inference(renaming,[status(thm)],[c_1191]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_1265,plain,
% 2.78/1.03      ( r2_hidden(sK0(X0,X1,X2),X1)
% 2.78/1.03      | ~ r1_tarski(X1,X0)
% 2.78/1.03      | ~ r1_tarski(X2,X0)
% 2.78/1.03      | r1_tarski(X1,X2) ),
% 2.78/1.03      inference(bin_hyper_res,[status(thm)],[c_328,c_1192]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3482,plain,
% 2.78/1.03      ( r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 2.78/1.03      | r1_tarski(X2,X0) != iProver_top
% 2.78/1.03      | r1_tarski(X1,X0) != iProver_top
% 2.78/1.03      | r1_tarski(X1,X2) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_1265]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_8,plain,
% 2.78/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.78/1.03      | ~ r2_hidden(X2,X0)
% 2.78/1.03      | ~ v1_xboole_0(X1) ),
% 2.78/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_332,plain,
% 2.78/1.03      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.78/1.03      inference(bin_hyper_res,[status(thm)],[c_8,c_247]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3485,plain,
% 2.78/1.03      ( r2_hidden(X0,X1) != iProver_top
% 2.78/1.03      | r1_tarski(X1,X2) != iProver_top
% 2.78/1.03      | v1_xboole_0(X2) != iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_7755,plain,
% 2.78/1.03      ( r1_tarski(X0,X1) != iProver_top
% 2.78/1.03      | r1_tarski(X2,X1) != iProver_top
% 2.78/1.03      | r1_tarski(X2,X3) != iProver_top
% 2.78/1.03      | r1_tarski(X2,X0) = iProver_top
% 2.78/1.03      | v1_xboole_0(X3) != iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3482,c_3485]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_7775,plain,
% 2.78/1.03      ( r1_tarski(X0,X1) != iProver_top
% 2.78/1.03      | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top
% 2.78/1.03      | r1_tarski(X0,sK5) = iProver_top
% 2.78/1.03      | v1_xboole_0(X1) != iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_4470,c_7755]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_7938,plain,
% 2.78/1.03      ( r1_tarski(sK7,X0) != iProver_top
% 2.78/1.03      | r1_tarski(sK7,sK5) = iProver_top
% 2.78/1.03      | v1_xboole_0(X0) != iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_4471,c_7775]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_8055,plain,
% 2.78/1.03      ( r1_tarski(sK7,sK5) = iProver_top
% 2.78/1.03      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_4471,c_7938]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_8069,plain,
% 2.78/1.03      ( r1_tarski(sK7,sK5) = iProver_top
% 2.78/1.03      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_6029,c_8055]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_8720,plain,
% 2.78/1.03      ( sK7 = sK5 | r1_tarski(sK7,sK5) = iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3484,c_8069]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_5199,plain,
% 2.78/1.03      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 2.78/1.03      | v1_xboole_0(sK5) = iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3498,c_3510]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_5276,plain,
% 2.78/1.03      ( sK7 = sK5 | v1_xboole_0(sK5) = iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3484,c_5199]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_7777,plain,
% 2.78/1.03      ( r1_tarski(X0,X1) != iProver_top
% 2.78/1.03      | r1_tarski(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top
% 2.78/1.03      | r1_tarski(X0,sK7) = iProver_top
% 2.78/1.03      | v1_xboole_0(X1) != iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_4471,c_7755]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_8158,plain,
% 2.78/1.03      ( r1_tarski(sK5,X0) != iProver_top
% 2.78/1.03      | r1_tarski(sK5,sK7) = iProver_top
% 2.78/1.03      | v1_xboole_0(X0) != iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_4470,c_7777]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_8572,plain,
% 2.78/1.03      ( r1_tarski(sK5,sK7) = iProver_top | v1_xboole_0(sK5) != iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3513,c_8158]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_8054,plain,
% 2.78/1.03      ( r1_tarski(sK7,sK5) = iProver_top | v1_xboole_0(sK7) != iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3513,c_7938]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_0,plain,
% 2.78/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.78/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3514,plain,
% 2.78/1.03      ( X0 = X1
% 2.78/1.03      | r1_tarski(X0,X1) != iProver_top
% 2.78/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_8347,plain,
% 2.78/1.03      ( sK7 = sK5
% 2.78/1.03      | r1_tarski(sK5,sK7) != iProver_top
% 2.78/1.03      | v1_xboole_0(sK7) != iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_8054,c_3514]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_5200,plain,
% 2.78/1.03      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 2.78/1.03      | v1_xboole_0(sK7) = iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3560,c_3510]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_5281,plain,
% 2.78/1.03      ( sK7 = sK5 | v1_xboole_0(sK7) = iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3484,c_5200]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_8370,plain,
% 2.78/1.03      ( r1_tarski(sK5,sK7) != iProver_top | sK7 = sK5 ),
% 2.78/1.03      inference(global_propositional_subsumption,[status(thm)],[c_8347,c_5281]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_8371,plain,
% 2.78/1.03      ( sK7 = sK5 | r1_tarski(sK5,sK7) != iProver_top ),
% 2.78/1.03      inference(renaming,[status(thm)],[c_8370]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_8698,plain,
% 2.78/1.03      ( sK7 = sK5 | v1_xboole_0(sK5) != iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_8572,c_8371]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_8776,plain,
% 2.78/1.03      ( sK7 = sK5 ),
% 2.78/1.03      inference(global_propositional_subsumption,
% 2.78/1.03                [status(thm)],
% 2.78/1.03                [c_8720,c_5276,c_8698]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_28,negated_conjecture,
% 2.78/1.03      ( m1_pre_topc(sK4,sK1) ),
% 2.78/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3495,plain,
% 2.78/1.03      ( m1_pre_topc(sK4,sK1) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3540,plain,
% 2.78/1.03      ( m1_pre_topc(sK1,sK1) = iProver_top ),
% 2.78/1.03      inference(light_normalisation,[status(thm)],[c_3495,c_18]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_30,negated_conjecture,
% 2.78/1.03      ( m1_pre_topc(sK3,sK1) ),
% 2.78/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3493,plain,
% 2.78/1.03      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_13,plain,
% 2.78/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.78/1.03      | ~ m1_pre_topc(X3,X4)
% 2.78/1.03      | ~ m1_pre_topc(X3,X1)
% 2.78/1.03      | ~ m1_pre_topc(X1,X4)
% 2.78/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.78/1.03      | v2_struct_0(X4)
% 2.78/1.03      | v2_struct_0(X2)
% 2.78/1.03      | ~ v2_pre_topc(X2)
% 2.78/1.03      | ~ v2_pre_topc(X4)
% 2.78/1.03      | ~ l1_pre_topc(X2)
% 2.78/1.03      | ~ l1_pre_topc(X4)
% 2.78/1.03      | ~ v1_funct_1(X0)
% 2.78/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 2.78/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3508,plain,
% 2.78/1.03      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 2.78/1.03      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.78/1.03      | m1_pre_topc(X3,X4) != iProver_top
% 2.78/1.03      | m1_pre_topc(X3,X0) != iProver_top
% 2.78/1.03      | m1_pre_topc(X0,X4) != iProver_top
% 2.78/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.78/1.03      | v2_struct_0(X4) = iProver_top
% 2.78/1.03      | v2_struct_0(X1) = iProver_top
% 2.78/1.03      | v2_pre_topc(X1) != iProver_top
% 2.78/1.03      | v2_pre_topc(X4) != iProver_top
% 2.78/1.03      | l1_pre_topc(X1) != iProver_top
% 2.78/1.03      | l1_pre_topc(X4) != iProver_top
% 2.78/1.03      | v1_funct_1(X2) != iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_14,plain,
% 2.78/1.03      ( ~ m1_pre_topc(X0,X1)
% 2.78/1.03      | ~ m1_pre_topc(X1,X2)
% 2.78/1.03      | m1_pre_topc(X0,X2)
% 2.78/1.03      | ~ v2_pre_topc(X2)
% 2.78/1.03      | ~ l1_pre_topc(X2) ),
% 2.78/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3507,plain,
% 2.78/1.03      ( m1_pre_topc(X0,X1) != iProver_top
% 2.78/1.03      | m1_pre_topc(X1,X2) != iProver_top
% 2.78/1.03      | m1_pre_topc(X0,X2) = iProver_top
% 2.78/1.03      | v2_pre_topc(X2) != iProver_top
% 2.78/1.03      | l1_pre_topc(X2) != iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3668,plain,
% 2.78/1.03      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 2.78/1.03      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.78/1.03      | m1_pre_topc(X3,X0) != iProver_top
% 2.78/1.03      | m1_pre_topc(X0,X4) != iProver_top
% 2.78/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.78/1.03      | v2_struct_0(X4) = iProver_top
% 2.78/1.03      | v2_struct_0(X1) = iProver_top
% 2.78/1.03      | v2_pre_topc(X4) != iProver_top
% 2.78/1.03      | v2_pre_topc(X1) != iProver_top
% 2.78/1.03      | l1_pre_topc(X4) != iProver_top
% 2.78/1.03      | l1_pre_topc(X1) != iProver_top
% 2.78/1.03      | v1_funct_1(X2) != iProver_top ),
% 2.78/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_3508,c_3507]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_5647,plain,
% 2.78/1.03      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
% 2.78/1.03      | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.78/1.03      | m1_pre_topc(X0,sK1) != iProver_top
% 2.78/1.03      | m1_pre_topc(sK1,X1) != iProver_top
% 2.78/1.03      | v2_struct_0(X1) = iProver_top
% 2.78/1.03      | v2_struct_0(sK2) = iProver_top
% 2.78/1.03      | v2_pre_topc(X1) != iProver_top
% 2.78/1.03      | v2_pre_topc(sK2) != iProver_top
% 2.78/1.03      | l1_pre_topc(X1) != iProver_top
% 2.78/1.03      | l1_pre_topc(sK2) != iProver_top
% 2.78/1.03      | v1_funct_1(sK7) != iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3560,c_3668]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_34,negated_conjecture,
% 2.78/1.03      ( ~ v2_struct_0(sK2) ),
% 2.78/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_41,plain,
% 2.78/1.03      ( v2_struct_0(sK2) != iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_33,negated_conjecture,
% 2.78/1.03      ( v2_pre_topc(sK2) ),
% 2.78/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_42,plain,
% 2.78/1.03      ( v2_pre_topc(sK2) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_32,negated_conjecture,
% 2.78/1.03      ( l1_pre_topc(sK2) ),
% 2.78/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_43,plain,
% 2.78/1.03      ( l1_pre_topc(sK2) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_54,plain,
% 2.78/1.03      ( v1_funct_1(sK7) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3503,plain,
% 2.78/1.03      ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3549,plain,
% 2.78/1.03      ( v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 2.78/1.03      inference(light_normalisation,[status(thm)],[c_3503,c_18]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_6281,plain,
% 2.78/1.03      ( v2_pre_topc(X1) != iProver_top
% 2.78/1.03      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
% 2.78/1.03      | m1_pre_topc(X0,sK1) != iProver_top
% 2.78/1.03      | m1_pre_topc(sK1,X1) != iProver_top
% 2.78/1.03      | v2_struct_0(X1) = iProver_top
% 2.78/1.03      | l1_pre_topc(X1) != iProver_top ),
% 2.78/1.03      inference(global_propositional_subsumption,
% 2.78/1.03                [status(thm)],
% 2.78/1.03                [c_5647,c_41,c_42,c_43,c_54,c_3549]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_6282,plain,
% 2.78/1.03      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k3_tmap_1(X1,sK2,sK1,X0,sK7)
% 2.78/1.03      | m1_pre_topc(X0,sK1) != iProver_top
% 2.78/1.03      | m1_pre_topc(sK1,X1) != iProver_top
% 2.78/1.03      | v2_struct_0(X1) = iProver_top
% 2.78/1.03      | v2_pre_topc(X1) != iProver_top
% 2.78/1.03      | l1_pre_topc(X1) != iProver_top ),
% 2.78/1.03      inference(renaming,[status(thm)],[c_6281]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_6293,plain,
% 2.78/1.03      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k3_tmap_1(X0,sK2,sK1,sK3,sK7)
% 2.78/1.03      | m1_pre_topc(sK1,X0) != iProver_top
% 2.78/1.03      | v2_struct_0(X0) = iProver_top
% 2.78/1.03      | v2_pre_topc(X0) != iProver_top
% 2.78/1.03      | l1_pre_topc(X0) != iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3493,c_6282]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_12,plain,
% 2.78/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.78/1.03      | ~ m1_pre_topc(X3,X1)
% 2.78/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.78/1.03      | v2_struct_0(X1)
% 2.78/1.03      | v2_struct_0(X2)
% 2.78/1.03      | ~ v2_pre_topc(X2)
% 2.78/1.03      | ~ v2_pre_topc(X1)
% 2.78/1.03      | ~ l1_pre_topc(X2)
% 2.78/1.03      | ~ l1_pre_topc(X1)
% 2.78/1.03      | ~ v1_funct_1(X0)
% 2.78/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.78/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3509,plain,
% 2.78/1.03      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 2.78/1.03      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 2.78/1.03      | m1_pre_topc(X3,X0) != iProver_top
% 2.78/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 2.78/1.03      | v2_struct_0(X1) = iProver_top
% 2.78/1.03      | v2_struct_0(X0) = iProver_top
% 2.78/1.03      | v2_pre_topc(X1) != iProver_top
% 2.78/1.03      | v2_pre_topc(X0) != iProver_top
% 2.78/1.03      | l1_pre_topc(X1) != iProver_top
% 2.78/1.03      | l1_pre_topc(X0) != iProver_top
% 2.78/1.03      | v1_funct_1(X2) != iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_4989,plain,
% 2.78/1.03      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0)
% 2.78/1.03      | v1_funct_2(sK7,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 2.78/1.03      | m1_pre_topc(X0,sK1) != iProver_top
% 2.78/1.03      | v2_struct_0(sK1) = iProver_top
% 2.78/1.03      | v2_struct_0(sK2) = iProver_top
% 2.78/1.03      | v2_pre_topc(sK1) != iProver_top
% 2.78/1.03      | v2_pre_topc(sK2) != iProver_top
% 2.78/1.03      | l1_pre_topc(sK1) != iProver_top
% 2.78/1.03      | l1_pre_topc(sK2) != iProver_top
% 2.78/1.03      | v1_funct_1(sK7) != iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3560,c_3509]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_37,negated_conjecture,
% 2.78/1.03      ( ~ v2_struct_0(sK1) ),
% 2.78/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_38,plain,
% 2.78/1.03      ( v2_struct_0(sK1) != iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_36,negated_conjecture,
% 2.78/1.03      ( v2_pre_topc(sK1) ),
% 2.78/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_39,plain,
% 2.78/1.03      ( v2_pre_topc(sK1) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_35,negated_conjecture,
% 2.78/1.03      ( l1_pre_topc(sK1) ),
% 2.78/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_40,plain,
% 2.78/1.03      ( l1_pre_topc(sK1) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_5561,plain,
% 2.78/1.03      ( m1_pre_topc(X0,sK1) != iProver_top
% 2.78/1.03      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0) ),
% 2.78/1.03      inference(global_propositional_subsumption,
% 2.78/1.03                [status(thm)],
% 2.78/1.03                [c_4989,c_38,c_39,c_40,c_41,c_42,c_43,c_54,c_3549]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_5562,plain,
% 2.78/1.03      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(X0)) = k2_tmap_1(sK1,sK2,sK7,X0)
% 2.78/1.03      | m1_pre_topc(X0,sK1) != iProver_top ),
% 2.78/1.03      inference(renaming,[status(thm)],[c_5561]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_5569,plain,
% 2.78/1.03      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK2),sK7,u1_struct_0(sK3)) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3493,c_5562]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_6311,plain,
% 2.78/1.03      ( k3_tmap_1(X0,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
% 2.78/1.03      | m1_pre_topc(sK1,X0) != iProver_top
% 2.78/1.03      | v2_struct_0(X0) = iProver_top
% 2.78/1.03      | v2_pre_topc(X0) != iProver_top
% 2.78/1.03      | l1_pre_topc(X0) != iProver_top ),
% 2.78/1.03      inference(light_normalisation,[status(thm)],[c_6293,c_5569]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_7144,plain,
% 2.78/1.03      ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3)
% 2.78/1.03      | v2_struct_0(sK1) = iProver_top
% 2.78/1.03      | v2_pre_topc(sK1) != iProver_top
% 2.78/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 2.78/1.03      inference(superposition,[status(thm)],[c_3540,c_6311]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_7147,plain,
% 2.78/1.03      ( k3_tmap_1(sK1,sK2,sK1,sK3,sK7) = k2_tmap_1(sK1,sK2,sK7,sK3) ),
% 2.78/1.03      inference(global_propositional_subsumption,
% 2.78/1.03                [status(thm)],
% 2.78/1.03                [c_7144,c_38,c_39,c_40]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_16,negated_conjecture,
% 2.78/1.03      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
% 2.78/1.03      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
% 2.78/1.03      inference(cnf_transformation,[],[f78]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3505,plain,
% 2.78/1.03      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) = iProver_top
% 2.78/1.03      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3605,plain,
% 2.78/1.03      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) = iProver_top
% 2.78/1.03      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 2.78/1.03      inference(light_normalisation,[status(thm)],[c_3505,c_18]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_7150,plain,
% 2.78/1.03      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) = iProver_top
% 2.78/1.03      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 2.78/1.03      inference(demodulation,[status(thm)],[c_7147,c_3605]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_8787,plain,
% 2.78/1.03      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) = iProver_top ),
% 2.78/1.03      inference(demodulation,[status(thm)],[c_8776,c_7150]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_15,negated_conjecture,
% 2.78/1.03      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6)
% 2.78/1.03      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) ),
% 2.78/1.03      inference(cnf_transformation,[],[f79]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3506,plain,
% 2.78/1.03      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK4,sK3,sK7),sK6) != iProver_top
% 2.78/1.03      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 2.78/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_3618,plain,
% 2.78/1.03      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k3_tmap_1(sK1,sK2,sK1,sK3,sK7),sK6) != iProver_top
% 2.78/1.03      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 2.78/1.03      inference(light_normalisation,[status(thm)],[c_3506,c_18]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_7151,plain,
% 2.78/1.03      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK7,sK3),sK6) != iProver_top
% 2.78/1.03      | r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 2.78/1.03      inference(demodulation,[status(thm)],[c_7147,c_3618]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_8788,plain,
% 2.78/1.03      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),k2_tmap_1(sK1,sK2,sK5,sK3),sK6) != iProver_top ),
% 2.78/1.03      inference(demodulation,[status(thm)],[c_8776,c_7151]) ).
% 2.78/1.03  
% 2.78/1.03  cnf(c_8806,plain,
% 2.78/1.03      ( $false ),
% 2.78/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_8787,c_8788]) ).
% 2.78/1.03  
% 2.78/1.03  
% 2.78/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/1.03  
% 2.78/1.03  ------                               Statistics
% 2.78/1.03  
% 2.78/1.03  ------ General
% 2.78/1.03  
% 2.78/1.03  abstr_ref_over_cycles:                  0
% 2.78/1.03  abstr_ref_under_cycles:                 0
% 2.78/1.03  gc_basic_clause_elim:                   0
% 2.78/1.03  forced_gc_time:                         0
% 2.78/1.03  parsing_time:                           0.019
% 2.78/1.03  unif_index_cands_time:                  0.
% 2.78/1.03  unif_index_add_time:                    0.
% 2.78/1.03  orderings_time:                         0.
% 2.78/1.03  out_proof_time:                         0.01
% 2.78/1.03  total_time:                             0.235
% 2.78/1.03  num_of_symbols:                         57
% 2.78/1.03  num_of_terms:                           5590
% 2.78/1.03  
% 2.78/1.03  ------ Preprocessing
% 2.78/1.03  
% 2.78/1.03  num_of_splits:                          0
% 2.78/1.03  num_of_split_atoms:                     0
% 2.78/1.03  num_of_reused_defs:                     0
% 2.78/1.03  num_eq_ax_congr_red:                    22
% 2.78/1.03  num_of_sem_filtered_clauses:            1
% 2.78/1.03  num_of_subtypes:                        0
% 2.78/1.03  monotx_restored_types:                  0
% 2.78/1.03  sat_num_of_epr_types:                   0
% 2.78/1.03  sat_num_of_non_cyclic_types:            0
% 2.78/1.03  sat_guarded_non_collapsed_types:        0
% 2.78/1.03  num_pure_diseq_elim:                    0
% 2.78/1.03  simp_replaced_by:                       0
% 2.78/1.03  res_preprocessed:                       179
% 2.78/1.03  prep_upred:                             0
% 2.78/1.03  prep_unflattend:                        65
% 2.78/1.03  smt_new_axioms:                         0
% 2.78/1.03  pred_elim_cands:                        11
% 2.78/1.03  pred_elim:                              1
% 2.78/1.03  pred_elim_cl:                           2
% 2.78/1.03  pred_elim_cycles:                       8
% 2.78/1.03  merged_defs:                            16
% 2.78/1.03  merged_defs_ncl:                        0
% 2.78/1.03  bin_hyper_res:                          23
% 2.78/1.03  prep_cycles:                            4
% 2.78/1.03  pred_elim_time:                         0.031
% 2.78/1.03  splitting_time:                         0.
% 2.78/1.03  sem_filter_time:                        0.
% 2.78/1.03  monotx_time:                            0.
% 2.78/1.03  subtype_inf_time:                       0.
% 2.78/1.03  
% 2.78/1.03  ------ Problem properties
% 2.78/1.03  
% 2.78/1.03  clauses:                                35
% 2.78/1.03  conjectures:                            22
% 2.78/1.03  epr:                                    18
% 2.78/1.03  horn:                                   29
% 2.78/1.03  ground:                                 23
% 2.78/1.03  unary:                                  21
% 2.78/1.03  binary:                                 5
% 2.78/1.03  lits:                                   81
% 2.78/1.03  lits_eq:                                5
% 2.78/1.03  fd_pure:                                0
% 2.78/1.03  fd_pseudo:                              0
% 2.78/1.03  fd_cond:                                0
% 2.78/1.03  fd_pseudo_cond:                         1
% 2.78/1.03  ac_symbols:                             0
% 2.78/1.03  
% 2.78/1.03  ------ Propositional Solver
% 2.78/1.03  
% 2.78/1.03  prop_solver_calls:                      29
% 2.78/1.03  prop_fast_solver_calls:                 2021
% 2.78/1.03  smt_solver_calls:                       0
% 2.78/1.03  smt_fast_solver_calls:                  0
% 2.78/1.03  prop_num_of_clauses:                    2285
% 2.78/1.03  prop_preprocess_simplified:             7212
% 2.78/1.03  prop_fo_subsumed:                       87
% 2.78/1.03  prop_solver_time:                       0.
% 2.78/1.03  smt_solver_time:                        0.
% 2.78/1.03  smt_fast_solver_time:                   0.
% 2.78/1.03  prop_fast_solver_time:                  0.
% 2.78/1.03  prop_unsat_core_time:                   0.
% 2.78/1.03  
% 2.78/1.03  ------ QBF
% 2.78/1.03  
% 2.78/1.03  qbf_q_res:                              0
% 2.78/1.03  qbf_num_tautologies:                    0
% 2.78/1.03  qbf_prep_cycles:                        0
% 2.78/1.03  
% 2.78/1.03  ------ BMC1
% 2.78/1.03  
% 2.78/1.03  bmc1_current_bound:                     -1
% 2.78/1.03  bmc1_last_solved_bound:                 -1
% 2.78/1.03  bmc1_unsat_core_size:                   -1
% 2.78/1.03  bmc1_unsat_core_parents_size:           -1
% 2.78/1.03  bmc1_merge_next_fun:                    0
% 2.78/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.78/1.03  
% 2.78/1.03  ------ Instantiation
% 2.78/1.03  
% 2.78/1.03  inst_num_of_clauses:                    653
% 2.78/1.03  inst_num_in_passive:                    184
% 2.78/1.03  inst_num_in_active:                     458
% 2.78/1.03  inst_num_in_unprocessed:                12
% 2.78/1.03  inst_num_of_loops:                      470
% 2.78/1.03  inst_num_of_learning_restarts:          0
% 2.78/1.03  inst_num_moves_active_passive:          8
% 2.78/1.03  inst_lit_activity:                      0
% 2.78/1.03  inst_lit_activity_moves:                0
% 2.78/1.03  inst_num_tautologies:                   0
% 2.78/1.03  inst_num_prop_implied:                  0
% 2.78/1.03  inst_num_existing_simplified:           0
% 2.78/1.03  inst_num_eq_res_simplified:             0
% 2.78/1.03  inst_num_child_elim:                    0
% 2.78/1.03  inst_num_of_dismatching_blockings:      167
% 2.78/1.03  inst_num_of_non_proper_insts:           1005
% 2.78/1.03  inst_num_of_duplicates:                 0
% 2.78/1.03  inst_inst_num_from_inst_to_res:         0
% 2.78/1.03  inst_dismatching_checking_time:         0.
% 2.78/1.03  
% 2.78/1.03  ------ Resolution
% 2.78/1.03  
% 2.78/1.03  res_num_of_clauses:                     0
% 2.78/1.03  res_num_in_passive:                     0
% 2.78/1.03  res_num_in_active:                      0
% 2.78/1.03  res_num_of_loops:                       183
% 2.78/1.03  res_forward_subset_subsumed:            147
% 2.78/1.03  res_backward_subset_subsumed:           12
% 2.78/1.03  res_forward_subsumed:                   0
% 2.78/1.03  res_backward_subsumed:                  0
% 2.78/1.03  res_forward_subsumption_resolution:     8
% 2.78/1.03  res_backward_subsumption_resolution:    0
% 2.78/1.03  res_clause_to_clause_subsumption:       519
% 2.78/1.03  res_orphan_elimination:                 0
% 2.78/1.03  res_tautology_del:                      182
% 2.78/1.03  res_num_eq_res_simplified:              0
% 2.78/1.03  res_num_sel_changes:                    0
% 2.78/1.03  res_moves_from_active_to_pass:          0
% 2.78/1.03  
% 2.78/1.03  ------ Superposition
% 2.78/1.03  
% 2.78/1.03  sup_time_total:                         0.
% 2.78/1.03  sup_time_generating:                    0.
% 2.78/1.03  sup_time_sim_full:                      0.
% 2.78/1.03  sup_time_sim_immed:                     0.
% 2.78/1.03  
% 2.78/1.03  sup_num_of_clauses:                     78
% 2.78/1.03  sup_num_in_active:                      61
% 2.78/1.03  sup_num_in_passive:                     17
% 2.78/1.03  sup_num_of_loops:                       92
% 2.78/1.03  sup_fw_superposition:                   71
% 2.78/1.03  sup_bw_superposition:                   26
% 2.78/1.03  sup_immediate_simplified:               14
% 2.78/1.03  sup_given_eliminated:                   0
% 2.78/1.03  comparisons_done:                       0
% 2.78/1.03  comparisons_avoided:                    0
% 2.78/1.03  
% 2.78/1.03  ------ Simplifications
% 2.78/1.03  
% 2.78/1.03  
% 2.78/1.03  sim_fw_subset_subsumed:                 4
% 2.78/1.03  sim_bw_subset_subsumed:                 6
% 2.78/1.03  sim_fw_subsumed:                        6
% 2.78/1.03  sim_bw_subsumed:                        0
% 2.78/1.03  sim_fw_subsumption_res:                 2
% 2.78/1.03  sim_bw_subsumption_res:                 0
% 2.78/1.03  sim_tautology_del:                      4
% 2.78/1.03  sim_eq_tautology_del:                   1
% 2.78/1.03  sim_eq_res_simp:                        0
% 2.78/1.03  sim_fw_demodulated:                     0
% 2.78/1.03  sim_bw_demodulated:                     26
% 2.78/1.03  sim_light_normalised:                   10
% 2.78/1.03  sim_joinable_taut:                      0
% 2.78/1.03  sim_joinable_simp:                      0
% 2.78/1.03  sim_ac_normalised:                      0
% 2.78/1.03  sim_smt_subsumption:                    0
% 2.78/1.03  
%------------------------------------------------------------------------------
