%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:30 EST 2020

% Result     : Theorem 11.47s
% Output     : CNFRefutation 11.47s
% Verified   : 
% Statistics : Number of formulae       :  221 (1678 expanded)
%              Number of clauses        :  133 ( 374 expanded)
%              Number of leaves         :   28 ( 741 expanded)
%              Depth                    :   24
%              Number of atoms          : 1140 (22746 expanded)
%              Number of equality atoms :  204 (3368 expanded)
%              Maximal formula depth    :   32 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f35,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(flattening,[],[f35])).

fof(f47,plain,(
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
                                  | ~ r1_tarski(X5,u1_struct_0(X2))
                                  | ~ r2_hidden(X6,X5)
                                  | ~ v3_pre_topc(X5,X3)
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
    inference(nnf_transformation,[],[f36])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | X6 != X7
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X6,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(cnf_transformation,[],[f47])).

fof(f98,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X7)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)
      | ~ r1_tarski(X5,u1_struct_0(X2))
      | ~ r2_hidden(X7,X5)
      | ~ v3_pre_topc(X5,X3)
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
    inference(equality_resolution,[],[f78])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
    inference(flattening,[],[f37])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X3,X1,X4,X5)
          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X3,X1,X4,X5)
        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8)
        & sK8 = X5
        & m1_subset_1(sK8,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X3,X1,X4,X5)
              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X3,X1,X4,sK7)
            & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            & sK7 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK7,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(X3,X1,X4,X5)
                  & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(X2)) )
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(X3,X1,sK6,X5)
                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK6),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,X1,X4,X5)
                      & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(sK5,X1,X4,X5)
                    & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK5,X2,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK5)) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK5
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,X1,X4,X5)
                          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
                        ( ~ r1_tmap_1(X3,X1,X4,X5)
                        & r1_tmap_1(sK4,X1,k3_tmap_1(X0,X1,X3,sK4,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK4)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
                            ( ~ r1_tmap_1(X3,sK3,X4,X5)
                            & r1_tmap_1(X2,sK3,k3_tmap_1(X0,sK3,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X3,X1,X4,X5)
                                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
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

fof(f55,plain,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
    & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    & sK7 = sK8
    & m1_subset_1(sK8,u1_struct_0(sK4))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f38,f54,f53,f52,f51,f50,f49,f48])).

fof(f88,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f81,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f58,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f86,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,(
    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 ),
    inference(cnf_transformation,[],[f55])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK1(X0,X1,X2))
        & r1_tarski(sK1(X0,X1,X2),X2)
        & v3_pre_topc(sK1(X0,X1,X2),X0)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK1(X0,X1,X2))
                    & r1_tarski(sK1(X0,X1,X2),X2)
                    & v3_pre_topc(sK1(X0,X1,X2),X0)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK1(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f41])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f96,plain,(
    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f95,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f55])).

fof(f94,plain,(
    m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f97,plain,(
    ~ r1_tmap_1(sK5,sK3,sK6,sK7) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f79,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ r2_hidden(X3,X6)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3649,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK5,X0,X3),X4)
    | r1_tmap_1(sK5,X1,X3,X4)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
    | ~ r2_hidden(X4,sK1(sK5,sK7,sK0(sK5,sK7)))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,sK5)
    | ~ m1_pre_topc(sK5,X2)
    | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(sK5))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_6040,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK5,X0,sK6),X3)
    | r1_tmap_1(sK5,X1,sK6,X3)
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
    | ~ r2_hidden(X3,sK1(sK5,sK7,sK0(sK5,sK7)))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,sK5)
    | ~ m1_pre_topc(sK5,X2)
    | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK5))
    | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_3649])).

cnf(c_6939,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK5,X0,sK6),sK7)
    | r1_tmap_1(sK5,X1,sK6,sK7)
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
    | ~ r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,sK5)
    | ~ m1_pre_topc(sK5,X2)
    | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(X0))
    | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(X0))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_6040])).

cnf(c_21361,plain,
    ( ~ r1_tmap_1(sK4,X0,k3_tmap_1(X1,X0,sK5,sK4,sK6),sK7)
    | r1_tmap_1(sK5,X0,sK6,sK7)
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
    | ~ r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
    | ~ m1_pre_topc(sK4,X1)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ m1_pre_topc(sK5,X1)
    | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK4)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_6939])).

cnf(c_34395,plain,
    ( ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK2,X0,sK5,sK4,sK6),sK7)
    | r1_tmap_1(sK5,X0,sK6,sK7)
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(X0))
    | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
    | ~ r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_21361])).

cnf(c_34397,plain,
    ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7)
    | r1_tmap_1(sK5,sK3,sK6,sK7)
    | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
    | ~ r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK4,sK5)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_34395])).

cnf(c_471,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5264,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5))
    | X0 != sK1(sK5,sK7,sK0(sK5,sK7))
    | X1 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_471])).

cnf(c_8179,plain,
    ( r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),X0)
    | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5))
    | X0 != u1_struct_0(sK5)
    | sK1(sK5,sK7,sK0(sK5,sK7)) != sK1(sK5,sK7,sK0(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_5264])).

cnf(c_14148,plain,
    ( r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK4))
    | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5))
    | sK1(sK5,sK7,sK0(sK5,sK7)) != sK1(sK5,sK7,sK0(sK5,sK7))
    | u1_struct_0(sK4) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_8179])).

cnf(c_468,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_2439,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK5)
    | u1_struct_0(sK5) != X1 ),
    inference(instantiation,[status(thm)],[c_468])).

cnf(c_3137,plain,
    ( X0 != u1_struct_0(X1)
    | X0 = u1_struct_0(sK5)
    | u1_struct_0(sK5) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_2439])).

cnf(c_5286,plain,
    ( X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | X0 = u1_struct_0(sK5)
    | u1_struct_0(sK5) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_3137])).

cnf(c_7817,plain,
    ( u1_struct_0(sK4) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | u1_struct_0(sK4) = u1_struct_0(sK5)
    | u1_struct_0(sK5) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_5286])).

cnf(c_2599,plain,
    ( X0 != X1
    | u1_struct_0(sK4) != X1
    | u1_struct_0(sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_468])).

cnf(c_3199,plain,
    ( X0 != u1_struct_0(sK4)
    | u1_struct_0(sK4) = X0
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2599])).

cnf(c_6321,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(sK4)
    | u1_struct_0(sK4) = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3199])).

cnf(c_19,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1481,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1470,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1491,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2769,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1470,c_1491])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_44,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_2328,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK5) ),
    inference(resolution,[status(thm)],[c_4,c_32])).

cnf(c_2329,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2328])).

cnf(c_2855,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2769,c_44,c_2329])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1493,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3070,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK5
    | v1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2855,c_1493])).

cnf(c_34,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1468,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1482,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3336,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1482])).

cnf(c_28,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3339,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3336,c_28])).

cnf(c_3705,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3070,c_44,c_3339])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1488,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3435,plain,
    ( g1_pre_topc(X0,X1) != sK5
    | u1_struct_0(sK4) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1488])).

cnf(c_2330,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(resolution,[status(thm)],[c_4,c_34])).

cnf(c_2331,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2330])).

cnf(c_5,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2606,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2611,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2606])).

cnf(c_3436,plain,
    ( g1_pre_topc(X0,X1) != sK5
    | u1_struct_0(sK4) = X0
    | m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1488])).

cnf(c_3457,plain,
    ( u1_struct_0(sK4) = X0
    | g1_pre_topc(X0,X1) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3435,c_44,c_2331,c_2611,c_3436])).

cnf(c_3458,plain,
    ( g1_pre_topc(X0,X1) != sK5
    | u1_struct_0(sK4) = X0 ),
    inference(renaming,[status(thm)],[c_3457])).

cnf(c_3709,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK4) ),
    inference(superposition,[status(thm)],[c_3705,c_3458])).

cnf(c_3735,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK4)) = sK5 ),
    inference(demodulation,[status(thm)],[c_3709,c_28])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1489,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3971,plain,
    ( g1_pre_topc(X0,X1) != sK5
    | u1_pre_topc(sK4) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3735,c_1489])).

cnf(c_1490,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3744,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3709,c_1490])).

cnf(c_3973,plain,
    ( g1_pre_topc(X0,X1) != sK5
    | u1_pre_topc(sK4) = X1
    | m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3735,c_1489])).

cnf(c_4543,plain,
    ( u1_pre_topc(sK4) = X1
    | g1_pre_topc(X0,X1) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3971,c_44,c_2331,c_3744,c_3973])).

cnf(c_4544,plain,
    ( g1_pre_topc(X0,X1) != sK5
    | u1_pre_topc(sK4) = X1 ),
    inference(renaming,[status(thm)],[c_4543])).

cnf(c_4548,plain,
    ( u1_pre_topc(sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_3705,c_4544])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_386,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_4])).

cnf(c_387,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_386])).

cnf(c_1460,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_4717,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK5))) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4548,c_1460])).

cnf(c_4748,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(X0,sK5) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4717,c_3705,c_3709])).

cnf(c_6158,plain,
    ( m1_pre_topc(X0,sK5) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4748,c_44,c_2331])).

cnf(c_6159,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(X0,sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_6158])).

cnf(c_6167,plain,
    ( m1_pre_topc(sK4,sK5) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_6159])).

cnf(c_6184,plain,
    ( m1_pre_topc(sK4,sK5)
    | ~ l1_pre_topc(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6167])).

cnf(c_467,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5690,plain,
    ( sK1(sK5,sK7,sK0(sK5,sK7)) = sK1(sK5,sK7,sK0(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_472,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_3138,plain,
    ( u1_struct_0(sK5) = u1_struct_0(X0)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_472])).

cnf(c_4199,plain,
    ( u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | sK5 != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(instantiation,[status(thm)],[c_3138])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3640,plain,
    ( r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5))
    | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3389,plain,
    ( ~ l1_pre_topc(sK2)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(resolution,[status(thm)],[c_18,c_34])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3106,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_3,c_32])).

cnf(c_1960,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3048,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(instantiation,[status(thm)],[c_1960])).

cnf(c_2278,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | X1 = u1_struct_0(sK4)
    | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2605,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | X0 = u1_struct_0(sK4)
    | g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(instantiation,[status(thm)],[c_2278])).

cnf(c_3047,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2605])).

cnf(c_3040,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_2240,plain,
    ( X0 != X1
    | X0 = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 ),
    inference(instantiation,[status(thm)],[c_468])).

cnf(c_2813,plain,
    ( X0 = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | X0 != sK5
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != sK5 ),
    inference(instantiation,[status(thm)],[c_2240])).

cnf(c_3039,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != sK5
    | sK5 = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2813])).

cnf(c_476,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2572,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(sK5) ),
    inference(resolution,[status(thm)],[c_476,c_28])).

cnf(c_2289,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_16,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_10])).

cnf(c_431,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_430])).

cnf(c_2087,plain,
    ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
    | m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_13,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,sK1(X1,X2,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK1(X1,X2,X0))
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_10])).

cnf(c_422,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,sK1(X1,X2,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_421])).

cnf(c_2088,plain,
    ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
    | r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_422])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_10])).

cnf(c_404,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_403])).

cnf(c_2090,plain,
    ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
    | v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_11,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2030,plain,
    ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_24,negated_conjecture,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1476,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1537,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1476,c_25])).

cnf(c_1807,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1537])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1475,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1522,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1475,c_25])).

cnf(c_1800,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1522])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK7) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34397,c_14148,c_7817,c_6321,c_6184,c_5690,c_4199,c_3640,c_3389,c_3106,c_3048,c_3047,c_3040,c_3039,c_2606,c_2572,c_2330,c_2328,c_2289,c_2087,c_2088,c_2090,c_2030,c_1807,c_1800,c_23,c_27,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:44:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.47/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.47/1.98  
% 11.47/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.47/1.98  
% 11.47/1.98  ------  iProver source info
% 11.47/1.98  
% 11.47/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.47/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.47/1.98  git: non_committed_changes: false
% 11.47/1.98  git: last_make_outside_of_git: false
% 11.47/1.98  
% 11.47/1.98  ------ 
% 11.47/1.98  ------ Parsing...
% 11.47/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.47/1.98  
% 11.47/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.47/1.98  
% 11.47/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.47/1.98  
% 11.47/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.47/1.98  ------ Proving...
% 11.47/1.98  ------ Problem Properties 
% 11.47/1.98  
% 11.47/1.98  
% 11.47/1.98  clauses                                 42
% 11.47/1.98  conjectures                             19
% 11.47/1.98  EPR                                     17
% 11.47/1.98  Horn                                    33
% 11.47/1.98  unary                                   19
% 11.47/1.98  binary                                  4
% 11.47/1.98  lits                                    150
% 11.47/1.98  lits eq                                 7
% 11.47/1.98  fd_pure                                 0
% 11.47/1.98  fd_pseudo                               0
% 11.47/1.98  fd_cond                                 0
% 11.47/1.98  fd_pseudo_cond                          2
% 11.47/1.98  AC symbols                              0
% 11.47/1.98  
% 11.47/1.98  ------ Input Options Time Limit: Unbounded
% 11.47/1.98  
% 11.47/1.98  
% 11.47/1.98  ------ 
% 11.47/1.98  Current options:
% 11.47/1.98  ------ 
% 11.47/1.98  
% 11.47/1.98  
% 11.47/1.98  
% 11.47/1.98  
% 11.47/1.98  ------ Proving...
% 11.47/1.98  
% 11.47/1.98  
% 11.47/1.98  % SZS status Theorem for theBenchmark.p
% 11.47/1.98  
% 11.47/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.47/1.98  
% 11.47/1.98  fof(f14,axiom,(
% 11.47/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 11.47/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.98  
% 11.47/1.98  fof(f35,plain,(
% 11.47/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.47/1.98    inference(ennf_transformation,[],[f14])).
% 11.47/1.98  
% 11.47/1.98  fof(f36,plain,(
% 11.47/1.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.47/1.99    inference(flattening,[],[f35])).
% 11.47/1.99  
% 11.47/1.99  fof(f47,plain,(
% 11.47/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.47/1.99    inference(nnf_transformation,[],[f36])).
% 11.47/1.99  
% 11.47/1.99  fof(f78,plain,(
% 11.47/1.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f47])).
% 11.47/1.99  
% 11.47/1.99  fof(f98,plain,(
% 11.47/1.99    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.47/1.99    inference(equality_resolution,[],[f78])).
% 11.47/1.99  
% 11.47/1.99  fof(f12,axiom,(
% 11.47/1.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f32,plain,(
% 11.47/1.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 11.47/1.99    inference(ennf_transformation,[],[f12])).
% 11.47/1.99  
% 11.47/1.99  fof(f75,plain,(
% 11.47/1.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f32])).
% 11.47/1.99  
% 11.47/1.99  fof(f15,conjecture,(
% 11.47/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f16,negated_conjecture,(
% 11.47/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 11.47/1.99    inference(negated_conjecture,[],[f15])).
% 11.47/1.99  
% 11.47/1.99  fof(f37,plain,(
% 11.47/1.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.47/1.99    inference(ennf_transformation,[],[f16])).
% 11.47/1.99  
% 11.47/1.99  fof(f38,plain,(
% 11.47/1.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.47/1.99    inference(flattening,[],[f37])).
% 11.47/1.99  
% 11.47/1.99  fof(f54,plain,(
% 11.47/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK8) & sK8 = X5 & m1_subset_1(sK8,u1_struct_0(X2)))) )),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f53,plain,(
% 11.47/1.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK7) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f52,plain,(
% 11.47/1.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK6,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK6),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK6,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f51,plain,(
% 11.47/1.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK5,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK5,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK5 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f50,plain,(
% 11.47/1.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK4,X1,k3_tmap_1(X0,X1,X3,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f49,plain,(
% 11.47/1.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(X2,sK3,k3_tmap_1(X0,sK3,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f48,plain,(
% 11.47/1.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f55,plain,(
% 11.47/1.99    ((((((~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 11.47/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f38,f54,f53,f52,f51,f50,f49,f48])).
% 11.47/1.99  
% 11.47/1.99  fof(f88,plain,(
% 11.47/1.99    m1_pre_topc(sK5,sK2)),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f4,axiom,(
% 11.47/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f21,plain,(
% 11.47/1.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.47/1.99    inference(ennf_transformation,[],[f4])).
% 11.47/1.99  
% 11.47/1.99  fof(f60,plain,(
% 11.47/1.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f21])).
% 11.47/1.99  
% 11.47/1.99  fof(f81,plain,(
% 11.47/1.99    l1_pre_topc(sK2)),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f2,axiom,(
% 11.47/1.99    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f17,plain,(
% 11.47/1.99    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 11.47/1.99    inference(ennf_transformation,[],[f2])).
% 11.47/1.99  
% 11.47/1.99  fof(f18,plain,(
% 11.47/1.99    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 11.47/1.99    inference(flattening,[],[f17])).
% 11.47/1.99  
% 11.47/1.99  fof(f58,plain,(
% 11.47/1.99    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f18])).
% 11.47/1.99  
% 11.47/1.99  fof(f86,plain,(
% 11.47/1.99    m1_pre_topc(sK4,sK2)),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f11,axiom,(
% 11.47/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f31,plain,(
% 11.47/1.99    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.47/1.99    inference(ennf_transformation,[],[f11])).
% 11.47/1.99  
% 11.47/1.99  fof(f73,plain,(
% 11.47/1.99    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f31])).
% 11.47/1.99  
% 11.47/1.99  fof(f92,plain,(
% 11.47/1.99    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f6,axiom,(
% 11.47/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f23,plain,(
% 11.47/1.99    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 11.47/1.99    inference(ennf_transformation,[],[f6])).
% 11.47/1.99  
% 11.47/1.99  fof(f62,plain,(
% 11.47/1.99    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.47/1.99    inference(cnf_transformation,[],[f23])).
% 11.47/1.99  
% 11.47/1.99  fof(f5,axiom,(
% 11.47/1.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f22,plain,(
% 11.47/1.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.47/1.99    inference(ennf_transformation,[],[f5])).
% 11.47/1.99  
% 11.47/1.99  fof(f61,plain,(
% 11.47/1.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f22])).
% 11.47/1.99  
% 11.47/1.99  fof(f63,plain,(
% 11.47/1.99    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 11.47/1.99    inference(cnf_transformation,[],[f23])).
% 11.47/1.99  
% 11.47/1.99  fof(f7,axiom,(
% 11.47/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f24,plain,(
% 11.47/1.99    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.47/1.99    inference(ennf_transformation,[],[f7])).
% 11.47/1.99  
% 11.47/1.99  fof(f40,plain,(
% 11.47/1.99    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.47/1.99    inference(nnf_transformation,[],[f24])).
% 11.47/1.99  
% 11.47/1.99  fof(f64,plain,(
% 11.47/1.99    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f40])).
% 11.47/1.99  
% 11.47/1.99  fof(f1,axiom,(
% 11.47/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f39,plain,(
% 11.47/1.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.47/1.99    inference(nnf_transformation,[],[f1])).
% 11.47/1.99  
% 11.47/1.99  fof(f56,plain,(
% 11.47/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.47/1.99    inference(cnf_transformation,[],[f39])).
% 11.47/1.99  
% 11.47/1.99  fof(f3,axiom,(
% 11.47/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f19,plain,(
% 11.47/1.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.47/1.99    inference(ennf_transformation,[],[f3])).
% 11.47/1.99  
% 11.47/1.99  fof(f20,plain,(
% 11.47/1.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.47/1.99    inference(flattening,[],[f19])).
% 11.47/1.99  
% 11.47/1.99  fof(f59,plain,(
% 11.47/1.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f20])).
% 11.47/1.99  
% 11.47/1.99  fof(f10,axiom,(
% 11.47/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f29,plain,(
% 11.47/1.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.47/1.99    inference(ennf_transformation,[],[f10])).
% 11.47/1.99  
% 11.47/1.99  fof(f30,plain,(
% 11.47/1.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.47/1.99    inference(flattening,[],[f29])).
% 11.47/1.99  
% 11.47/1.99  fof(f43,plain,(
% 11.47/1.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.47/1.99    inference(nnf_transformation,[],[f30])).
% 11.47/1.99  
% 11.47/1.99  fof(f44,plain,(
% 11.47/1.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.47/1.99    inference(rectify,[],[f43])).
% 11.47/1.99  
% 11.47/1.99  fof(f45,plain,(
% 11.47/1.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f46,plain,(
% 11.47/1.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.47/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f44,f45])).
% 11.47/1.99  
% 11.47/1.99  fof(f68,plain,(
% 11.47/1.99    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f46])).
% 11.47/1.99  
% 11.47/1.99  fof(f8,axiom,(
% 11.47/1.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f25,plain,(
% 11.47/1.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.47/1.99    inference(ennf_transformation,[],[f8])).
% 11.47/1.99  
% 11.47/1.99  fof(f26,plain,(
% 11.47/1.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.47/1.99    inference(flattening,[],[f25])).
% 11.47/1.99  
% 11.47/1.99  fof(f66,plain,(
% 11.47/1.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f26])).
% 11.47/1.99  
% 11.47/1.99  fof(f71,plain,(
% 11.47/1.99    ( ! [X2,X0,X1] : (r2_hidden(X1,sK1(X0,X1,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f46])).
% 11.47/1.99  
% 11.47/1.99  fof(f69,plain,(
% 11.47/1.99    ( ! [X2,X0,X1] : (v3_pre_topc(sK1(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f46])).
% 11.47/1.99  
% 11.47/1.99  fof(f9,axiom,(
% 11.47/1.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 11.47/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.47/1.99  
% 11.47/1.99  fof(f27,plain,(
% 11.47/1.99    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.47/1.99    inference(ennf_transformation,[],[f9])).
% 11.47/1.99  
% 11.47/1.99  fof(f28,plain,(
% 11.47/1.99    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.47/1.99    inference(flattening,[],[f27])).
% 11.47/1.99  
% 11.47/1.99  fof(f41,plain,(
% 11.47/1.99    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 11.47/1.99    introduced(choice_axiom,[])).
% 11.47/1.99  
% 11.47/1.99  fof(f42,plain,(
% 11.47/1.99    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.47/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f41])).
% 11.47/1.99  
% 11.47/1.99  fof(f67,plain,(
% 11.47/1.99    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.47/1.99    inference(cnf_transformation,[],[f42])).
% 11.47/1.99  
% 11.47/1.99  fof(f96,plain,(
% 11.47/1.99    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f95,plain,(
% 11.47/1.99    sK7 = sK8),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f94,plain,(
% 11.47/1.99    m1_subset_1(sK8,u1_struct_0(sK4))),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f97,plain,(
% 11.47/1.99    ~r1_tmap_1(sK5,sK3,sK6,sK7)),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f93,plain,(
% 11.47/1.99    m1_subset_1(sK7,u1_struct_0(sK5))),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f91,plain,(
% 11.47/1.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f90,plain,(
% 11.47/1.99    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f89,plain,(
% 11.47/1.99    v1_funct_1(sK6)),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f87,plain,(
% 11.47/1.99    ~v2_struct_0(sK5)),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f85,plain,(
% 11.47/1.99    ~v2_struct_0(sK4)),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f84,plain,(
% 11.47/1.99    l1_pre_topc(sK3)),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f83,plain,(
% 11.47/1.99    v2_pre_topc(sK3)),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f82,plain,(
% 11.47/1.99    ~v2_struct_0(sK3)),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f80,plain,(
% 11.47/1.99    v2_pre_topc(sK2)),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  fof(f79,plain,(
% 11.47/1.99    ~v2_struct_0(sK2)),
% 11.47/1.99    inference(cnf_transformation,[],[f55])).
% 11.47/1.99  
% 11.47/1.99  cnf(c_21,plain,
% 11.47/1.99      ( r1_tmap_1(X0,X1,X2,X3)
% 11.47/1.99      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 11.47/1.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 11.47/1.99      | ~ v3_pre_topc(X6,X0)
% 11.47/1.99      | ~ r2_hidden(X3,X6)
% 11.47/1.99      | ~ m1_pre_topc(X0,X5)
% 11.47/1.99      | ~ m1_pre_topc(X4,X0)
% 11.47/1.99      | ~ m1_pre_topc(X4,X5)
% 11.47/1.99      | ~ r1_tarski(X6,u1_struct_0(X4))
% 11.47/1.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 11.47/1.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.47/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 11.47/1.99      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 11.47/1.99      | ~ v1_funct_1(X2)
% 11.47/1.99      | v2_struct_0(X5)
% 11.47/1.99      | v2_struct_0(X1)
% 11.47/1.99      | v2_struct_0(X4)
% 11.47/1.99      | v2_struct_0(X0)
% 11.47/1.99      | ~ v2_pre_topc(X5)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | ~ l1_pre_topc(X5)
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(cnf_transformation,[],[f98]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3649,plain,
% 11.47/1.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK5,X0,X3),X4)
% 11.47/1.99      | r1_tmap_1(sK5,X1,X3,X4)
% 11.47/1.99      | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
% 11.47/1.99      | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
% 11.47/1.99      | ~ r2_hidden(X4,sK1(sK5,sK7,sK0(sK5,sK7)))
% 11.47/1.99      | ~ m1_pre_topc(X0,X2)
% 11.47/1.99      | ~ m1_pre_topc(X0,sK5)
% 11.47/1.99      | ~ m1_pre_topc(sK5,X2)
% 11.47/1.99      | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(X0))
% 11.47/1.99      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 11.47/1.99      | ~ m1_subset_1(X4,u1_struct_0(sK5))
% 11.47/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 11.47/1.99      | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 11.47/1.99      | ~ v1_funct_1(X3)
% 11.47/1.99      | v2_struct_0(X1)
% 11.47/1.99      | v2_struct_0(X0)
% 11.47/1.99      | v2_struct_0(X2)
% 11.47/1.99      | v2_struct_0(sK5)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | ~ v2_pre_topc(X2)
% 11.47/1.99      | ~ l1_pre_topc(X1)
% 11.47/1.99      | ~ l1_pre_topc(X2) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_21]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_6040,plain,
% 11.47/1.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK5,X0,sK6),X3)
% 11.47/1.99      | r1_tmap_1(sK5,X1,sK6,X3)
% 11.47/1.99      | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(X1))
% 11.47/1.99      | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
% 11.47/1.99      | ~ r2_hidden(X3,sK1(sK5,sK7,sK0(sK5,sK7)))
% 11.47/1.99      | ~ m1_pre_topc(X0,X2)
% 11.47/1.99      | ~ m1_pre_topc(X0,sK5)
% 11.47/1.99      | ~ m1_pre_topc(sK5,X2)
% 11.47/1.99      | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(X0))
% 11.47/1.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 11.47/1.99      | ~ m1_subset_1(X3,u1_struct_0(sK5))
% 11.47/1.99      | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 11.47/1.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 11.47/1.99      | ~ v1_funct_1(sK6)
% 11.47/1.99      | v2_struct_0(X0)
% 11.47/1.99      | v2_struct_0(X1)
% 11.47/1.99      | v2_struct_0(X2)
% 11.47/1.99      | v2_struct_0(sK5)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | ~ v2_pre_topc(X2)
% 11.47/1.99      | ~ l1_pre_topc(X1)
% 11.47/1.99      | ~ l1_pre_topc(X2) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_3649]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_6939,plain,
% 11.47/1.99      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,sK5,X0,sK6),sK7)
% 11.47/1.99      | r1_tmap_1(sK5,X1,sK6,sK7)
% 11.47/1.99      | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(X1))
% 11.47/1.99      | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
% 11.47/1.99      | ~ r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
% 11.47/1.99      | ~ m1_pre_topc(X0,X2)
% 11.47/1.99      | ~ m1_pre_topc(X0,sK5)
% 11.47/1.99      | ~ m1_pre_topc(sK5,X2)
% 11.47/1.99      | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(X0))
% 11.47/1.99      | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 11.47/1.99      | ~ m1_subset_1(sK7,u1_struct_0(X0))
% 11.47/1.99      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 11.47/1.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 11.47/1.99      | ~ v1_funct_1(sK6)
% 11.47/1.99      | v2_struct_0(X0)
% 11.47/1.99      | v2_struct_0(X1)
% 11.47/1.99      | v2_struct_0(X2)
% 11.47/1.99      | v2_struct_0(sK5)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | ~ v2_pre_topc(X2)
% 11.47/1.99      | ~ l1_pre_topc(X1)
% 11.47/1.99      | ~ l1_pre_topc(X2) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_6040]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_21361,plain,
% 11.47/1.99      ( ~ r1_tmap_1(sK4,X0,k3_tmap_1(X1,X0,sK5,sK4,sK6),sK7)
% 11.47/1.99      | r1_tmap_1(sK5,X0,sK6,sK7)
% 11.47/1.99      | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(X0))
% 11.47/1.99      | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
% 11.47/1.99      | ~ r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
% 11.47/1.99      | ~ m1_pre_topc(sK4,X1)
% 11.47/1.99      | ~ m1_pre_topc(sK4,sK5)
% 11.47/1.99      | ~ m1_pre_topc(sK5,X1)
% 11.47/1.99      | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK4))
% 11.47/1.99      | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 11.47/1.99      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 11.47/1.99      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 11.47/1.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 11.47/1.99      | ~ v1_funct_1(sK6)
% 11.47/1.99      | v2_struct_0(X0)
% 11.47/1.99      | v2_struct_0(X1)
% 11.47/1.99      | v2_struct_0(sK4)
% 11.47/1.99      | v2_struct_0(sK5)
% 11.47/1.99      | ~ v2_pre_topc(X0)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | ~ l1_pre_topc(X0)
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_6939]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_34395,plain,
% 11.47/1.99      ( ~ r1_tmap_1(sK4,X0,k3_tmap_1(sK2,X0,sK5,sK4,sK6),sK7)
% 11.47/1.99      | r1_tmap_1(sK5,X0,sK6,sK7)
% 11.47/1.99      | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(X0))
% 11.47/1.99      | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
% 11.47/1.99      | ~ r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
% 11.47/1.99      | ~ m1_pre_topc(sK4,sK2)
% 11.47/1.99      | ~ m1_pre_topc(sK4,sK5)
% 11.47/1.99      | ~ m1_pre_topc(sK5,sK2)
% 11.47/1.99      | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK4))
% 11.47/1.99      | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 11.47/1.99      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 11.47/1.99      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 11.47/1.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 11.47/1.99      | ~ v1_funct_1(sK6)
% 11.47/1.99      | v2_struct_0(X0)
% 11.47/1.99      | v2_struct_0(sK2)
% 11.47/1.99      | v2_struct_0(sK4)
% 11.47/1.99      | v2_struct_0(sK5)
% 11.47/1.99      | ~ v2_pre_topc(X0)
% 11.47/1.99      | ~ v2_pre_topc(sK2)
% 11.47/1.99      | ~ l1_pre_topc(X0)
% 11.47/1.99      | ~ l1_pre_topc(sK2) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_21361]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_34397,plain,
% 11.47/1.99      ( ~ r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7)
% 11.47/1.99      | r1_tmap_1(sK5,sK3,sK6,sK7)
% 11.47/1.99      | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
% 11.47/1.99      | ~ v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
% 11.47/1.99      | ~ r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
% 11.47/1.99      | ~ m1_pre_topc(sK4,sK2)
% 11.47/1.99      | ~ m1_pre_topc(sK4,sK5)
% 11.47/1.99      | ~ m1_pre_topc(sK5,sK2)
% 11.47/1.99      | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK4))
% 11.47/1.99      | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 11.47/1.99      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 11.47/1.99      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 11.47/1.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 11.47/1.99      | ~ v1_funct_1(sK6)
% 11.47/1.99      | v2_struct_0(sK2)
% 11.47/1.99      | v2_struct_0(sK4)
% 11.47/1.99      | v2_struct_0(sK3)
% 11.47/1.99      | v2_struct_0(sK5)
% 11.47/1.99      | ~ v2_pre_topc(sK2)
% 11.47/1.99      | ~ v2_pre_topc(sK3)
% 11.47/1.99      | ~ l1_pre_topc(sK2)
% 11.47/1.99      | ~ l1_pre_topc(sK3) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_34395]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_471,plain,
% 11.47/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.47/1.99      theory(equality) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_5264,plain,
% 11.47/1.99      ( r1_tarski(X0,X1)
% 11.47/1.99      | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5))
% 11.47/1.99      | X0 != sK1(sK5,sK7,sK0(sK5,sK7))
% 11.47/1.99      | X1 != u1_struct_0(sK5) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_471]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_8179,plain,
% 11.47/1.99      ( r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),X0)
% 11.47/1.99      | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5))
% 11.47/1.99      | X0 != u1_struct_0(sK5)
% 11.47/1.99      | sK1(sK5,sK7,sK0(sK5,sK7)) != sK1(sK5,sK7,sK0(sK5,sK7)) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_5264]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_14148,plain,
% 11.47/1.99      ( r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK4))
% 11.47/1.99      | ~ r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5))
% 11.47/1.99      | sK1(sK5,sK7,sK0(sK5,sK7)) != sK1(sK5,sK7,sK0(sK5,sK7))
% 11.47/1.99      | u1_struct_0(sK4) != u1_struct_0(sK5) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_8179]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_468,plain,( X0 != X1 | X2 != X1 | X0 = X2 ),theory(equality) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2439,plain,
% 11.47/1.99      ( X0 != X1 | X0 = u1_struct_0(sK5) | u1_struct_0(sK5) != X1 ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_468]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3137,plain,
% 11.47/1.99      ( X0 != u1_struct_0(X1)
% 11.47/1.99      | X0 = u1_struct_0(sK5)
% 11.47/1.99      | u1_struct_0(sK5) != u1_struct_0(X1) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_2439]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_5286,plain,
% 11.47/1.99      ( X0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 11.47/1.99      | X0 = u1_struct_0(sK5)
% 11.47/1.99      | u1_struct_0(sK5) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_3137]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_7817,plain,
% 11.47/1.99      ( u1_struct_0(sK4) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 11.47/1.99      | u1_struct_0(sK4) = u1_struct_0(sK5)
% 11.47/1.99      | u1_struct_0(sK5) != u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_5286]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2599,plain,
% 11.47/1.99      ( X0 != X1 | u1_struct_0(sK4) != X1 | u1_struct_0(sK4) = X0 ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_468]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3199,plain,
% 11.47/1.99      ( X0 != u1_struct_0(sK4)
% 11.47/1.99      | u1_struct_0(sK4) = X0
% 11.47/1.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_2599]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_6321,plain,
% 11.47/1.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != u1_struct_0(sK4)
% 11.47/1.99      | u1_struct_0(sK4) = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 11.47/1.99      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_3199]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_19,plain,
% 11.47/1.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 11.47/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1481,plain,
% 11.47/1.99      ( m1_pre_topc(X0,X0) = iProver_top
% 11.47/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_32,negated_conjecture,
% 11.47/1.99      ( m1_pre_topc(sK5,sK2) ),
% 11.47/1.99      inference(cnf_transformation,[],[f88]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1470,plain,
% 11.47/1.99      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_4,plain,
% 11.47/1.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 11.47/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1491,plain,
% 11.47/1.99      ( m1_pre_topc(X0,X1) != iProver_top
% 11.47/1.99      | l1_pre_topc(X1) != iProver_top
% 11.47/1.99      | l1_pre_topc(X0) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2769,plain,
% 11.47/1.99      ( l1_pre_topc(sK2) != iProver_top
% 11.47/1.99      | l1_pre_topc(sK5) = iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_1470,c_1491]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_39,negated_conjecture,
% 11.47/1.99      ( l1_pre_topc(sK2) ),
% 11.47/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_44,plain,
% 11.47/1.99      ( l1_pre_topc(sK2) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2328,plain,
% 11.47/1.99      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK5) ),
% 11.47/1.99      inference(resolution,[status(thm)],[c_4,c_32]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2329,plain,
% 11.47/1.99      ( l1_pre_topc(sK2) != iProver_top
% 11.47/1.99      | l1_pre_topc(sK5) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_2328]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2855,plain,
% 11.47/1.99      ( l1_pre_topc(sK5) = iProver_top ),
% 11.47/1.99      inference(global_propositional_subsumption,
% 11.47/1.99                [status(thm)],
% 11.47/1.99                [c_2769,c_44,c_2329]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2,plain,
% 11.47/1.99      ( ~ l1_pre_topc(X0)
% 11.47/1.99      | ~ v1_pre_topc(X0)
% 11.47/1.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 11.47/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1493,plain,
% 11.47/1.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 11.47/1.99      | l1_pre_topc(X0) != iProver_top
% 11.47/1.99      | v1_pre_topc(X0) != iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3070,plain,
% 11.47/1.99      ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK5
% 11.47/1.99      | v1_pre_topc(sK5) != iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_2855,c_1493]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_34,negated_conjecture,
% 11.47/1.99      ( m1_pre_topc(sK4,sK2) ),
% 11.47/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1468,plain,
% 11.47/1.99      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_18,plain,
% 11.47/1.99      ( ~ m1_pre_topc(X0,X1)
% 11.47/1.99      | ~ l1_pre_topc(X1)
% 11.47/1.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 11.47/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1482,plain,
% 11.47/1.99      ( m1_pre_topc(X0,X1) != iProver_top
% 11.47/1.99      | l1_pre_topc(X1) != iProver_top
% 11.47/1.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3336,plain,
% 11.47/1.99      ( l1_pre_topc(sK2) != iProver_top
% 11.47/1.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_1468,c_1482]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_28,negated_conjecture,
% 11.47/1.99      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 ),
% 11.47/1.99      inference(cnf_transformation,[],[f92]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3339,plain,
% 11.47/1.99      ( l1_pre_topc(sK2) != iProver_top
% 11.47/1.99      | v1_pre_topc(sK5) = iProver_top ),
% 11.47/1.99      inference(light_normalisation,[status(thm)],[c_3336,c_28]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3705,plain,
% 11.47/1.99      ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK5 ),
% 11.47/1.99      inference(global_propositional_subsumption,
% 11.47/1.99                [status(thm)],
% 11.47/1.99                [c_3070,c_44,c_3339]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_7,plain,
% 11.47/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.47/1.99      | X2 = X1
% 11.47/1.99      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 11.47/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1488,plain,
% 11.47/1.99      ( X0 = X1
% 11.47/1.99      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 11.47/1.99      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3435,plain,
% 11.47/1.99      ( g1_pre_topc(X0,X1) != sK5
% 11.47/1.99      | u1_struct_0(sK4) = X0
% 11.47/1.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_28,c_1488]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2330,plain,
% 11.47/1.99      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 11.47/1.99      inference(resolution,[status(thm)],[c_4,c_34]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2331,plain,
% 11.47/1.99      ( l1_pre_topc(sK2) != iProver_top
% 11.47/1.99      | l1_pre_topc(sK4) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_2330]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_5,plain,
% 11.47/1.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 11.47/1.99      | ~ l1_pre_topc(X0) ),
% 11.47/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2606,plain,
% 11.47/1.99      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 11.47/1.99      | ~ l1_pre_topc(sK4) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2611,plain,
% 11.47/1.99      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
% 11.47/1.99      | l1_pre_topc(sK4) != iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_2606]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3436,plain,
% 11.47/1.99      ( g1_pre_topc(X0,X1) != sK5
% 11.47/1.99      | u1_struct_0(sK4) = X0
% 11.47/1.99      | m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_28,c_1488]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3457,plain,
% 11.47/1.99      ( u1_struct_0(sK4) = X0 | g1_pre_topc(X0,X1) != sK5 ),
% 11.47/1.99      inference(global_propositional_subsumption,
% 11.47/1.99                [status(thm)],
% 11.47/1.99                [c_3435,c_44,c_2331,c_2611,c_3436]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3458,plain,
% 11.47/1.99      ( g1_pre_topc(X0,X1) != sK5 | u1_struct_0(sK4) = X0 ),
% 11.47/1.99      inference(renaming,[status(thm)],[c_3457]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3709,plain,
% 11.47/1.99      ( u1_struct_0(sK5) = u1_struct_0(sK4) ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_3705,c_3458]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3735,plain,
% 11.47/1.99      ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK4)) = sK5 ),
% 11.47/1.99      inference(demodulation,[status(thm)],[c_3709,c_28]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_6,plain,
% 11.47/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 11.47/1.99      | X2 = X0
% 11.47/1.99      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 11.47/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1489,plain,
% 11.47/1.99      ( X0 = X1
% 11.47/1.99      | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
% 11.47/1.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3971,plain,
% 11.47/1.99      ( g1_pre_topc(X0,X1) != sK5
% 11.47/1.99      | u1_pre_topc(sK4) = X1
% 11.47/1.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_3735,c_1489]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1490,plain,
% 11.47/1.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 11.47/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3744,plain,
% 11.47/1.99      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
% 11.47/1.99      | l1_pre_topc(sK4) != iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_3709,c_1490]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3973,plain,
% 11.47/1.99      ( g1_pre_topc(X0,X1) != sK5
% 11.47/1.99      | u1_pre_topc(sK4) = X1
% 11.47/1.99      | m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_3735,c_1489]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_4543,plain,
% 11.47/1.99      ( u1_pre_topc(sK4) = X1 | g1_pre_topc(X0,X1) != sK5 ),
% 11.47/1.99      inference(global_propositional_subsumption,
% 11.47/1.99                [status(thm)],
% 11.47/1.99                [c_3971,c_44,c_2331,c_3744,c_3973]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_4544,plain,
% 11.47/1.99      ( g1_pre_topc(X0,X1) != sK5 | u1_pre_topc(sK4) = X1 ),
% 11.47/1.99      inference(renaming,[status(thm)],[c_4543]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_4548,plain,
% 11.47/1.99      ( u1_pre_topc(sK5) = u1_pre_topc(sK4) ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_3705,c_4544]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_9,plain,
% 11.47/1.99      ( ~ m1_pre_topc(X0,X1)
% 11.47/1.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.47/1.99      | ~ l1_pre_topc(X0)
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_386,plain,
% 11.47/1.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.47/1.99      | ~ m1_pre_topc(X0,X1)
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(global_propositional_subsumption,[status(thm)],[c_9,c_4]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_387,plain,
% 11.47/1.99      ( ~ m1_pre_topc(X0,X1)
% 11.47/1.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(renaming,[status(thm)],[c_386]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1460,plain,
% 11.47/1.99      ( m1_pre_topc(X0,X1) != iProver_top
% 11.47/1.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 11.47/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_4717,plain,
% 11.47/1.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK5))) = iProver_top
% 11.47/1.99      | m1_pre_topc(X0,sK4) != iProver_top
% 11.47/1.99      | l1_pre_topc(sK4) != iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_4548,c_1460]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_4748,plain,
% 11.47/1.99      ( m1_pre_topc(X0,sK4) != iProver_top
% 11.47/1.99      | m1_pre_topc(X0,sK5) = iProver_top
% 11.47/1.99      | l1_pre_topc(sK4) != iProver_top ),
% 11.47/1.99      inference(light_normalisation,[status(thm)],[c_4717,c_3705,c_3709]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_6158,plain,
% 11.47/1.99      ( m1_pre_topc(X0,sK5) = iProver_top
% 11.47/1.99      | m1_pre_topc(X0,sK4) != iProver_top ),
% 11.47/1.99      inference(global_propositional_subsumption,
% 11.47/1.99                [status(thm)],
% 11.47/1.99                [c_4748,c_44,c_2331]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_6159,plain,
% 11.47/1.99      ( m1_pre_topc(X0,sK4) != iProver_top
% 11.47/1.99      | m1_pre_topc(X0,sK5) = iProver_top ),
% 11.47/1.99      inference(renaming,[status(thm)],[c_6158]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_6167,plain,
% 11.47/1.99      ( m1_pre_topc(sK4,sK5) = iProver_top
% 11.47/1.99      | l1_pre_topc(sK4) != iProver_top ),
% 11.47/1.99      inference(superposition,[status(thm)],[c_1481,c_6159]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_6184,plain,
% 11.47/1.99      ( m1_pre_topc(sK4,sK5) | ~ l1_pre_topc(sK4) ),
% 11.47/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_6167]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_467,plain,( X0 = X0 ),theory(equality) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_5690,plain,
% 11.47/1.99      ( sK1(sK5,sK7,sK0(sK5,sK7)) = sK1(sK5,sK7,sK0(sK5,sK7)) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_467]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_472,plain,
% 11.47/1.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 11.47/1.99      theory(equality) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3138,plain,
% 11.47/1.99      ( u1_struct_0(sK5) = u1_struct_0(X0) | sK5 != X0 ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_472]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_4199,plain,
% 11.47/1.99      ( u1_struct_0(sK5) = u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 11.47/1.99      | sK5 != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_3138]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1,plain,
% 11.47/1.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.47/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3640,plain,
% 11.47/1.99      ( r1_tarski(sK1(sK5,sK7,sK0(sK5,sK7)),u1_struct_0(sK5))
% 11.47/1.99      | ~ m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3389,plain,
% 11.47/1.99      ( ~ l1_pre_topc(sK2)
% 11.47/1.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 11.47/1.99      inference(resolution,[status(thm)],[c_18,c_34]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3,plain,
% 11.47/1.99      ( ~ m1_pre_topc(X0,X1)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | v2_pre_topc(X0)
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3106,plain,
% 11.47/1.99      ( ~ v2_pre_topc(sK2) | v2_pre_topc(sK5) | ~ l1_pre_topc(sK2) ),
% 11.47/1.99      inference(resolution,[status(thm)],[c_3,c_32]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1960,plain,
% 11.47/1.99      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 11.47/1.99      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 11.47/1.99      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3048,plain,
% 11.47/1.99      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 11.47/1.99      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 11.47/1.99      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_1960]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2278,plain,
% 11.47/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 11.47/1.99      | X1 = u1_struct_0(sK4)
% 11.47/1.99      | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK4),X0) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2605,plain,
% 11.47/1.99      ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 11.47/1.99      | X0 = u1_struct_0(sK4)
% 11.47/1.99      | g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_2278]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3047,plain,
% 11.47/1.99      ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 11.47/1.99      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
% 11.47/1.99      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(sK4) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_2605]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3040,plain,
% 11.47/1.99      ( sK5 = sK5 ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_467]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2240,plain,
% 11.47/1.99      ( X0 != X1
% 11.47/1.99      | X0 = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
% 11.47/1.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_468]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2813,plain,
% 11.47/1.99      ( X0 = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
% 11.47/1.99      | X0 != sK5
% 11.47/1.99      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != sK5 ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_2240]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_3039,plain,
% 11.47/1.99      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != sK5
% 11.47/1.99      | sK5 = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
% 11.47/1.99      | sK5 != sK5 ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_2813]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_476,plain,
% 11.47/1.99      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 11.47/1.99      theory(equality) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2572,plain,
% 11.47/1.99      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 11.47/1.99      | ~ l1_pre_topc(sK5) ),
% 11.47/1.99      inference(resolution,[status(thm)],[c_476,c_28]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2289,plain,
% 11.47/1.99      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_467]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_16,plain,
% 11.47/1.99      ( ~ m1_connsp_2(X0,X1,X2)
% 11.47/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.47/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.47/1.99      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.47/1.99      | v2_struct_0(X1)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_10,plain,
% 11.47/1.99      ( ~ m1_connsp_2(X0,X1,X2)
% 11.47/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.47/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.47/1.99      | v2_struct_0(X1)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_430,plain,
% 11.47/1.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.47/1.99      | ~ m1_connsp_2(X0,X1,X2)
% 11.47/1.99      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.47/1.99      | v2_struct_0(X1)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(global_propositional_subsumption,
% 11.47/1.99                [status(thm)],
% 11.47/1.99                [c_16,c_10]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_431,plain,
% 11.47/1.99      ( ~ m1_connsp_2(X0,X1,X2)
% 11.47/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.47/1.99      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.47/1.99      | v2_struct_0(X1)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(renaming,[status(thm)],[c_430]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2087,plain,
% 11.47/1.99      ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
% 11.47/1.99      | m1_subset_1(sK1(sK5,sK7,sK0(sK5,sK7)),k1_zfmisc_1(u1_struct_0(sK5)))
% 11.47/1.99      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 11.47/1.99      | v2_struct_0(sK5)
% 11.47/1.99      | ~ v2_pre_topc(sK5)
% 11.47/1.99      | ~ l1_pre_topc(sK5) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_431]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_13,plain,
% 11.47/1.99      ( ~ m1_connsp_2(X0,X1,X2)
% 11.47/1.99      | r2_hidden(X2,sK1(X1,X2,X0))
% 11.47/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.47/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.47/1.99      | v2_struct_0(X1)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_421,plain,
% 11.47/1.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.47/1.99      | r2_hidden(X2,sK1(X1,X2,X0))
% 11.47/1.99      | ~ m1_connsp_2(X0,X1,X2)
% 11.47/1.99      | v2_struct_0(X1)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(global_propositional_subsumption,
% 11.47/1.99                [status(thm)],
% 11.47/1.99                [c_13,c_10]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_422,plain,
% 11.47/1.99      ( ~ m1_connsp_2(X0,X1,X2)
% 11.47/1.99      | r2_hidden(X2,sK1(X1,X2,X0))
% 11.47/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.47/1.99      | v2_struct_0(X1)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(renaming,[status(thm)],[c_421]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2088,plain,
% 11.47/1.99      ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
% 11.47/1.99      | r2_hidden(sK7,sK1(sK5,sK7,sK0(sK5,sK7)))
% 11.47/1.99      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 11.47/1.99      | v2_struct_0(sK5)
% 11.47/1.99      | ~ v2_pre_topc(sK5)
% 11.47/1.99      | ~ l1_pre_topc(sK5) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_422]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_15,plain,
% 11.47/1.99      ( ~ m1_connsp_2(X0,X1,X2)
% 11.47/1.99      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 11.47/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.47/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.47/1.99      | v2_struct_0(X1)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_403,plain,
% 11.47/1.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.47/1.99      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 11.47/1.99      | ~ m1_connsp_2(X0,X1,X2)
% 11.47/1.99      | v2_struct_0(X1)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(global_propositional_subsumption,
% 11.47/1.99                [status(thm)],
% 11.47/1.99                [c_15,c_10]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_404,plain,
% 11.47/1.99      ( ~ m1_connsp_2(X0,X1,X2)
% 11.47/1.99      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 11.47/1.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.47/1.99      | v2_struct_0(X1)
% 11.47/1.99      | ~ v2_pre_topc(X1)
% 11.47/1.99      | ~ l1_pre_topc(X1) ),
% 11.47/1.99      inference(renaming,[status(thm)],[c_403]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2090,plain,
% 11.47/1.99      ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
% 11.47/1.99      | v3_pre_topc(sK1(sK5,sK7,sK0(sK5,sK7)),sK5)
% 11.47/1.99      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 11.47/1.99      | v2_struct_0(sK5)
% 11.47/1.99      | ~ v2_pre_topc(sK5)
% 11.47/1.99      | ~ l1_pre_topc(sK5) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_404]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_11,plain,
% 11.47/1.99      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 11.47/1.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 11.47/1.99      | v2_struct_0(X0)
% 11.47/1.99      | ~ v2_pre_topc(X0)
% 11.47/1.99      | ~ l1_pre_topc(X0) ),
% 11.47/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_2030,plain,
% 11.47/1.99      ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
% 11.47/1.99      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 11.47/1.99      | v2_struct_0(sK5)
% 11.47/1.99      | ~ v2_pre_topc(sK5)
% 11.47/1.99      | ~ l1_pre_topc(sK5) ),
% 11.47/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_24,negated_conjecture,
% 11.47/1.99      ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
% 11.47/1.99      inference(cnf_transformation,[],[f96]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1476,plain,
% 11.47/1.99      ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_25,negated_conjecture,
% 11.47/1.99      ( sK7 = sK8 ),
% 11.47/1.99      inference(cnf_transformation,[],[f95]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1537,plain,
% 11.47/1.99      ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) = iProver_top ),
% 11.47/1.99      inference(light_normalisation,[status(thm)],[c_1476,c_25]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1807,plain,
% 11.47/1.99      ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) ),
% 11.47/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_1537]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_26,negated_conjecture,
% 11.47/1.99      ( m1_subset_1(sK8,u1_struct_0(sK4)) ),
% 11.47/1.99      inference(cnf_transformation,[],[f94]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1475,plain,
% 11.47/1.99      ( m1_subset_1(sK8,u1_struct_0(sK4)) = iProver_top ),
% 11.47/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1522,plain,
% 11.47/1.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 11.47/1.99      inference(light_normalisation,[status(thm)],[c_1475,c_25]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_1800,plain,
% 11.47/1.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 11.47/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_1522]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_23,negated_conjecture,
% 11.47/1.99      ( ~ r1_tmap_1(sK5,sK3,sK6,sK7) ),
% 11.47/1.99      inference(cnf_transformation,[],[f97]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_27,negated_conjecture,
% 11.47/1.99      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 11.47/1.99      inference(cnf_transformation,[],[f93]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_29,negated_conjecture,
% 11.47/1.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 11.47/1.99      inference(cnf_transformation,[],[f91]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_30,negated_conjecture,
% 11.47/1.99      ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 11.47/1.99      inference(cnf_transformation,[],[f90]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_31,negated_conjecture,
% 11.47/1.99      ( v1_funct_1(sK6) ),
% 11.47/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_33,negated_conjecture,
% 11.47/1.99      ( ~ v2_struct_0(sK5) ),
% 11.47/1.99      inference(cnf_transformation,[],[f87]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_35,negated_conjecture,
% 11.47/1.99      ( ~ v2_struct_0(sK4) ),
% 11.47/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_36,negated_conjecture,
% 11.47/1.99      ( l1_pre_topc(sK3) ),
% 11.47/1.99      inference(cnf_transformation,[],[f84]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_37,negated_conjecture,
% 11.47/1.99      ( v2_pre_topc(sK3) ),
% 11.47/1.99      inference(cnf_transformation,[],[f83]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_38,negated_conjecture,
% 11.47/1.99      ( ~ v2_struct_0(sK3) ),
% 11.47/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_40,negated_conjecture,
% 11.47/1.99      ( v2_pre_topc(sK2) ),
% 11.47/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(c_41,negated_conjecture,
% 11.47/1.99      ( ~ v2_struct_0(sK2) ),
% 11.47/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.47/1.99  
% 11.47/1.99  cnf(contradiction,plain,
% 11.47/1.99      ( $false ),
% 11.47/1.99      inference(minisat,
% 11.47/1.99                [status(thm)],
% 11.47/1.99                [c_34397,c_14148,c_7817,c_6321,c_6184,c_5690,c_4199,
% 11.47/1.99                 c_3640,c_3389,c_3106,c_3048,c_3047,c_3040,c_3039,c_2606,
% 11.47/1.99                 c_2572,c_2330,c_2328,c_2289,c_2087,c_2088,c_2090,c_2030,
% 11.47/1.99                 c_1807,c_1800,c_23,c_27,c_28,c_29,c_30,c_31,c_32,c_33,
% 11.47/1.99                 c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_41]) ).
% 11.47/1.99  
% 11.47/1.99  
% 11.47/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.47/1.99  
% 11.47/1.99  ------                               Statistics
% 11.47/1.99  
% 11.47/1.99  ------ Selected
% 11.47/1.99  
% 11.47/1.99  total_time:                             1.051
% 11.47/1.99  
%------------------------------------------------------------------------------
