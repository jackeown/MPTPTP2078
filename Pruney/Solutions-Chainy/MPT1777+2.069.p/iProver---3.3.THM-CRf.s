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
% DateTime   : Thu Dec  3 12:23:39 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 853 expanded)
%              Number of clauses        :  121 ( 217 expanded)
%              Number of leaves         :   21 ( 357 expanded)
%              Depth                    :   24
%              Number of atoms          : 1108 (11439 expanded)
%              Number of equality atoms :  273 (1709 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X3,X1,X4,X5)
          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X3,X1,X4,X5)
        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6)
        & sK6 = X5
        & m1_subset_1(sK6,u1_struct_0(X2)) ) ) ),
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
            ( ~ r1_tmap_1(X3,X1,X4,sK5)
            & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            & sK5 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
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
                ( ~ r1_tmap_1(X3,X1,sK4,X5)
                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
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
                    ( ~ r1_tmap_1(sK3,X1,X4,X5)
                    & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
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
                        & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
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
                            ( ~ r1_tmap_1(X3,sK1,X4,X5)
                            & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
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

fof(f55,plain,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5)
    & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f43,f54,f53,f52,f51,f50,f49,f48])).

fof(f90,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f86,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f55])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(flattening,[],[f40])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X1,X4,X5)
                                  | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
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
    inference(nnf_transformation,[],[f41])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X5)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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

fof(f99,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
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
    inference(equality_resolution,[],[f76])).

fof(f88,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f77,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f95,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_6,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_14,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_216,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_14])).

cnf(c_420,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | X1 != X2
    | u1_struct_0(X0) != k2_struct_0(X2) ),
    inference(resolution_lifted,[status(thm)],[c_6,c_216])).

cnf(c_421,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_829,plain,
    ( v1_tsep_1(X0_55,X1_55)
    | ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v2_pre_topc(X1_55)
    | u1_struct_0(X0_55) != k2_struct_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_6271,plain,
    ( v1_tsep_1(sK2,X0_55)
    | ~ m1_pre_topc(sK2,X0_55)
    | ~ l1_pre_topc(X0_55)
    | ~ v2_pre_topc(X0_55)
    | u1_struct_0(sK2) != k2_struct_0(X0_55) ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_15014,plain,
    ( v1_tsep_1(sK2,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(sK2) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6271])).

cnf(c_16,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_850,plain,
    ( m1_pre_topc(X0_55,X0_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1411,plain,
    ( m1_pre_topc(X0_55,X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_843,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_226,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_3])).

cnf(c_227,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_226])).

cnf(c_831,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_227])).

cnf(c_1428,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_3876,plain,
    ( m1_pre_topc(X0_55,sK2) != iProver_top
    | m1_pre_topc(X0_55,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_843,c_1428])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_42,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_839,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1420,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_856,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1405,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_2231,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_1405])).

cnf(c_4006,plain,
    ( m1_pre_topc(X0_55,sK3) = iProver_top
    | m1_pre_topc(X0_55,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3876,c_42,c_2231])).

cnf(c_4007,plain,
    ( m1_pre_topc(X0_55,sK2) != iProver_top
    | m1_pre_topc(X0_55,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4006])).

cnf(c_4014,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_4007])).

cnf(c_4553,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4014,c_42,c_2231])).

cnf(c_4,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_855,plain,
    ( m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1406,plain,
    ( m1_pre_topc(X0_55,X1_55) = iProver_top
    | m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_855])).

cnf(c_2395,plain,
    ( m1_pre_topc(X0_55,sK2) = iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_843,c_1406])).

cnf(c_2417,plain,
    ( l1_pre_topc(X0_55) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(X0_55,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2395,c_42,c_2231])).

cnf(c_2418,plain,
    ( m1_pre_topc(X0_55,sK2) = iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_2417])).

cnf(c_2426,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_2418])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_841,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1418,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_2230,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1418,c_1405])).

cnf(c_2577,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2426,c_42,c_2230])).

cnf(c_17,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_13,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X0,X2)
    | v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_447,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_17,c_13])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_469,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_447,c_3,c_18])).

cnf(c_828,plain,
    ( ~ v1_tsep_1(X0_55,X1_55)
    | v1_tsep_1(X0_55,X2_55)
    | ~ m1_pre_topc(X2_55,X1_55)
    | ~ m1_pre_topc(X0_55,X2_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v2_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_469])).

cnf(c_1431,plain,
    ( v1_tsep_1(X0_55,X1_55) != iProver_top
    | v1_tsep_1(X0_55,X2_55) = iProver_top
    | m1_pre_topc(X2_55,X1_55) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_828])).

cnf(c_6053,plain,
    ( v1_tsep_1(X0_55,sK2) != iProver_top
    | v1_tsep_1(X0_55,sK3) = iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2577,c_1431])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_41,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_46,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_48,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_857,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | ~ v2_pre_topc(X1_55)
    | v2_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1404,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_857])).

cnf(c_1789,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_1404])).

cnf(c_10080,plain,
    ( v1_tsep_1(X0_55,sK2) != iProver_top
    | v1_tsep_1(X0_55,sK3) = iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6053,c_41,c_42,c_46,c_48,c_1789,c_2231])).

cnf(c_10093,plain,
    ( v1_tsep_1(sK2,sK2) != iProver_top
    | v1_tsep_1(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4553,c_10080])).

cnf(c_10149,plain,
    ( ~ v1_tsep_1(sK2,sK2)
    | v1_tsep_1(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10093])).

cnf(c_4037,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4014])).

cnf(c_2,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_405,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_1])).

cnf(c_830,plain,
    ( ~ l1_pre_topc(X0_55)
    | u1_struct_0(X0_55) = k2_struct_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_405])).

cnf(c_3738,plain,
    ( ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_22,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_847,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1414,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_23,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_846,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1475,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1414,c_846])).

cnf(c_19,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_558,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_559,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_563,plain,
    ( ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v1_tsep_1(X0,X3)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_559,c_29])).

cnf(c_564,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_563])).

cnf(c_607,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v1_tsep_1(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_564,c_18])).

cnf(c_826,plain,
    ( ~ r1_tmap_1(X0_55,X1_55,k3_tmap_1(X2_55,X1_55,X3_55,X0_55,sK4),X0_56)
    | r1_tmap_1(X3_55,X1_55,sK4,X0_56)
    | ~ v1_tsep_1(X0_55,X3_55)
    | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
    | ~ m1_subset_1(X0_56,u1_struct_0(X3_55))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55))))
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_pre_topc(X3_55,X2_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X2_55)
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X2_55)
    | u1_struct_0(X1_55) != u1_struct_0(sK1)
    | u1_struct_0(X3_55) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_607])).

cnf(c_1433,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK1)
    | u1_struct_0(X1_55) != u1_struct_0(sK3)
    | r1_tmap_1(X2_55,X0_55,k3_tmap_1(X3_55,X0_55,X1_55,X2_55,sK4),X0_56) != iProver_top
    | r1_tmap_1(X1_55,X0_55,sK4,X0_56) = iProver_top
    | v1_tsep_1(X2_55,X1_55) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X2_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
    | m1_pre_topc(X2_55,X1_55) != iProver_top
    | m1_pre_topc(X1_55,X3_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_826])).

cnf(c_2603,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | r1_tmap_1(X1_55,sK1,k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4),X0_56) != iProver_top
    | r1_tmap_1(X0_55,sK1,sK4,X0_56) = iProver_top
    | v1_tsep_1(X1_55,X0_55) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1433])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_43,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_44,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_45,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2768,plain,
    ( v2_pre_topc(X2_55) != iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | v1_tsep_1(X1_55,X0_55) != iProver_top
    | r1_tmap_1(X0_55,sK1,sK4,X0_56) = iProver_top
    | r1_tmap_1(X1_55,sK1,k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4),X0_56) != iProver_top
    | u1_struct_0(X0_55) != u1_struct_0(sK3)
    | l1_pre_topc(X2_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2603,c_43,c_44,c_45])).

cnf(c_2769,plain,
    ( u1_struct_0(X0_55) != u1_struct_0(sK3)
    | r1_tmap_1(X1_55,sK1,k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4),X0_56) != iProver_top
    | r1_tmap_1(X0_55,sK1,sK4,X0_56) = iProver_top
    | v1_tsep_1(X1_55,X0_55) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_pre_topc(X1_55,X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_2768])).

cnf(c_2786,plain,
    ( r1_tmap_1(X0_55,sK1,k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4),X0_56) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_56) = iProver_top
    | v1_tsep_1(X0_55,sK3) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2769])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_52,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2867,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | r1_tmap_1(X0_55,sK1,k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4),X0_56) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_56) = iProver_top
    | v1_tsep_1(X0_55,sK3) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2786,c_48,c_52])).

cnf(c_2868,plain,
    ( r1_tmap_1(X0_55,sK1,k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4),X0_56) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X0_56) = iProver_top
    | v1_tsep_1(X0_55,sK3) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_56,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(X0_55,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_2867])).

cnf(c_2884,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1475,c_2868])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_40,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_49,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_53,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_56,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_845,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1415,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_845])).

cnf(c_1456,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1415,c_846])).

cnf(c_3645,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | v1_tsep_1(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2884,c_40,c_41,c_42,c_46,c_49,c_53,c_56,c_1456])).

cnf(c_3646,plain,
    ( v1_tsep_1(sK2,sK3) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3645])).

cnf(c_3647,plain,
    ( ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3646])).

cnf(c_2955,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_2241,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2231])).

cnf(c_1790,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1789])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15014,c_10149,c_4037,c_3738,c_3647,c_2955,c_2241,c_1790,c_37,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:43:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.71/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/1.00  
% 3.71/1.00  ------  iProver source info
% 3.71/1.00  
% 3.71/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.71/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/1.00  git: non_committed_changes: false
% 3.71/1.00  git: last_make_outside_of_git: false
% 3.71/1.00  
% 3.71/1.00  ------ 
% 3.71/1.00  
% 3.71/1.00  ------ Input Options
% 3.71/1.00  
% 3.71/1.00  --out_options                           all
% 3.71/1.00  --tptp_safe_out                         true
% 3.71/1.00  --problem_path                          ""
% 3.71/1.00  --include_path                          ""
% 3.71/1.00  --clausifier                            res/vclausify_rel
% 3.71/1.00  --clausifier_options                    --mode clausify
% 3.71/1.00  --stdin                                 false
% 3.71/1.00  --stats_out                             all
% 3.71/1.00  
% 3.71/1.00  ------ General Options
% 3.71/1.00  
% 3.71/1.00  --fof                                   false
% 3.71/1.00  --time_out_real                         305.
% 3.71/1.00  --time_out_virtual                      -1.
% 3.71/1.00  --symbol_type_check                     false
% 3.71/1.00  --clausify_out                          false
% 3.71/1.00  --sig_cnt_out                           false
% 3.71/1.00  --trig_cnt_out                          false
% 3.71/1.00  --trig_cnt_out_tolerance                1.
% 3.71/1.00  --trig_cnt_out_sk_spl                   false
% 3.71/1.00  --abstr_cl_out                          false
% 3.71/1.00  
% 3.71/1.00  ------ Global Options
% 3.71/1.00  
% 3.71/1.00  --schedule                              default
% 3.71/1.00  --add_important_lit                     false
% 3.71/1.00  --prop_solver_per_cl                    1000
% 3.71/1.00  --min_unsat_core                        false
% 3.71/1.00  --soft_assumptions                      false
% 3.71/1.00  --soft_lemma_size                       3
% 3.71/1.00  --prop_impl_unit_size                   0
% 3.71/1.00  --prop_impl_unit                        []
% 3.71/1.00  --share_sel_clauses                     true
% 3.71/1.00  --reset_solvers                         false
% 3.71/1.00  --bc_imp_inh                            [conj_cone]
% 3.71/1.00  --conj_cone_tolerance                   3.
% 3.71/1.00  --extra_neg_conj                        none
% 3.71/1.00  --large_theory_mode                     true
% 3.71/1.00  --prolific_symb_bound                   200
% 3.71/1.00  --lt_threshold                          2000
% 3.71/1.00  --clause_weak_htbl                      true
% 3.71/1.00  --gc_record_bc_elim                     false
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing Options
% 3.71/1.00  
% 3.71/1.00  --preprocessing_flag                    true
% 3.71/1.00  --time_out_prep_mult                    0.1
% 3.71/1.00  --splitting_mode                        input
% 3.71/1.00  --splitting_grd                         true
% 3.71/1.00  --splitting_cvd                         false
% 3.71/1.00  --splitting_cvd_svl                     false
% 3.71/1.00  --splitting_nvd                         32
% 3.71/1.00  --sub_typing                            true
% 3.71/1.00  --prep_gs_sim                           true
% 3.71/1.00  --prep_unflatten                        true
% 3.71/1.00  --prep_res_sim                          true
% 3.71/1.00  --prep_upred                            true
% 3.71/1.00  --prep_sem_filter                       exhaustive
% 3.71/1.00  --prep_sem_filter_out                   false
% 3.71/1.00  --pred_elim                             true
% 3.71/1.00  --res_sim_input                         true
% 3.71/1.00  --eq_ax_congr_red                       true
% 3.71/1.00  --pure_diseq_elim                       true
% 3.71/1.00  --brand_transform                       false
% 3.71/1.00  --non_eq_to_eq                          false
% 3.71/1.00  --prep_def_merge                        true
% 3.71/1.00  --prep_def_merge_prop_impl              false
% 3.71/1.00  --prep_def_merge_mbd                    true
% 3.71/1.00  --prep_def_merge_tr_red                 false
% 3.71/1.00  --prep_def_merge_tr_cl                  false
% 3.71/1.00  --smt_preprocessing                     true
% 3.71/1.00  --smt_ac_axioms                         fast
% 3.71/1.00  --preprocessed_out                      false
% 3.71/1.00  --preprocessed_stats                    false
% 3.71/1.00  
% 3.71/1.00  ------ Abstraction refinement Options
% 3.71/1.00  
% 3.71/1.00  --abstr_ref                             []
% 3.71/1.00  --abstr_ref_prep                        false
% 3.71/1.00  --abstr_ref_until_sat                   false
% 3.71/1.00  --abstr_ref_sig_restrict                funpre
% 3.71/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.00  --abstr_ref_under                       []
% 3.71/1.00  
% 3.71/1.00  ------ SAT Options
% 3.71/1.00  
% 3.71/1.00  --sat_mode                              false
% 3.71/1.00  --sat_fm_restart_options                ""
% 3.71/1.00  --sat_gr_def                            false
% 3.71/1.00  --sat_epr_types                         true
% 3.71/1.00  --sat_non_cyclic_types                  false
% 3.71/1.00  --sat_finite_models                     false
% 3.71/1.00  --sat_fm_lemmas                         false
% 3.71/1.00  --sat_fm_prep                           false
% 3.71/1.00  --sat_fm_uc_incr                        true
% 3.71/1.00  --sat_out_model                         small
% 3.71/1.00  --sat_out_clauses                       false
% 3.71/1.00  
% 3.71/1.00  ------ QBF Options
% 3.71/1.00  
% 3.71/1.00  --qbf_mode                              false
% 3.71/1.00  --qbf_elim_univ                         false
% 3.71/1.00  --qbf_dom_inst                          none
% 3.71/1.00  --qbf_dom_pre_inst                      false
% 3.71/1.00  --qbf_sk_in                             false
% 3.71/1.00  --qbf_pred_elim                         true
% 3.71/1.00  --qbf_split                             512
% 3.71/1.00  
% 3.71/1.00  ------ BMC1 Options
% 3.71/1.00  
% 3.71/1.00  --bmc1_incremental                      false
% 3.71/1.00  --bmc1_axioms                           reachable_all
% 3.71/1.00  --bmc1_min_bound                        0
% 3.71/1.00  --bmc1_max_bound                        -1
% 3.71/1.00  --bmc1_max_bound_default                -1
% 3.71/1.00  --bmc1_symbol_reachability              true
% 3.71/1.00  --bmc1_property_lemmas                  false
% 3.71/1.00  --bmc1_k_induction                      false
% 3.71/1.00  --bmc1_non_equiv_states                 false
% 3.71/1.00  --bmc1_deadlock                         false
% 3.71/1.00  --bmc1_ucm                              false
% 3.71/1.00  --bmc1_add_unsat_core                   none
% 3.71/1.00  --bmc1_unsat_core_children              false
% 3.71/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.00  --bmc1_out_stat                         full
% 3.71/1.00  --bmc1_ground_init                      false
% 3.71/1.00  --bmc1_pre_inst_next_state              false
% 3.71/1.00  --bmc1_pre_inst_state                   false
% 3.71/1.00  --bmc1_pre_inst_reach_state             false
% 3.71/1.00  --bmc1_out_unsat_core                   false
% 3.71/1.00  --bmc1_aig_witness_out                  false
% 3.71/1.00  --bmc1_verbose                          false
% 3.71/1.00  --bmc1_dump_clauses_tptp                false
% 3.71/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.00  --bmc1_dump_file                        -
% 3.71/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.00  --bmc1_ucm_extend_mode                  1
% 3.71/1.00  --bmc1_ucm_init_mode                    2
% 3.71/1.00  --bmc1_ucm_cone_mode                    none
% 3.71/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.00  --bmc1_ucm_relax_model                  4
% 3.71/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.00  --bmc1_ucm_layered_model                none
% 3.71/1.00  --bmc1_ucm_max_lemma_size               10
% 3.71/1.00  
% 3.71/1.00  ------ AIG Options
% 3.71/1.00  
% 3.71/1.00  --aig_mode                              false
% 3.71/1.00  
% 3.71/1.00  ------ Instantiation Options
% 3.71/1.00  
% 3.71/1.00  --instantiation_flag                    true
% 3.71/1.00  --inst_sos_flag                         false
% 3.71/1.00  --inst_sos_phase                        true
% 3.71/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel_side                     num_symb
% 3.71/1.00  --inst_solver_per_active                1400
% 3.71/1.00  --inst_solver_calls_frac                1.
% 3.71/1.00  --inst_passive_queue_type               priority_queues
% 3.71/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.00  --inst_passive_queues_freq              [25;2]
% 3.71/1.00  --inst_dismatching                      true
% 3.71/1.00  --inst_eager_unprocessed_to_passive     true
% 3.71/1.00  --inst_prop_sim_given                   true
% 3.71/1.00  --inst_prop_sim_new                     false
% 3.71/1.00  --inst_subs_new                         false
% 3.71/1.00  --inst_eq_res_simp                      false
% 3.71/1.00  --inst_subs_given                       false
% 3.71/1.00  --inst_orphan_elimination               true
% 3.71/1.00  --inst_learning_loop_flag               true
% 3.71/1.00  --inst_learning_start                   3000
% 3.71/1.00  --inst_learning_factor                  2
% 3.71/1.00  --inst_start_prop_sim_after_learn       3
% 3.71/1.00  --inst_sel_renew                        solver
% 3.71/1.00  --inst_lit_activity_flag                true
% 3.71/1.00  --inst_restr_to_given                   false
% 3.71/1.00  --inst_activity_threshold               500
% 3.71/1.00  --inst_out_proof                        true
% 3.71/1.00  
% 3.71/1.00  ------ Resolution Options
% 3.71/1.00  
% 3.71/1.00  --resolution_flag                       true
% 3.71/1.00  --res_lit_sel                           adaptive
% 3.71/1.00  --res_lit_sel_side                      none
% 3.71/1.00  --res_ordering                          kbo
% 3.71/1.00  --res_to_prop_solver                    active
% 3.71/1.00  --res_prop_simpl_new                    false
% 3.71/1.00  --res_prop_simpl_given                  true
% 3.71/1.00  --res_passive_queue_type                priority_queues
% 3.71/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.00  --res_passive_queues_freq               [15;5]
% 3.71/1.00  --res_forward_subs                      full
% 3.71/1.00  --res_backward_subs                     full
% 3.71/1.00  --res_forward_subs_resolution           true
% 3.71/1.00  --res_backward_subs_resolution          true
% 3.71/1.00  --res_orphan_elimination                true
% 3.71/1.00  --res_time_limit                        2.
% 3.71/1.00  --res_out_proof                         true
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Options
% 3.71/1.00  
% 3.71/1.00  --superposition_flag                    true
% 3.71/1.00  --sup_passive_queue_type                priority_queues
% 3.71/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.00  --demod_completeness_check              fast
% 3.71/1.00  --demod_use_ground                      true
% 3.71/1.00  --sup_to_prop_solver                    passive
% 3.71/1.00  --sup_prop_simpl_new                    true
% 3.71/1.00  --sup_prop_simpl_given                  true
% 3.71/1.00  --sup_fun_splitting                     false
% 3.71/1.00  --sup_smt_interval                      50000
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Simplification Setup
% 3.71/1.00  
% 3.71/1.00  --sup_indices_passive                   []
% 3.71/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_full_bw                           [BwDemod]
% 3.71/1.00  --sup_immed_triv                        [TrivRules]
% 3.71/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_immed_bw_main                     []
% 3.71/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  
% 3.71/1.00  ------ Combination Options
% 3.71/1.00  
% 3.71/1.00  --comb_res_mult                         3
% 3.71/1.00  --comb_sup_mult                         2
% 3.71/1.00  --comb_inst_mult                        10
% 3.71/1.00  
% 3.71/1.00  ------ Debug Options
% 3.71/1.00  
% 3.71/1.00  --dbg_backtrace                         false
% 3.71/1.00  --dbg_dump_prop_clauses                 false
% 3.71/1.00  --dbg_dump_prop_clauses_file            -
% 3.71/1.00  --dbg_out_stat                          false
% 3.71/1.00  ------ Parsing...
% 3.71/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/1.00  ------ Proving...
% 3.71/1.00  ------ Problem Properties 
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  clauses                                 32
% 3.71/1.00  conjectures                             17
% 3.71/1.00  EPR                                     17
% 3.71/1.00  Horn                                    26
% 3.71/1.00  unary                                   17
% 3.71/1.00  binary                                  2
% 3.71/1.00  lits                                    112
% 3.71/1.00  lits eq                                 9
% 3.71/1.00  fd_pure                                 0
% 3.71/1.00  fd_pseudo                               0
% 3.71/1.00  fd_cond                                 0
% 3.71/1.00  fd_pseudo_cond                          0
% 3.71/1.00  AC symbols                              0
% 3.71/1.00  
% 3.71/1.00  ------ Schedule dynamic 5 is on 
% 3.71/1.00  
% 3.71/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  ------ 
% 3.71/1.00  Current options:
% 3.71/1.00  ------ 
% 3.71/1.00  
% 3.71/1.00  ------ Input Options
% 3.71/1.00  
% 3.71/1.00  --out_options                           all
% 3.71/1.00  --tptp_safe_out                         true
% 3.71/1.00  --problem_path                          ""
% 3.71/1.00  --include_path                          ""
% 3.71/1.00  --clausifier                            res/vclausify_rel
% 3.71/1.00  --clausifier_options                    --mode clausify
% 3.71/1.00  --stdin                                 false
% 3.71/1.00  --stats_out                             all
% 3.71/1.00  
% 3.71/1.00  ------ General Options
% 3.71/1.00  
% 3.71/1.00  --fof                                   false
% 3.71/1.00  --time_out_real                         305.
% 3.71/1.00  --time_out_virtual                      -1.
% 3.71/1.00  --symbol_type_check                     false
% 3.71/1.00  --clausify_out                          false
% 3.71/1.00  --sig_cnt_out                           false
% 3.71/1.00  --trig_cnt_out                          false
% 3.71/1.00  --trig_cnt_out_tolerance                1.
% 3.71/1.00  --trig_cnt_out_sk_spl                   false
% 3.71/1.00  --abstr_cl_out                          false
% 3.71/1.00  
% 3.71/1.00  ------ Global Options
% 3.71/1.00  
% 3.71/1.00  --schedule                              default
% 3.71/1.00  --add_important_lit                     false
% 3.71/1.00  --prop_solver_per_cl                    1000
% 3.71/1.00  --min_unsat_core                        false
% 3.71/1.00  --soft_assumptions                      false
% 3.71/1.00  --soft_lemma_size                       3
% 3.71/1.00  --prop_impl_unit_size                   0
% 3.71/1.00  --prop_impl_unit                        []
% 3.71/1.00  --share_sel_clauses                     true
% 3.71/1.00  --reset_solvers                         false
% 3.71/1.00  --bc_imp_inh                            [conj_cone]
% 3.71/1.00  --conj_cone_tolerance                   3.
% 3.71/1.00  --extra_neg_conj                        none
% 3.71/1.00  --large_theory_mode                     true
% 3.71/1.00  --prolific_symb_bound                   200
% 3.71/1.00  --lt_threshold                          2000
% 3.71/1.00  --clause_weak_htbl                      true
% 3.71/1.00  --gc_record_bc_elim                     false
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing Options
% 3.71/1.00  
% 3.71/1.00  --preprocessing_flag                    true
% 3.71/1.00  --time_out_prep_mult                    0.1
% 3.71/1.00  --splitting_mode                        input
% 3.71/1.00  --splitting_grd                         true
% 3.71/1.00  --splitting_cvd                         false
% 3.71/1.00  --splitting_cvd_svl                     false
% 3.71/1.00  --splitting_nvd                         32
% 3.71/1.00  --sub_typing                            true
% 3.71/1.00  --prep_gs_sim                           true
% 3.71/1.00  --prep_unflatten                        true
% 3.71/1.00  --prep_res_sim                          true
% 3.71/1.00  --prep_upred                            true
% 3.71/1.00  --prep_sem_filter                       exhaustive
% 3.71/1.00  --prep_sem_filter_out                   false
% 3.71/1.00  --pred_elim                             true
% 3.71/1.00  --res_sim_input                         true
% 3.71/1.00  --eq_ax_congr_red                       true
% 3.71/1.00  --pure_diseq_elim                       true
% 3.71/1.00  --brand_transform                       false
% 3.71/1.00  --non_eq_to_eq                          false
% 3.71/1.00  --prep_def_merge                        true
% 3.71/1.00  --prep_def_merge_prop_impl              false
% 3.71/1.00  --prep_def_merge_mbd                    true
% 3.71/1.00  --prep_def_merge_tr_red                 false
% 3.71/1.00  --prep_def_merge_tr_cl                  false
% 3.71/1.00  --smt_preprocessing                     true
% 3.71/1.00  --smt_ac_axioms                         fast
% 3.71/1.00  --preprocessed_out                      false
% 3.71/1.00  --preprocessed_stats                    false
% 3.71/1.00  
% 3.71/1.00  ------ Abstraction refinement Options
% 3.71/1.00  
% 3.71/1.00  --abstr_ref                             []
% 3.71/1.00  --abstr_ref_prep                        false
% 3.71/1.00  --abstr_ref_until_sat                   false
% 3.71/1.00  --abstr_ref_sig_restrict                funpre
% 3.71/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.00  --abstr_ref_under                       []
% 3.71/1.00  
% 3.71/1.00  ------ SAT Options
% 3.71/1.00  
% 3.71/1.00  --sat_mode                              false
% 3.71/1.00  --sat_fm_restart_options                ""
% 3.71/1.00  --sat_gr_def                            false
% 3.71/1.00  --sat_epr_types                         true
% 3.71/1.00  --sat_non_cyclic_types                  false
% 3.71/1.00  --sat_finite_models                     false
% 3.71/1.00  --sat_fm_lemmas                         false
% 3.71/1.00  --sat_fm_prep                           false
% 3.71/1.00  --sat_fm_uc_incr                        true
% 3.71/1.00  --sat_out_model                         small
% 3.71/1.00  --sat_out_clauses                       false
% 3.71/1.00  
% 3.71/1.00  ------ QBF Options
% 3.71/1.00  
% 3.71/1.00  --qbf_mode                              false
% 3.71/1.00  --qbf_elim_univ                         false
% 3.71/1.00  --qbf_dom_inst                          none
% 3.71/1.00  --qbf_dom_pre_inst                      false
% 3.71/1.00  --qbf_sk_in                             false
% 3.71/1.00  --qbf_pred_elim                         true
% 3.71/1.00  --qbf_split                             512
% 3.71/1.00  
% 3.71/1.00  ------ BMC1 Options
% 3.71/1.00  
% 3.71/1.00  --bmc1_incremental                      false
% 3.71/1.00  --bmc1_axioms                           reachable_all
% 3.71/1.00  --bmc1_min_bound                        0
% 3.71/1.00  --bmc1_max_bound                        -1
% 3.71/1.00  --bmc1_max_bound_default                -1
% 3.71/1.00  --bmc1_symbol_reachability              true
% 3.71/1.00  --bmc1_property_lemmas                  false
% 3.71/1.00  --bmc1_k_induction                      false
% 3.71/1.00  --bmc1_non_equiv_states                 false
% 3.71/1.00  --bmc1_deadlock                         false
% 3.71/1.00  --bmc1_ucm                              false
% 3.71/1.00  --bmc1_add_unsat_core                   none
% 3.71/1.00  --bmc1_unsat_core_children              false
% 3.71/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.00  --bmc1_out_stat                         full
% 3.71/1.00  --bmc1_ground_init                      false
% 3.71/1.00  --bmc1_pre_inst_next_state              false
% 3.71/1.00  --bmc1_pre_inst_state                   false
% 3.71/1.00  --bmc1_pre_inst_reach_state             false
% 3.71/1.00  --bmc1_out_unsat_core                   false
% 3.71/1.00  --bmc1_aig_witness_out                  false
% 3.71/1.00  --bmc1_verbose                          false
% 3.71/1.00  --bmc1_dump_clauses_tptp                false
% 3.71/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.00  --bmc1_dump_file                        -
% 3.71/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.00  --bmc1_ucm_extend_mode                  1
% 3.71/1.00  --bmc1_ucm_init_mode                    2
% 3.71/1.00  --bmc1_ucm_cone_mode                    none
% 3.71/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.00  --bmc1_ucm_relax_model                  4
% 3.71/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.00  --bmc1_ucm_layered_model                none
% 3.71/1.00  --bmc1_ucm_max_lemma_size               10
% 3.71/1.00  
% 3.71/1.00  ------ AIG Options
% 3.71/1.00  
% 3.71/1.00  --aig_mode                              false
% 3.71/1.00  
% 3.71/1.00  ------ Instantiation Options
% 3.71/1.00  
% 3.71/1.00  --instantiation_flag                    true
% 3.71/1.00  --inst_sos_flag                         false
% 3.71/1.00  --inst_sos_phase                        true
% 3.71/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel_side                     none
% 3.71/1.00  --inst_solver_per_active                1400
% 3.71/1.00  --inst_solver_calls_frac                1.
% 3.71/1.00  --inst_passive_queue_type               priority_queues
% 3.71/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.00  --inst_passive_queues_freq              [25;2]
% 3.71/1.00  --inst_dismatching                      true
% 3.71/1.00  --inst_eager_unprocessed_to_passive     true
% 3.71/1.00  --inst_prop_sim_given                   true
% 3.71/1.00  --inst_prop_sim_new                     false
% 3.71/1.00  --inst_subs_new                         false
% 3.71/1.00  --inst_eq_res_simp                      false
% 3.71/1.00  --inst_subs_given                       false
% 3.71/1.00  --inst_orphan_elimination               true
% 3.71/1.00  --inst_learning_loop_flag               true
% 3.71/1.00  --inst_learning_start                   3000
% 3.71/1.00  --inst_learning_factor                  2
% 3.71/1.00  --inst_start_prop_sim_after_learn       3
% 3.71/1.00  --inst_sel_renew                        solver
% 3.71/1.00  --inst_lit_activity_flag                true
% 3.71/1.00  --inst_restr_to_given                   false
% 3.71/1.00  --inst_activity_threshold               500
% 3.71/1.00  --inst_out_proof                        true
% 3.71/1.00  
% 3.71/1.00  ------ Resolution Options
% 3.71/1.00  
% 3.71/1.00  --resolution_flag                       false
% 3.71/1.00  --res_lit_sel                           adaptive
% 3.71/1.00  --res_lit_sel_side                      none
% 3.71/1.00  --res_ordering                          kbo
% 3.71/1.00  --res_to_prop_solver                    active
% 3.71/1.00  --res_prop_simpl_new                    false
% 3.71/1.00  --res_prop_simpl_given                  true
% 3.71/1.00  --res_passive_queue_type                priority_queues
% 3.71/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.00  --res_passive_queues_freq               [15;5]
% 3.71/1.00  --res_forward_subs                      full
% 3.71/1.00  --res_backward_subs                     full
% 3.71/1.00  --res_forward_subs_resolution           true
% 3.71/1.00  --res_backward_subs_resolution          true
% 3.71/1.00  --res_orphan_elimination                true
% 3.71/1.00  --res_time_limit                        2.
% 3.71/1.00  --res_out_proof                         true
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Options
% 3.71/1.00  
% 3.71/1.00  --superposition_flag                    true
% 3.71/1.00  --sup_passive_queue_type                priority_queues
% 3.71/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.00  --demod_completeness_check              fast
% 3.71/1.00  --demod_use_ground                      true
% 3.71/1.00  --sup_to_prop_solver                    passive
% 3.71/1.00  --sup_prop_simpl_new                    true
% 3.71/1.00  --sup_prop_simpl_given                  true
% 3.71/1.00  --sup_fun_splitting                     false
% 3.71/1.00  --sup_smt_interval                      50000
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Simplification Setup
% 3.71/1.00  
% 3.71/1.00  --sup_indices_passive                   []
% 3.71/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_full_bw                           [BwDemod]
% 3.71/1.00  --sup_immed_triv                        [TrivRules]
% 3.71/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_immed_bw_main                     []
% 3.71/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  
% 3.71/1.00  ------ Combination Options
% 3.71/1.00  
% 3.71/1.00  --comb_res_mult                         3
% 3.71/1.00  --comb_sup_mult                         2
% 3.71/1.00  --comb_inst_mult                        10
% 3.71/1.00  
% 3.71/1.00  ------ Debug Options
% 3.71/1.00  
% 3.71/1.00  --dbg_backtrace                         false
% 3.71/1.00  --dbg_dump_prop_clauses                 false
% 3.71/1.00  --dbg_dump_prop_clauses_file            -
% 3.71/1.00  --dbg_out_stat                          false
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  ------ Proving...
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  % SZS status Theorem for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  fof(f6,axiom,(
% 3.71/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f25,plain,(
% 3.71/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.71/1.00    inference(ennf_transformation,[],[f6])).
% 3.71/1.00  
% 3.71/1.00  fof(f26,plain,(
% 3.71/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.71/1.00    inference(flattening,[],[f25])).
% 3.71/1.00  
% 3.71/1.00  fof(f62,plain,(
% 3.71/1.00    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f26])).
% 3.71/1.00  
% 3.71/1.00  fof(f8,axiom,(
% 3.71/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f29,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.71/1.00    inference(ennf_transformation,[],[f8])).
% 3.71/1.00  
% 3.71/1.00  fof(f30,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.71/1.00    inference(flattening,[],[f29])).
% 3.71/1.00  
% 3.71/1.00  fof(f45,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.71/1.00    inference(nnf_transformation,[],[f30])).
% 3.71/1.00  
% 3.71/1.00  fof(f46,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.71/1.00    inference(flattening,[],[f45])).
% 3.71/1.00  
% 3.71/1.00  fof(f66,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f46])).
% 3.71/1.00  
% 3.71/1.00  fof(f97,plain,(
% 3.71/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.71/1.00    inference(equality_resolution,[],[f66])).
% 3.71/1.00  
% 3.71/1.00  fof(f10,axiom,(
% 3.71/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f33,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f10])).
% 3.71/1.00  
% 3.71/1.00  fof(f70,plain,(
% 3.71/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f33])).
% 3.71/1.00  
% 3.71/1.00  fof(f12,axiom,(
% 3.71/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f36,plain,(
% 3.71/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f12])).
% 3.71/1.00  
% 3.71/1.00  fof(f72,plain,(
% 3.71/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f36])).
% 3.71/1.00  
% 3.71/1.00  fof(f16,conjecture,(
% 3.71/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f17,negated_conjecture,(
% 3.71/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.71/1.00    inference(negated_conjecture,[],[f16])).
% 3.71/1.00  
% 3.71/1.00  fof(f42,plain,(
% 3.71/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.71/1.00    inference(ennf_transformation,[],[f17])).
% 3.71/1.00  
% 3.71/1.00  fof(f43,plain,(
% 3.71/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.71/1.00    inference(flattening,[],[f42])).
% 3.71/1.00  
% 3.71/1.00  fof(f54,plain,(
% 3.71/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f53,plain,(
% 3.71/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f52,plain,(
% 3.71/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f51,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f50,plain,(
% 3.71/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f49,plain,(
% 3.71/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f48,plain,(
% 3.71/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f55,plain,(
% 3.71/1.00    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f43,f54,f53,f52,f51,f50,f49,f48])).
% 3.71/1.00  
% 3.71/1.00  fof(f90,plain,(
% 3.71/1.00    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f5,axiom,(
% 3.71/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f24,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f5])).
% 3.71/1.00  
% 3.71/1.00  fof(f44,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.71/1.00    inference(nnf_transformation,[],[f24])).
% 3.71/1.00  
% 3.71/1.00  fof(f60,plain,(
% 3.71/1.00    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f44])).
% 3.71/1.00  
% 3.71/1.00  fof(f4,axiom,(
% 3.71/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f23,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f4])).
% 3.71/1.00  
% 3.71/1.00  fof(f59,plain,(
% 3.71/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f23])).
% 3.71/1.00  
% 3.71/1.00  fof(f79,plain,(
% 3.71/1.00    l1_pre_topc(sK0)),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f84,plain,(
% 3.71/1.00    m1_pre_topc(sK2,sK0)),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f61,plain,(
% 3.71/1.00    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f44])).
% 3.71/1.00  
% 3.71/1.00  fof(f86,plain,(
% 3.71/1.00    m1_pre_topc(sK3,sK0)),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f13,axiom,(
% 3.71/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f37,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f13])).
% 3.71/1.00  
% 3.71/1.00  fof(f73,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f37])).
% 3.71/1.00  
% 3.71/1.00  fof(f9,axiom,(
% 3.71/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f31,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.71/1.00    inference(ennf_transformation,[],[f9])).
% 3.71/1.00  
% 3.71/1.00  fof(f32,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.71/1.00    inference(flattening,[],[f31])).
% 3.71/1.00  
% 3.71/1.00  fof(f68,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f32])).
% 3.71/1.00  
% 3.71/1.00  fof(f14,axiom,(
% 3.71/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f38,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.71/1.00    inference(ennf_transformation,[],[f14])).
% 3.71/1.00  
% 3.71/1.00  fof(f39,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.71/1.00    inference(flattening,[],[f38])).
% 3.71/1.00  
% 3.71/1.00  fof(f74,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f39])).
% 3.71/1.00  
% 3.71/1.00  fof(f78,plain,(
% 3.71/1.00    v2_pre_topc(sK0)),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f83,plain,(
% 3.71/1.00    ~v2_struct_0(sK2)),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f85,plain,(
% 3.71/1.00    ~v2_struct_0(sK3)),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f1,axiom,(
% 3.71/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f19,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.71/1.00    inference(ennf_transformation,[],[f1])).
% 3.71/1.00  
% 3.71/1.00  fof(f20,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.71/1.00    inference(flattening,[],[f19])).
% 3.71/1.00  
% 3.71/1.00  fof(f56,plain,(
% 3.71/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f20])).
% 3.71/1.00  
% 3.71/1.00  fof(f3,axiom,(
% 3.71/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f22,plain,(
% 3.71/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f3])).
% 3.71/1.00  
% 3.71/1.00  fof(f58,plain,(
% 3.71/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f22])).
% 3.71/1.00  
% 3.71/1.00  fof(f2,axiom,(
% 3.71/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f21,plain,(
% 3.71/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f2])).
% 3.71/1.00  
% 3.71/1.00  fof(f57,plain,(
% 3.71/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f21])).
% 3.71/1.00  
% 3.71/1.00  fof(f94,plain,(
% 3.71/1.00    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f93,plain,(
% 3.71/1.00    sK5 = sK6),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f15,axiom,(
% 3.71/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f40,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.71/1.00    inference(ennf_transformation,[],[f15])).
% 3.71/1.00  
% 3.71/1.00  fof(f41,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.71/1.00    inference(flattening,[],[f40])).
% 3.71/1.00  
% 3.71/1.00  fof(f47,plain,(
% 3.71/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.71/1.00    inference(nnf_transformation,[],[f41])).
% 3.71/1.00  
% 3.71/1.00  fof(f76,plain,(
% 3.71/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f47])).
% 3.71/1.00  
% 3.71/1.00  fof(f99,plain,(
% 3.71/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.71/1.00    inference(equality_resolution,[],[f76])).
% 3.71/1.00  
% 3.71/1.00  fof(f88,plain,(
% 3.71/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f87,plain,(
% 3.71/1.00    v1_funct_1(sK4)),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f80,plain,(
% 3.71/1.00    ~v2_struct_0(sK1)),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f81,plain,(
% 3.71/1.00    v2_pre_topc(sK1)),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f82,plain,(
% 3.71/1.00    l1_pre_topc(sK1)),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f89,plain,(
% 3.71/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f77,plain,(
% 3.71/1.00    ~v2_struct_0(sK0)),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f91,plain,(
% 3.71/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f95,plain,(
% 3.71/1.00    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f92,plain,(
% 3.71/1.00    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6,plain,
% 3.71/1.00      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.71/1.00      | ~ l1_pre_topc(X0)
% 3.71/1.00      | ~ v2_pre_topc(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_10,plain,
% 3.71/1.00      ( v1_tsep_1(X0,X1)
% 3.71/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.71/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.71/1.00      | ~ m1_pre_topc(X0,X1)
% 3.71/1.00      | ~ l1_pre_topc(X1)
% 3.71/1.00      | ~ v2_pre_topc(X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_14,plain,
% 3.71/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.71/1.00      | ~ m1_pre_topc(X0,X1)
% 3.71/1.00      | ~ l1_pre_topc(X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_216,plain,
% 3.71/1.00      ( v1_tsep_1(X0,X1)
% 3.71/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.71/1.00      | ~ m1_pre_topc(X0,X1)
% 3.71/1.00      | ~ l1_pre_topc(X1)
% 3.71/1.00      | ~ v2_pre_topc(X1) ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_10,c_14]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_420,plain,
% 3.71/1.00      ( v1_tsep_1(X0,X1)
% 3.71/1.00      | ~ m1_pre_topc(X0,X1)
% 3.71/1.00      | ~ l1_pre_topc(X2)
% 3.71/1.00      | ~ l1_pre_topc(X1)
% 3.71/1.00      | ~ v2_pre_topc(X2)
% 3.71/1.00      | ~ v2_pre_topc(X1)
% 3.71/1.00      | X1 != X2
% 3.71/1.00      | u1_struct_0(X0) != k2_struct_0(X2) ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_216]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_421,plain,
% 3.71/1.00      ( v1_tsep_1(X0,X1)
% 3.71/1.00      | ~ m1_pre_topc(X0,X1)
% 3.71/1.00      | ~ l1_pre_topc(X1)
% 3.71/1.00      | ~ v2_pre_topc(X1)
% 3.71/1.00      | u1_struct_0(X0) != k2_struct_0(X1) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_420]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_829,plain,
% 3.71/1.00      ( v1_tsep_1(X0_55,X1_55)
% 3.71/1.00      | ~ m1_pre_topc(X0_55,X1_55)
% 3.71/1.00      | ~ l1_pre_topc(X1_55)
% 3.71/1.00      | ~ v2_pre_topc(X1_55)
% 3.71/1.00      | u1_struct_0(X0_55) != k2_struct_0(X1_55) ),
% 3.71/1.00      inference(subtyping,[status(esa)],[c_421]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6271,plain,
% 3.71/1.00      ( v1_tsep_1(sK2,X0_55)
% 3.71/1.00      | ~ m1_pre_topc(sK2,X0_55)
% 3.71/1.00      | ~ l1_pre_topc(X0_55)
% 3.71/1.00      | ~ v2_pre_topc(X0_55)
% 3.71/1.00      | u1_struct_0(sK2) != k2_struct_0(X0_55) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_829]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_15014,plain,
% 3.71/1.00      ( v1_tsep_1(sK2,sK2)
% 3.71/1.00      | ~ m1_pre_topc(sK2,sK2)
% 3.71/1.00      | ~ l1_pre_topc(sK2)
% 3.71/1.00      | ~ v2_pre_topc(sK2)
% 3.71/1.00      | u1_struct_0(sK2) != k2_struct_0(sK2) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_6271]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_16,plain,
% 3.71/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_850,plain,
% 3.71/1.00      ( m1_pre_topc(X0_55,X0_55) | ~ l1_pre_topc(X0_55) ),
% 3.71/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1411,plain,
% 3.71/1.00      ( m1_pre_topc(X0_55,X0_55) = iProver_top
% 3.71/1.00      | l1_pre_topc(X0_55) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_850]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_26,negated_conjecture,
% 3.71/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.71/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_843,negated_conjecture,
% 3.71/1.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.71/1.00      inference(subtyping,[status(esa)],[c_26]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5,plain,
% 3.71/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.71/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.71/1.00      | ~ l1_pre_topc(X0)
% 3.71/1.00      | ~ l1_pre_topc(X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3,plain,
% 3.71/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_226,plain,
% 3.71/1.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.71/1.00      | ~ m1_pre_topc(X0,X1)
% 3.71/1.00      | ~ l1_pre_topc(X1) ),
% 3.71/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5,c_3]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_227,plain,
% 3.71/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.71/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.71/1.00      | ~ l1_pre_topc(X1) ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_226]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_831,plain,
% 3.71/1.00      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.71/1.00      | m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))
% 3.71/1.00      | ~ l1_pre_topc(X1_55) ),
% 3.71/1.00      inference(subtyping,[status(esa)],[c_227]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1428,plain,
% 3.71/1.00      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) = iProver_top
% 3.71/1.00      | l1_pre_topc(X1_55) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3876,plain,
% 3.71/1.00      ( m1_pre_topc(X0_55,sK2) != iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,sK3) = iProver_top
% 3.71/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_843,c_1428]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_37,negated_conjecture,
% 3.71/1.00      ( l1_pre_topc(sK0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_42,plain,
% 3.71/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_32,negated_conjecture,
% 3.71/1.00      ( m1_pre_topc(sK2,sK0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_839,negated_conjecture,
% 3.71/1.00      ( m1_pre_topc(sK2,sK0) ),
% 3.71/1.00      inference(subtyping,[status(esa)],[c_32]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1420,plain,
% 3.71/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_839]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_856,plain,
% 3.71/1.00      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.71/1.00      | ~ l1_pre_topc(X1_55)
% 3.71/1.00      | l1_pre_topc(X0_55) ),
% 3.71/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1405,plain,
% 3.71/1.00      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.71/1.00      | l1_pre_topc(X1_55) != iProver_top
% 3.71/1.00      | l1_pre_topc(X0_55) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2231,plain,
% 3.71/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.71/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_1420,c_1405]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4006,plain,
% 3.71/1.00      ( m1_pre_topc(X0_55,sK3) = iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,sK2) != iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_3876,c_42,c_2231]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4007,plain,
% 3.71/1.00      ( m1_pre_topc(X0_55,sK2) != iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,sK3) = iProver_top ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_4006]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4014,plain,
% 3.71/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top
% 3.71/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_1411,c_4007]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4553,plain,
% 3.71/1.00      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_4014,c_42,c_2231]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4,plain,
% 3.71/1.00      ( m1_pre_topc(X0,X1)
% 3.71/1.00      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.71/1.00      | ~ l1_pre_topc(X0)
% 3.71/1.00      | ~ l1_pre_topc(X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_855,plain,
% 3.71/1.00      ( m1_pre_topc(X0_55,X1_55)
% 3.71/1.00      | ~ m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55)))
% 3.71/1.00      | ~ l1_pre_topc(X1_55)
% 3.71/1.00      | ~ l1_pre_topc(X0_55) ),
% 3.71/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1406,plain,
% 3.71/1.00      ( m1_pre_topc(X0_55,X1_55) = iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,g1_pre_topc(u1_struct_0(X1_55),u1_pre_topc(X1_55))) != iProver_top
% 3.71/1.00      | l1_pre_topc(X1_55) != iProver_top
% 3.71/1.00      | l1_pre_topc(X0_55) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_855]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2395,plain,
% 3.71/1.00      ( m1_pre_topc(X0_55,sK2) = iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.71/1.00      | l1_pre_topc(X0_55) != iProver_top
% 3.71/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_843,c_1406]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2417,plain,
% 3.71/1.00      ( l1_pre_topc(X0_55) != iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,sK2) = iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_2395,c_42,c_2231]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2418,plain,
% 3.71/1.00      ( m1_pre_topc(X0_55,sK2) = iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.71/1.00      | l1_pre_topc(X0_55) != iProver_top ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_2417]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2426,plain,
% 3.71/1.00      ( m1_pre_topc(sK3,sK2) = iProver_top
% 3.71/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_1411,c_2418]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_30,negated_conjecture,
% 3.71/1.00      ( m1_pre_topc(sK3,sK0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_841,negated_conjecture,
% 3.71/1.00      ( m1_pre_topc(sK3,sK0) ),
% 3.71/1.00      inference(subtyping,[status(esa)],[c_30]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1418,plain,
% 3.71/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_841]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2230,plain,
% 3.71/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.71/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_1418,c_1405]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2577,plain,
% 3.71/1.00      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_2426,c_42,c_2230]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_17,plain,
% 3.71/1.00      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.71/1.00      | ~ m1_pre_topc(X0,X1)
% 3.71/1.00      | ~ l1_pre_topc(X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_13,plain,
% 3.71/1.00      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.71/1.00      | ~ v1_tsep_1(X0,X2)
% 3.71/1.00      | v1_tsep_1(X0,X1)
% 3.71/1.00      | ~ m1_pre_topc(X0,X2)
% 3.71/1.00      | ~ m1_pre_topc(X1,X2)
% 3.71/1.00      | v2_struct_0(X2)
% 3.71/1.00      | v2_struct_0(X1)
% 3.71/1.00      | ~ l1_pre_topc(X2)
% 3.71/1.00      | ~ v2_pre_topc(X2) ),
% 3.71/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_447,plain,
% 3.71/1.00      ( ~ v1_tsep_1(X0,X1)
% 3.71/1.00      | v1_tsep_1(X0,X2)
% 3.71/1.00      | ~ m1_pre_topc(X0,X1)
% 3.71/1.00      | ~ m1_pre_topc(X2,X1)
% 3.71/1.00      | ~ m1_pre_topc(X0,X2)
% 3.71/1.00      | v2_struct_0(X1)
% 3.71/1.00      | v2_struct_0(X2)
% 3.71/1.00      | ~ l1_pre_topc(X1)
% 3.71/1.00      | ~ l1_pre_topc(X2)
% 3.71/1.00      | ~ v2_pre_topc(X1) ),
% 3.71/1.00      inference(resolution,[status(thm)],[c_17,c_13]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_18,plain,
% 3.71/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.71/1.00      | ~ m1_pre_topc(X2,X0)
% 3.71/1.00      | m1_pre_topc(X2,X1)
% 3.71/1.00      | ~ l1_pre_topc(X1)
% 3.71/1.00      | ~ v2_pre_topc(X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_469,plain,
% 3.71/1.00      ( ~ v1_tsep_1(X0,X1)
% 3.71/1.00      | v1_tsep_1(X0,X2)
% 3.71/1.00      | ~ m1_pre_topc(X2,X1)
% 3.71/1.00      | ~ m1_pre_topc(X0,X2)
% 3.71/1.00      | v2_struct_0(X1)
% 3.71/1.00      | v2_struct_0(X2)
% 3.71/1.00      | ~ l1_pre_topc(X1)
% 3.71/1.00      | ~ v2_pre_topc(X1) ),
% 3.71/1.00      inference(forward_subsumption_resolution,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_447,c_3,c_18]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_828,plain,
% 3.71/1.00      ( ~ v1_tsep_1(X0_55,X1_55)
% 3.71/1.00      | v1_tsep_1(X0_55,X2_55)
% 3.71/1.00      | ~ m1_pre_topc(X2_55,X1_55)
% 3.71/1.00      | ~ m1_pre_topc(X0_55,X2_55)
% 3.71/1.00      | v2_struct_0(X1_55)
% 3.71/1.00      | v2_struct_0(X2_55)
% 3.71/1.00      | ~ l1_pre_topc(X1_55)
% 3.71/1.00      | ~ v2_pre_topc(X1_55) ),
% 3.71/1.00      inference(subtyping,[status(esa)],[c_469]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1431,plain,
% 3.71/1.00      ( v1_tsep_1(X0_55,X1_55) != iProver_top
% 3.71/1.00      | v1_tsep_1(X0_55,X2_55) = iProver_top
% 3.71/1.00      | m1_pre_topc(X2_55,X1_55) != iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 3.71/1.00      | v2_struct_0(X1_55) = iProver_top
% 3.71/1.00      | v2_struct_0(X2_55) = iProver_top
% 3.71/1.00      | l1_pre_topc(X1_55) != iProver_top
% 3.71/1.00      | v2_pre_topc(X1_55) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_828]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6053,plain,
% 3.71/1.00      ( v1_tsep_1(X0_55,sK2) != iProver_top
% 3.71/1.00      | v1_tsep_1(X0_55,sK3) = iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.71/1.00      | v2_struct_0(sK2) = iProver_top
% 3.71/1.00      | v2_struct_0(sK3) = iProver_top
% 3.71/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.71/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_2577,c_1431]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_38,negated_conjecture,
% 3.71/1.00      ( v2_pre_topc(sK0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_41,plain,
% 3.71/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_33,negated_conjecture,
% 3.71/1.00      ( ~ v2_struct_0(sK2) ),
% 3.71/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_46,plain,
% 3.71/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_31,negated_conjecture,
% 3.71/1.00      ( ~ v2_struct_0(sK3) ),
% 3.71/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_48,plain,
% 3.71/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_0,plain,
% 3.71/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.71/1.00      | ~ l1_pre_topc(X1)
% 3.71/1.00      | ~ v2_pre_topc(X1)
% 3.71/1.00      | v2_pre_topc(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_857,plain,
% 3.71/1.00      ( ~ m1_pre_topc(X0_55,X1_55)
% 3.71/1.00      | ~ l1_pre_topc(X1_55)
% 3.71/1.00      | ~ v2_pre_topc(X1_55)
% 3.71/1.00      | v2_pre_topc(X0_55) ),
% 3.71/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1404,plain,
% 3.71/1.00      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 3.71/1.00      | l1_pre_topc(X1_55) != iProver_top
% 3.71/1.00      | v2_pre_topc(X1_55) != iProver_top
% 3.71/1.00      | v2_pre_topc(X0_55) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_857]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1789,plain,
% 3.71/1.00      ( l1_pre_topc(sK0) != iProver_top
% 3.71/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.71/1.00      | v2_pre_topc(sK2) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_1420,c_1404]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_10080,plain,
% 3.71/1.00      ( v1_tsep_1(X0_55,sK2) != iProver_top
% 3.71/1.00      | v1_tsep_1(X0_55,sK3) = iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_6053,c_41,c_42,c_46,c_48,c_1789,c_2231]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_10093,plain,
% 3.71/1.00      ( v1_tsep_1(sK2,sK2) != iProver_top
% 3.71/1.00      | v1_tsep_1(sK2,sK3) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_4553,c_10080]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_10149,plain,
% 3.71/1.00      ( ~ v1_tsep_1(sK2,sK2) | v1_tsep_1(sK2,sK3) ),
% 3.71/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_10093]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4037,plain,
% 3.71/1.00      ( m1_pre_topc(sK2,sK3) | ~ l1_pre_topc(sK2) ),
% 3.71/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4014]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2,plain,
% 3.71/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1,plain,
% 3.71/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_405,plain,
% 3.71/1.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.71/1.00      inference(resolution,[status(thm)],[c_2,c_1]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_830,plain,
% 3.71/1.00      ( ~ l1_pre_topc(X0_55) | u1_struct_0(X0_55) = k2_struct_0(X0_55) ),
% 3.71/1.00      inference(subtyping,[status(esa)],[c_405]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3738,plain,
% 3.71/1.00      ( ~ l1_pre_topc(sK2) | u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_830]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_22,negated_conjecture,
% 3.71/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.71/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_847,negated_conjecture,
% 3.71/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.71/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1414,plain,
% 3.71/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_847]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_23,negated_conjecture,
% 3.71/1.00      ( sK5 = sK6 ),
% 3.71/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_846,negated_conjecture,
% 3.71/1.00      ( sK5 = sK6 ),
% 3.71/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1475,plain,
% 3.71/1.00      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_1414,c_846]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_19,plain,
% 3.71/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.71/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.71/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.71/1.00      | ~ v1_tsep_1(X4,X0)
% 3.71/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.71/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.71/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.71/1.00      | ~ m1_pre_topc(X4,X5)
% 3.71/1.00      | ~ m1_pre_topc(X4,X0)
% 3.71/1.00      | ~ m1_pre_topc(X0,X5)
% 3.71/1.00      | ~ v1_funct_1(X2)
% 3.71/1.00      | v2_struct_0(X5)
% 3.71/1.00      | v2_struct_0(X1)
% 3.71/1.00      | v2_struct_0(X4)
% 3.71/1.00      | v2_struct_0(X0)
% 3.71/1.00      | ~ l1_pre_topc(X5)
% 3.71/1.00      | ~ l1_pre_topc(X1)
% 3.71/1.00      | ~ v2_pre_topc(X5)
% 3.71/1.00      | ~ v2_pre_topc(X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_28,negated_conjecture,
% 3.71/1.00      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_558,plain,
% 3.71/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.71/1.00      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.71/1.00      | ~ v1_tsep_1(X4,X0)
% 3.71/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.71/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.71/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.71/1.00      | ~ m1_pre_topc(X4,X5)
% 3.71/1.00      | ~ m1_pre_topc(X4,X0)
% 3.71/1.00      | ~ m1_pre_topc(X0,X5)
% 3.71/1.00      | ~ v1_funct_1(X2)
% 3.71/1.00      | v2_struct_0(X1)
% 3.71/1.00      | v2_struct_0(X0)
% 3.71/1.00      | v2_struct_0(X5)
% 3.71/1.00      | v2_struct_0(X4)
% 3.71/1.00      | ~ l1_pre_topc(X1)
% 3.71/1.00      | ~ l1_pre_topc(X5)
% 3.71/1.00      | ~ v2_pre_topc(X1)
% 3.71/1.00      | ~ v2_pre_topc(X5)
% 3.71/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.71/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.71/1.00      | sK4 != X2 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_559,plain,
% 3.71/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.71/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.71/1.00      | ~ v1_tsep_1(X0,X3)
% 3.71/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.71/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.71/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.71/1.00      | ~ m1_pre_topc(X0,X2)
% 3.71/1.00      | ~ m1_pre_topc(X0,X3)
% 3.71/1.00      | ~ m1_pre_topc(X3,X2)
% 3.71/1.00      | ~ v1_funct_1(sK4)
% 3.71/1.00      | v2_struct_0(X1)
% 3.71/1.00      | v2_struct_0(X3)
% 3.71/1.00      | v2_struct_0(X2)
% 3.71/1.00      | v2_struct_0(X0)
% 3.71/1.00      | ~ l1_pre_topc(X1)
% 3.71/1.00      | ~ l1_pre_topc(X2)
% 3.71/1.00      | ~ v2_pre_topc(X1)
% 3.71/1.00      | ~ v2_pre_topc(X2)
% 3.71/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.71/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_558]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_29,negated_conjecture,
% 3.71/1.00      ( v1_funct_1(sK4) ),
% 3.71/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_563,plain,
% 3.71/1.00      ( ~ m1_pre_topc(X3,X2)
% 3.71/1.00      | ~ m1_pre_topc(X0,X3)
% 3.71/1.00      | ~ m1_pre_topc(X0,X2)
% 3.71/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.71/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.71/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.71/1.00      | ~ v1_tsep_1(X0,X3)
% 3.71/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.71/1.00      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.71/1.00      | v2_struct_0(X1)
% 3.71/1.00      | v2_struct_0(X3)
% 3.71/1.00      | v2_struct_0(X2)
% 3.71/1.00      | v2_struct_0(X0)
% 3.71/1.00      | ~ l1_pre_topc(X1)
% 3.71/1.00      | ~ l1_pre_topc(X2)
% 3.71/1.00      | ~ v2_pre_topc(X1)
% 3.71/1.00      | ~ v2_pre_topc(X2)
% 3.71/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.71/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_559,c_29]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_564,plain,
% 3.71/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.71/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.71/1.00      | ~ v1_tsep_1(X0,X3)
% 3.71/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.71/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.71/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.71/1.00      | ~ m1_pre_topc(X0,X2)
% 3.71/1.00      | ~ m1_pre_topc(X0,X3)
% 3.71/1.00      | ~ m1_pre_topc(X3,X2)
% 3.71/1.00      | v2_struct_0(X1)
% 3.71/1.00      | v2_struct_0(X0)
% 3.71/1.00      | v2_struct_0(X2)
% 3.71/1.00      | v2_struct_0(X3)
% 3.71/1.00      | ~ l1_pre_topc(X1)
% 3.71/1.00      | ~ l1_pre_topc(X2)
% 3.71/1.00      | ~ v2_pre_topc(X1)
% 3.71/1.00      | ~ v2_pre_topc(X2)
% 3.71/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.71/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_563]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_607,plain,
% 3.71/1.00      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.71/1.00      | r1_tmap_1(X3,X1,sK4,X4)
% 3.71/1.00      | ~ v1_tsep_1(X0,X3)
% 3.71/1.00      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.71/1.00      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.71/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.71/1.00      | ~ m1_pre_topc(X0,X3)
% 3.71/1.00      | ~ m1_pre_topc(X3,X2)
% 3.71/1.00      | v2_struct_0(X1)
% 3.71/1.00      | v2_struct_0(X0)
% 3.71/1.00      | v2_struct_0(X2)
% 3.71/1.00      | v2_struct_0(X3)
% 3.71/1.00      | ~ l1_pre_topc(X1)
% 3.71/1.00      | ~ l1_pre_topc(X2)
% 3.71/1.00      | ~ v2_pre_topc(X1)
% 3.71/1.00      | ~ v2_pre_topc(X2)
% 3.71/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.71/1.00      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.71/1.00      inference(forward_subsumption_resolution,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_564,c_18]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_826,plain,
% 3.71/1.00      ( ~ r1_tmap_1(X0_55,X1_55,k3_tmap_1(X2_55,X1_55,X3_55,X0_55,sK4),X0_56)
% 3.71/1.00      | r1_tmap_1(X3_55,X1_55,sK4,X0_56)
% 3.71/1.00      | ~ v1_tsep_1(X0_55,X3_55)
% 3.71/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
% 3.71/1.00      | ~ m1_subset_1(X0_56,u1_struct_0(X3_55))
% 3.71/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55))))
% 3.71/1.00      | ~ m1_pre_topc(X0_55,X3_55)
% 3.71/1.00      | ~ m1_pre_topc(X3_55,X2_55)
% 3.71/1.00      | v2_struct_0(X1_55)
% 3.71/1.00      | v2_struct_0(X0_55)
% 3.71/1.00      | v2_struct_0(X2_55)
% 3.71/1.00      | v2_struct_0(X3_55)
% 3.71/1.00      | ~ l1_pre_topc(X1_55)
% 3.71/1.00      | ~ l1_pre_topc(X2_55)
% 3.71/1.00      | ~ v2_pre_topc(X1_55)
% 3.71/1.00      | ~ v2_pre_topc(X2_55)
% 3.71/1.00      | u1_struct_0(X1_55) != u1_struct_0(sK1)
% 3.71/1.00      | u1_struct_0(X3_55) != u1_struct_0(sK3) ),
% 3.71/1.00      inference(subtyping,[status(esa)],[c_607]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1433,plain,
% 3.71/1.00      ( u1_struct_0(X0_55) != u1_struct_0(sK1)
% 3.71/1.00      | u1_struct_0(X1_55) != u1_struct_0(sK3)
% 3.71/1.00      | r1_tmap_1(X2_55,X0_55,k3_tmap_1(X3_55,X0_55,X1_55,X2_55,sK4),X0_56) != iProver_top
% 3.71/1.00      | r1_tmap_1(X1_55,X0_55,sK4,X0_56) = iProver_top
% 3.71/1.00      | v1_tsep_1(X2_55,X1_55) != iProver_top
% 3.71/1.00      | m1_subset_1(X0_56,u1_struct_0(X2_55)) != iProver_top
% 3.71/1.00      | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
% 3.71/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_55),u1_struct_0(X0_55)))) != iProver_top
% 3.71/1.00      | m1_pre_topc(X2_55,X1_55) != iProver_top
% 3.71/1.00      | m1_pre_topc(X1_55,X3_55) != iProver_top
% 3.71/1.00      | v2_struct_0(X0_55) = iProver_top
% 3.71/1.00      | v2_struct_0(X2_55) = iProver_top
% 3.71/1.00      | v2_struct_0(X3_55) = iProver_top
% 3.71/1.00      | v2_struct_0(X1_55) = iProver_top
% 3.71/1.00      | l1_pre_topc(X0_55) != iProver_top
% 3.71/1.00      | l1_pre_topc(X3_55) != iProver_top
% 3.71/1.00      | v2_pre_topc(X0_55) != iProver_top
% 3.71/1.00      | v2_pre_topc(X3_55) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_826]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2603,plain,
% 3.71/1.00      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 3.71/1.00      | r1_tmap_1(X1_55,sK1,k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4),X0_56) != iProver_top
% 3.71/1.00      | r1_tmap_1(X0_55,sK1,sK4,X0_56) = iProver_top
% 3.71/1.00      | v1_tsep_1(X1_55,X0_55) != iProver_top
% 3.71/1.00      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 3.71/1.00      | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
% 3.71/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 3.71/1.00      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 3.71/1.00      | v2_struct_0(X1_55) = iProver_top
% 3.71/1.00      | v2_struct_0(X0_55) = iProver_top
% 3.71/1.00      | v2_struct_0(X2_55) = iProver_top
% 3.71/1.00      | v2_struct_0(sK1) = iProver_top
% 3.71/1.00      | l1_pre_topc(X2_55) != iProver_top
% 3.71/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.71/1.00      | v2_pre_topc(X2_55) != iProver_top
% 3.71/1.00      | v2_pre_topc(sK1) != iProver_top ),
% 3.71/1.00      inference(equality_resolution,[status(thm)],[c_1433]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_36,negated_conjecture,
% 3.71/1.00      ( ~ v2_struct_0(sK1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_43,plain,
% 3.71/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_35,negated_conjecture,
% 3.71/1.00      ( v2_pre_topc(sK1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_44,plain,
% 3.71/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_34,negated_conjecture,
% 3.71/1.00      ( l1_pre_topc(sK1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_45,plain,
% 3.71/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2768,plain,
% 3.71/1.00      ( v2_pre_topc(X2_55) != iProver_top
% 3.71/1.00      | v2_struct_0(X2_55) = iProver_top
% 3.71/1.00      | v2_struct_0(X0_55) = iProver_top
% 3.71/1.00      | v2_struct_0(X1_55) = iProver_top
% 3.71/1.00      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 3.71/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 3.71/1.00      | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
% 3.71/1.00      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 3.71/1.00      | v1_tsep_1(X1_55,X0_55) != iProver_top
% 3.71/1.00      | r1_tmap_1(X0_55,sK1,sK4,X0_56) = iProver_top
% 3.71/1.00      | r1_tmap_1(X1_55,sK1,k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4),X0_56) != iProver_top
% 3.71/1.00      | u1_struct_0(X0_55) != u1_struct_0(sK3)
% 3.71/1.00      | l1_pre_topc(X2_55) != iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_2603,c_43,c_44,c_45]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2769,plain,
% 3.71/1.00      ( u1_struct_0(X0_55) != u1_struct_0(sK3)
% 3.71/1.00      | r1_tmap_1(X1_55,sK1,k3_tmap_1(X2_55,sK1,X0_55,X1_55,sK4),X0_56) != iProver_top
% 3.71/1.00      | r1_tmap_1(X0_55,sK1,sK4,X0_56) = iProver_top
% 3.71/1.00      | v1_tsep_1(X1_55,X0_55) != iProver_top
% 3.71/1.00      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 3.71/1.00      | m1_subset_1(X0_56,u1_struct_0(X1_55)) != iProver_top
% 3.71/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK1)))) != iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 3.71/1.00      | m1_pre_topc(X1_55,X0_55) != iProver_top
% 3.71/1.00      | v2_struct_0(X1_55) = iProver_top
% 3.71/1.00      | v2_struct_0(X0_55) = iProver_top
% 3.71/1.00      | v2_struct_0(X2_55) = iProver_top
% 3.71/1.00      | l1_pre_topc(X2_55) != iProver_top
% 3.71/1.00      | v2_pre_topc(X2_55) != iProver_top ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_2768]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2786,plain,
% 3.71/1.00      ( r1_tmap_1(X0_55,sK1,k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4),X0_56) != iProver_top
% 3.71/1.00      | r1_tmap_1(sK3,sK1,sK4,X0_56) = iProver_top
% 3.71/1.00      | v1_tsep_1(X0_55,sK3) != iProver_top
% 3.71/1.00      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 3.71/1.00      | m1_subset_1(X0_56,u1_struct_0(sK3)) != iProver_top
% 3.71/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.71/1.00      | m1_pre_topc(sK3,X1_55) != iProver_top
% 3.71/1.00      | v2_struct_0(X1_55) = iProver_top
% 3.71/1.00      | v2_struct_0(X0_55) = iProver_top
% 3.71/1.00      | v2_struct_0(sK3) = iProver_top
% 3.71/1.00      | l1_pre_topc(X1_55) != iProver_top
% 3.71/1.00      | v2_pre_topc(X1_55) != iProver_top ),
% 3.71/1.00      inference(equality_resolution,[status(thm)],[c_2769]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_27,negated_conjecture,
% 3.71/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.71/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_52,plain,
% 3.71/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2867,plain,
% 3.71/1.00      ( v2_struct_0(X0_55) = iProver_top
% 3.71/1.00      | v2_struct_0(X1_55) = iProver_top
% 3.71/1.00      | m1_pre_topc(sK3,X1_55) != iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.71/1.00      | r1_tmap_1(X0_55,sK1,k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4),X0_56) != iProver_top
% 3.71/1.00      | r1_tmap_1(sK3,sK1,sK4,X0_56) = iProver_top
% 3.71/1.00      | v1_tsep_1(X0_55,sK3) != iProver_top
% 3.71/1.00      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 3.71/1.00      | m1_subset_1(X0_56,u1_struct_0(sK3)) != iProver_top
% 3.71/1.00      | l1_pre_topc(X1_55) != iProver_top
% 3.71/1.00      | v2_pre_topc(X1_55) != iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_2786,c_48,c_52]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2868,plain,
% 3.71/1.00      ( r1_tmap_1(X0_55,sK1,k3_tmap_1(X1_55,sK1,sK3,X0_55,sK4),X0_56) != iProver_top
% 3.71/1.00      | r1_tmap_1(sK3,sK1,sK4,X0_56) = iProver_top
% 3.71/1.00      | v1_tsep_1(X0_55,sK3) != iProver_top
% 3.71/1.00      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 3.71/1.00      | m1_subset_1(X0_56,u1_struct_0(sK3)) != iProver_top
% 3.71/1.00      | m1_pre_topc(X0_55,sK3) != iProver_top
% 3.71/1.00      | m1_pre_topc(sK3,X1_55) != iProver_top
% 3.71/1.00      | v2_struct_0(X1_55) = iProver_top
% 3.71/1.00      | v2_struct_0(X0_55) = iProver_top
% 3.71/1.00      | l1_pre_topc(X1_55) != iProver_top
% 3.71/1.00      | v2_pre_topc(X1_55) != iProver_top ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_2867]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2884,plain,
% 3.71/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.71/1.00      | v1_tsep_1(sK2,sK3) != iProver_top
% 3.71/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.71/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.71/1.00      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.71/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.71/1.00      | v2_struct_0(sK0) = iProver_top
% 3.71/1.00      | v2_struct_0(sK2) = iProver_top
% 3.71/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.71/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_1475,c_2868]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_39,negated_conjecture,
% 3.71/1.00      ( ~ v2_struct_0(sK0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_40,plain,
% 3.71/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_49,plain,
% 3.71/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_25,negated_conjecture,
% 3.71/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_53,plain,
% 3.71/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_21,negated_conjecture,
% 3.71/1.00      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.71/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_56,plain,
% 3.71/1.00      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_24,negated_conjecture,
% 3.71/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_845,negated_conjecture,
% 3.71/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.71/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1415,plain,
% 3.71/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_845]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1456,plain,
% 3.71/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_1415,c_846]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3645,plain,
% 3.71/1.00      ( m1_pre_topc(sK2,sK3) != iProver_top
% 3.71/1.00      | v1_tsep_1(sK2,sK3) != iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_2884,c_40,c_41,c_42,c_46,c_49,c_53,c_56,c_1456]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3646,plain,
% 3.71/1.00      ( v1_tsep_1(sK2,sK3) != iProver_top
% 3.71/1.00      | m1_pre_topc(sK2,sK3) != iProver_top ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_3645]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3647,plain,
% 3.71/1.00      ( ~ v1_tsep_1(sK2,sK3) | ~ m1_pre_topc(sK2,sK3) ),
% 3.71/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3646]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2955,plain,
% 3.71/1.00      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_850]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2241,plain,
% 3.71/1.00      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 3.71/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2231]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1790,plain,
% 3.71/1.00      ( ~ l1_pre_topc(sK0) | ~ v2_pre_topc(sK0) | v2_pre_topc(sK2) ),
% 3.71/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1789]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(contradiction,plain,
% 3.71/1.00      ( $false ),
% 3.71/1.00      inference(minisat,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_15014,c_10149,c_4037,c_3738,c_3647,c_2955,c_2241,
% 3.71/1.00                 c_1790,c_37,c_38]) ).
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  ------                               Statistics
% 3.71/1.00  
% 3.71/1.00  ------ General
% 3.71/1.00  
% 3.71/1.00  abstr_ref_over_cycles:                  0
% 3.71/1.00  abstr_ref_under_cycles:                 0
% 3.71/1.00  gc_basic_clause_elim:                   0
% 3.71/1.00  forced_gc_time:                         0
% 3.71/1.00  parsing_time:                           0.011
% 3.71/1.00  unif_index_cands_time:                  0.
% 3.71/1.00  unif_index_add_time:                    0.
% 3.71/1.00  orderings_time:                         0.
% 3.71/1.00  out_proof_time:                         0.017
% 3.71/1.00  total_time:                             0.434
% 3.71/1.00  num_of_symbols:                         61
% 3.71/1.00  num_of_terms:                           8327
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing
% 3.71/1.00  
% 3.71/1.00  num_of_splits:                          0
% 3.71/1.00  num_of_split_atoms:                     0
% 3.71/1.00  num_of_reused_defs:                     0
% 3.71/1.00  num_eq_ax_congr_red:                    20
% 3.71/1.00  num_of_sem_filtered_clauses:            1
% 3.71/1.00  num_of_subtypes:                        3
% 3.71/1.00  monotx_restored_types:                  0
% 3.71/1.00  sat_num_of_epr_types:                   0
% 3.71/1.00  sat_num_of_non_cyclic_types:            0
% 3.71/1.00  sat_guarded_non_collapsed_types:        0
% 3.71/1.00  num_pure_diseq_elim:                    0
% 3.71/1.00  simp_replaced_by:                       0
% 3.71/1.00  res_preprocessed:                       170
% 3.71/1.00  prep_upred:                             0
% 3.71/1.00  prep_unflattend:                        3
% 3.71/1.00  smt_new_axioms:                         0
% 3.71/1.00  pred_elim_cands:                        7
% 3.71/1.00  pred_elim:                              5
% 3.71/1.00  pred_elim_cl:                           7
% 3.71/1.00  pred_elim_cycles:                       7
% 3.71/1.00  merged_defs:                            0
% 3.71/1.00  merged_defs_ncl:                        0
% 3.71/1.00  bin_hyper_res:                          0
% 3.71/1.00  prep_cycles:                            4
% 3.71/1.00  pred_elim_time:                         0.009
% 3.71/1.00  splitting_time:                         0.
% 3.71/1.00  sem_filter_time:                        0.
% 3.71/1.00  monotx_time:                            0.
% 3.71/1.00  subtype_inf_time:                       0.001
% 3.71/1.00  
% 3.71/1.00  ------ Problem properties
% 3.71/1.00  
% 3.71/1.00  clauses:                                32
% 3.71/1.00  conjectures:                            17
% 3.71/1.00  epr:                                    17
% 3.71/1.00  horn:                                   26
% 3.71/1.00  ground:                                 17
% 3.71/1.00  unary:                                  17
% 3.71/1.00  binary:                                 2
% 3.71/1.00  lits:                                   112
% 3.71/1.00  lits_eq:                                9
% 3.71/1.00  fd_pure:                                0
% 3.71/1.00  fd_pseudo:                              0
% 3.71/1.00  fd_cond:                                0
% 3.71/1.00  fd_pseudo_cond:                         0
% 3.71/1.00  ac_symbols:                             0
% 3.71/1.00  
% 3.71/1.00  ------ Propositional Solver
% 3.71/1.00  
% 3.71/1.00  prop_solver_calls:                      31
% 3.71/1.00  prop_fast_solver_calls:                 2184
% 3.71/1.00  smt_solver_calls:                       0
% 3.71/1.00  smt_fast_solver_calls:                  0
% 3.71/1.00  prop_num_of_clauses:                    4373
% 3.71/1.00  prop_preprocess_simplified:             8919
% 3.71/1.00  prop_fo_subsumed:                       166
% 3.71/1.00  prop_solver_time:                       0.
% 3.71/1.00  smt_solver_time:                        0.
% 3.71/1.00  smt_fast_solver_time:                   0.
% 3.71/1.00  prop_fast_solver_time:                  0.
% 3.71/1.00  prop_unsat_core_time:                   0.
% 3.71/1.00  
% 3.71/1.00  ------ QBF
% 3.71/1.00  
% 3.71/1.00  qbf_q_res:                              0
% 3.71/1.00  qbf_num_tautologies:                    0
% 3.71/1.00  qbf_prep_cycles:                        0
% 3.71/1.00  
% 3.71/1.00  ------ BMC1
% 3.71/1.00  
% 3.71/1.00  bmc1_current_bound:                     -1
% 3.71/1.00  bmc1_last_solved_bound:                 -1
% 3.71/1.00  bmc1_unsat_core_size:                   -1
% 3.71/1.00  bmc1_unsat_core_parents_size:           -1
% 3.71/1.00  bmc1_merge_next_fun:                    0
% 3.71/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.71/1.00  
% 3.71/1.00  ------ Instantiation
% 3.71/1.00  
% 3.71/1.00  inst_num_of_clauses:                    1188
% 3.71/1.00  inst_num_in_passive:                    88
% 3.71/1.00  inst_num_in_active:                     743
% 3.71/1.00  inst_num_in_unprocessed:                356
% 3.71/1.00  inst_num_of_loops:                      783
% 3.71/1.00  inst_num_of_learning_restarts:          0
% 3.71/1.00  inst_num_moves_active_passive:          33
% 3.71/1.00  inst_lit_activity:                      0
% 3.71/1.00  inst_lit_activity_moves:                0
% 3.71/1.00  inst_num_tautologies:                   0
% 3.71/1.00  inst_num_prop_implied:                  0
% 3.71/1.00  inst_num_existing_simplified:           0
% 3.71/1.00  inst_num_eq_res_simplified:             0
% 3.71/1.00  inst_num_child_elim:                    0
% 3.71/1.00  inst_num_of_dismatching_blockings:      569
% 3.71/1.00  inst_num_of_non_proper_insts:           1757
% 3.71/1.00  inst_num_of_duplicates:                 0
% 3.71/1.00  inst_inst_num_from_inst_to_res:         0
% 3.71/1.00  inst_dismatching_checking_time:         0.
% 3.71/1.00  
% 3.71/1.00  ------ Resolution
% 3.71/1.00  
% 3.71/1.00  res_num_of_clauses:                     0
% 3.71/1.00  res_num_in_passive:                     0
% 3.71/1.00  res_num_in_active:                      0
% 3.71/1.00  res_num_of_loops:                       174
% 3.71/1.00  res_forward_subset_subsumed:            240
% 3.71/1.00  res_backward_subset_subsumed:           2
% 3.71/1.00  res_forward_subsumed:                   0
% 3.71/1.00  res_backward_subsumed:                  0
% 3.71/1.00  res_forward_subsumption_resolution:     4
% 3.71/1.00  res_backward_subsumption_resolution:    0
% 3.71/1.00  res_clause_to_clause_subsumption:       1898
% 3.71/1.00  res_orphan_elimination:                 0
% 3.71/1.00  res_tautology_del:                      307
% 3.71/1.00  res_num_eq_res_simplified:              0
% 3.71/1.00  res_num_sel_changes:                    0
% 3.71/1.00  res_moves_from_active_to_pass:          0
% 3.71/1.00  
% 3.71/1.00  ------ Superposition
% 3.71/1.00  
% 3.71/1.00  sup_time_total:                         0.
% 3.71/1.00  sup_time_generating:                    0.
% 3.71/1.00  sup_time_sim_full:                      0.
% 3.71/1.00  sup_time_sim_immed:                     0.
% 3.71/1.00  
% 3.71/1.00  sup_num_of_clauses:                     321
% 3.71/1.00  sup_num_in_active:                      134
% 3.71/1.00  sup_num_in_passive:                     187
% 3.71/1.00  sup_num_of_loops:                       156
% 3.71/1.00  sup_fw_superposition:                   245
% 3.71/1.00  sup_bw_superposition:                   201
% 3.71/1.00  sup_immediate_simplified:               126
% 3.71/1.00  sup_given_eliminated:                   0
% 3.71/1.00  comparisons_done:                       0
% 3.71/1.00  comparisons_avoided:                    0
% 3.71/1.00  
% 3.71/1.00  ------ Simplifications
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  sim_fw_subset_subsumed:                 51
% 3.71/1.00  sim_bw_subset_subsumed:                 29
% 3.71/1.00  sim_fw_subsumed:                        26
% 3.71/1.00  sim_bw_subsumed:                        4
% 3.71/1.00  sim_fw_subsumption_res:                 1
% 3.71/1.00  sim_bw_subsumption_res:                 2
% 3.71/1.00  sim_tautology_del:                      28
% 3.71/1.00  sim_eq_tautology_del:                   1
% 3.71/1.00  sim_eq_res_simp:                        0
% 3.71/1.00  sim_fw_demodulated:                     1
% 3.71/1.00  sim_bw_demodulated:                     21
% 3.71/1.00  sim_light_normalised:                   71
% 3.71/1.00  sim_joinable_taut:                      0
% 3.71/1.00  sim_joinable_simp:                      0
% 3.71/1.00  sim_ac_normalised:                      0
% 3.71/1.00  sim_smt_subsumption:                    0
% 3.71/1.00  
%------------------------------------------------------------------------------
