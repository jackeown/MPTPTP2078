%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:36 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  210 (2140 expanded)
%              Number of clauses        :  120 ( 448 expanded)
%              Number of leaves         :   23 ( 965 expanded)
%              Depth                    :   25
%              Number of atoms          : 1254 (30236 expanded)
%              Number of equality atoms :  401 (4624 expanded)
%              Maximal formula depth    :   32 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f54,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f44,f53,f52,f51,f50,f49,f48,f47])).

fof(f90,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
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
    inference(equality_resolution,[],[f72])).

fof(f84,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f77,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f81,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f75,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f70,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f54])).

fof(f73,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f74,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3) )
                    & ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_19,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2071,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_20,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2121,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2071,c_20])).

cnf(c_11,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_16,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X6)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_595,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v3_pre_topc(X6,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ r1_tarski(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X6)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_596,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,X5)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_600,plain,
    ( ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v3_pre_topc(X5,X3)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_596,c_26])).

cnf(c_601,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_600])).

cnf(c_653,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,X5)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | X5 != X6
    | u1_struct_0(X0) != X7
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(resolution_lifted,[status(thm)],[c_2,c_601])).

cnf(c_654,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ v3_pre_topc(X5,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,X5)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_932,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,X5)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | X3 != X6
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3)
    | k2_struct_0(X6) != X5 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_654])).

cnf(c_933,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,k2_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_932])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_6,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_402,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_6,c_5])).

cnf(c_983,plain,
    ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
    | r1_tmap_1(X3,X1,sK4,X4)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ r2_hidden(X4,k2_struct_0(X3))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_933,c_3,c_7,c_402])).

cnf(c_2053,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK4),X4) != iProver_top
    | r1_tmap_1(X1,X0,sK4,X4) = iProver_top
    | m1_pre_topc(X1,X3) != iProver_top
    | m1_pre_topc(X2,X3) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | r2_hidden(X4,k2_struct_0(X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_983])).

cnf(c_2518,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2053])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_40,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_41,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_42,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3047,plain,
    ( v2_pre_topc(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | l1_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2518,c_40,c_41,c_42])).

cnf(c_3048,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
    | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3047])).

cnf(c_3067,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3048])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_45,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_49,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7215,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3067,c_45,c_49])).

cnf(c_7216,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7215])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2067,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2079,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3239,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2067,c_2079])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_39,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3560,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3239,c_39])).

cnf(c_4,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_413,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_6,c_4])).

cnf(c_2055,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_3565,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3560,c_2055])).

cnf(c_7221,plain,
    ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
    | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(sK3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7216,c_3565])).

cnf(c_7238,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
    | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2121,c_7221])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2065,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2073,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3910,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2065,c_2073])).

cnf(c_23,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3916,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = sK3
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3910,c_23])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_37,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_38,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_43,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3993,plain,
    ( k1_tsep_1(sK0,sK2,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3916,c_37,c_38,c_39,c_43])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2074,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4444,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK2,sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3993,c_2074])).

cnf(c_44,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5109,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4444,c_37,c_38,c_39,c_43,c_44])).

cnf(c_5114,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK3,sK2,sK2)
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5109,c_2073])).

cnf(c_3240,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2065,c_2079])).

cnf(c_3567,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3240,c_39])).

cnf(c_3572,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_3567,c_2055])).

cnf(c_4249,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3572,c_23])).

cnf(c_5122,plain,
    ( k1_tsep_1(sK3,sK2,sK2) = sK3
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5114,c_3572,c_4249])).

cnf(c_2080,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3886,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2067,c_2080])).

cnf(c_5130,plain,
    ( k1_tsep_1(sK3,sK2,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5122,c_38,c_39,c_43,c_45,c_3239,c_3886])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2075,plain,
    ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) != iProver_top
    | v1_pre_topc(k1_tsep_1(X0,X1,X2)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(k1_tsep_1(X0,X1,X2)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5422,plain,
    ( u1_struct_0(k1_tsep_1(sK3,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | v1_pre_topc(k1_tsep_1(sK3,sK2,sK2)) != iProver_top
    | v2_struct_0(k1_tsep_1(sK3,sK2,sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5130,c_2075])).

cnf(c_5431,plain,
    ( k2_xboole_0(k2_struct_0(sK2),k2_struct_0(sK2)) = k2_struct_0(sK3)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | v1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5422,c_3565,c_3572,c_5130])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_5432,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | m1_pre_topc(sK2,sK3) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top
    | v1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5431,c_0])).

cnf(c_46,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2077,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3365,plain,
    ( v1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_2077])).

cnf(c_3368,plain,
    ( v1_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3365,c_39,c_3240])).

cnf(c_3887,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2065,c_2080])).

cnf(c_5421,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK2,sK2)) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3993,c_2075])).

cnf(c_5448,plain,
    ( k2_xboole_0(k2_struct_0(sK2),k2_struct_0(sK2)) = k2_struct_0(sK3)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5421,c_3565,c_3572,c_3993])).

cnf(c_5449,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5448,c_0])).

cnf(c_5518,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5432,c_37,c_38,c_39,c_43,c_44,c_45,c_46,c_3368,c_3887,c_5449])).

cnf(c_2056,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_5529,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5518,c_2056])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2069,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4150,plain,
    ( m1_subset_1(sK5,k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3565,c_2069])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2081,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3255,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2069,c_2081])).

cnf(c_50,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2408,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r2_hidden(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2409,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2408])).

cnf(c_8,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_388,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_6,c_8])).

cnf(c_2531,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_2532,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2531])).

cnf(c_3613,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3255,c_39,c_45,c_50,c_2409,c_2532,c_3239])).

cnf(c_4148,plain,
    ( r2_hidden(sK5,k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3565,c_3613])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2070,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2108,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2070,c_20])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_53,plain,
    ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7238,c_5529,c_4444,c_4150,c_4148,c_3240,c_2108,c_53,c_46,c_44,c_43,c_39,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:22:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.01/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/1.00  
% 3.01/1.00  ------  iProver source info
% 3.01/1.00  
% 3.01/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.01/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/1.00  git: non_committed_changes: false
% 3.01/1.00  git: last_make_outside_of_git: false
% 3.01/1.00  
% 3.01/1.00  ------ 
% 3.01/1.00  
% 3.01/1.00  ------ Input Options
% 3.01/1.00  
% 3.01/1.00  --out_options                           all
% 3.01/1.00  --tptp_safe_out                         true
% 3.01/1.00  --problem_path                          ""
% 3.01/1.00  --include_path                          ""
% 3.01/1.00  --clausifier                            res/vclausify_rel
% 3.01/1.00  --clausifier_options                    --mode clausify
% 3.01/1.00  --stdin                                 false
% 3.01/1.00  --stats_out                             all
% 3.01/1.00  
% 3.01/1.00  ------ General Options
% 3.01/1.00  
% 3.01/1.00  --fof                                   false
% 3.01/1.00  --time_out_real                         305.
% 3.01/1.00  --time_out_virtual                      -1.
% 3.01/1.00  --symbol_type_check                     false
% 3.01/1.00  --clausify_out                          false
% 3.01/1.00  --sig_cnt_out                           false
% 3.01/1.00  --trig_cnt_out                          false
% 3.01/1.00  --trig_cnt_out_tolerance                1.
% 3.01/1.00  --trig_cnt_out_sk_spl                   false
% 3.01/1.00  --abstr_cl_out                          false
% 3.01/1.00  
% 3.01/1.00  ------ Global Options
% 3.01/1.00  
% 3.01/1.00  --schedule                              default
% 3.01/1.00  --add_important_lit                     false
% 3.01/1.00  --prop_solver_per_cl                    1000
% 3.01/1.00  --min_unsat_core                        false
% 3.01/1.00  --soft_assumptions                      false
% 3.01/1.00  --soft_lemma_size                       3
% 3.01/1.00  --prop_impl_unit_size                   0
% 3.01/1.00  --prop_impl_unit                        []
% 3.01/1.00  --share_sel_clauses                     true
% 3.01/1.00  --reset_solvers                         false
% 3.01/1.00  --bc_imp_inh                            [conj_cone]
% 3.01/1.00  --conj_cone_tolerance                   3.
% 3.01/1.00  --extra_neg_conj                        none
% 3.01/1.00  --large_theory_mode                     true
% 3.01/1.00  --prolific_symb_bound                   200
% 3.01/1.00  --lt_threshold                          2000
% 3.01/1.00  --clause_weak_htbl                      true
% 3.01/1.00  --gc_record_bc_elim                     false
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing Options
% 3.01/1.00  
% 3.01/1.00  --preprocessing_flag                    true
% 3.01/1.00  --time_out_prep_mult                    0.1
% 3.01/1.00  --splitting_mode                        input
% 3.01/1.00  --splitting_grd                         true
% 3.01/1.00  --splitting_cvd                         false
% 3.01/1.00  --splitting_cvd_svl                     false
% 3.01/1.00  --splitting_nvd                         32
% 3.01/1.00  --sub_typing                            true
% 3.01/1.00  --prep_gs_sim                           true
% 3.01/1.00  --prep_unflatten                        true
% 3.01/1.00  --prep_res_sim                          true
% 3.01/1.00  --prep_upred                            true
% 3.01/1.00  --prep_sem_filter                       exhaustive
% 3.01/1.00  --prep_sem_filter_out                   false
% 3.01/1.00  --pred_elim                             true
% 3.01/1.00  --res_sim_input                         true
% 3.01/1.00  --eq_ax_congr_red                       true
% 3.01/1.00  --pure_diseq_elim                       true
% 3.01/1.00  --brand_transform                       false
% 3.01/1.00  --non_eq_to_eq                          false
% 3.01/1.00  --prep_def_merge                        true
% 3.01/1.00  --prep_def_merge_prop_impl              false
% 3.01/1.00  --prep_def_merge_mbd                    true
% 3.01/1.00  --prep_def_merge_tr_red                 false
% 3.01/1.00  --prep_def_merge_tr_cl                  false
% 3.01/1.00  --smt_preprocessing                     true
% 3.01/1.00  --smt_ac_axioms                         fast
% 3.01/1.00  --preprocessed_out                      false
% 3.01/1.00  --preprocessed_stats                    false
% 3.01/1.00  
% 3.01/1.00  ------ Abstraction refinement Options
% 3.01/1.00  
% 3.01/1.00  --abstr_ref                             []
% 3.01/1.00  --abstr_ref_prep                        false
% 3.01/1.00  --abstr_ref_until_sat                   false
% 3.01/1.00  --abstr_ref_sig_restrict                funpre
% 3.01/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.00  --abstr_ref_under                       []
% 3.01/1.00  
% 3.01/1.00  ------ SAT Options
% 3.01/1.00  
% 3.01/1.00  --sat_mode                              false
% 3.01/1.00  --sat_fm_restart_options                ""
% 3.01/1.00  --sat_gr_def                            false
% 3.01/1.00  --sat_epr_types                         true
% 3.01/1.00  --sat_non_cyclic_types                  false
% 3.01/1.00  --sat_finite_models                     false
% 3.01/1.00  --sat_fm_lemmas                         false
% 3.01/1.00  --sat_fm_prep                           false
% 3.01/1.00  --sat_fm_uc_incr                        true
% 3.01/1.00  --sat_out_model                         small
% 3.01/1.00  --sat_out_clauses                       false
% 3.01/1.00  
% 3.01/1.00  ------ QBF Options
% 3.01/1.00  
% 3.01/1.00  --qbf_mode                              false
% 3.01/1.00  --qbf_elim_univ                         false
% 3.01/1.00  --qbf_dom_inst                          none
% 3.01/1.00  --qbf_dom_pre_inst                      false
% 3.01/1.00  --qbf_sk_in                             false
% 3.01/1.00  --qbf_pred_elim                         true
% 3.01/1.00  --qbf_split                             512
% 3.01/1.00  
% 3.01/1.00  ------ BMC1 Options
% 3.01/1.00  
% 3.01/1.00  --bmc1_incremental                      false
% 3.01/1.00  --bmc1_axioms                           reachable_all
% 3.01/1.00  --bmc1_min_bound                        0
% 3.01/1.00  --bmc1_max_bound                        -1
% 3.01/1.00  --bmc1_max_bound_default                -1
% 3.01/1.00  --bmc1_symbol_reachability              true
% 3.01/1.00  --bmc1_property_lemmas                  false
% 3.01/1.00  --bmc1_k_induction                      false
% 3.01/1.00  --bmc1_non_equiv_states                 false
% 3.01/1.00  --bmc1_deadlock                         false
% 3.01/1.00  --bmc1_ucm                              false
% 3.01/1.00  --bmc1_add_unsat_core                   none
% 3.01/1.00  --bmc1_unsat_core_children              false
% 3.01/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.00  --bmc1_out_stat                         full
% 3.01/1.00  --bmc1_ground_init                      false
% 3.01/1.00  --bmc1_pre_inst_next_state              false
% 3.01/1.00  --bmc1_pre_inst_state                   false
% 3.01/1.00  --bmc1_pre_inst_reach_state             false
% 3.01/1.00  --bmc1_out_unsat_core                   false
% 3.01/1.00  --bmc1_aig_witness_out                  false
% 3.01/1.00  --bmc1_verbose                          false
% 3.01/1.00  --bmc1_dump_clauses_tptp                false
% 3.01/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.00  --bmc1_dump_file                        -
% 3.01/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.00  --bmc1_ucm_extend_mode                  1
% 3.01/1.00  --bmc1_ucm_init_mode                    2
% 3.01/1.00  --bmc1_ucm_cone_mode                    none
% 3.01/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.00  --bmc1_ucm_relax_model                  4
% 3.01/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.00  --bmc1_ucm_layered_model                none
% 3.01/1.00  --bmc1_ucm_max_lemma_size               10
% 3.01/1.00  
% 3.01/1.00  ------ AIG Options
% 3.01/1.00  
% 3.01/1.00  --aig_mode                              false
% 3.01/1.00  
% 3.01/1.00  ------ Instantiation Options
% 3.01/1.00  
% 3.01/1.00  --instantiation_flag                    true
% 3.01/1.00  --inst_sos_flag                         false
% 3.01/1.00  --inst_sos_phase                        true
% 3.01/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel_side                     num_symb
% 3.01/1.00  --inst_solver_per_active                1400
% 3.01/1.00  --inst_solver_calls_frac                1.
% 3.01/1.00  --inst_passive_queue_type               priority_queues
% 3.01/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.00  --inst_passive_queues_freq              [25;2]
% 3.01/1.00  --inst_dismatching                      true
% 3.01/1.00  --inst_eager_unprocessed_to_passive     true
% 3.01/1.00  --inst_prop_sim_given                   true
% 3.01/1.00  --inst_prop_sim_new                     false
% 3.01/1.00  --inst_subs_new                         false
% 3.01/1.00  --inst_eq_res_simp                      false
% 3.01/1.00  --inst_subs_given                       false
% 3.01/1.00  --inst_orphan_elimination               true
% 3.01/1.00  --inst_learning_loop_flag               true
% 3.01/1.00  --inst_learning_start                   3000
% 3.01/1.00  --inst_learning_factor                  2
% 3.01/1.00  --inst_start_prop_sim_after_learn       3
% 3.01/1.00  --inst_sel_renew                        solver
% 3.01/1.00  --inst_lit_activity_flag                true
% 3.01/1.00  --inst_restr_to_given                   false
% 3.01/1.00  --inst_activity_threshold               500
% 3.01/1.00  --inst_out_proof                        true
% 3.01/1.00  
% 3.01/1.00  ------ Resolution Options
% 3.01/1.00  
% 3.01/1.00  --resolution_flag                       true
% 3.01/1.00  --res_lit_sel                           adaptive
% 3.01/1.00  --res_lit_sel_side                      none
% 3.01/1.00  --res_ordering                          kbo
% 3.01/1.00  --res_to_prop_solver                    active
% 3.01/1.00  --res_prop_simpl_new                    false
% 3.01/1.00  --res_prop_simpl_given                  true
% 3.01/1.00  --res_passive_queue_type                priority_queues
% 3.01/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.00  --res_passive_queues_freq               [15;5]
% 3.01/1.00  --res_forward_subs                      full
% 3.01/1.00  --res_backward_subs                     full
% 3.01/1.00  --res_forward_subs_resolution           true
% 3.01/1.00  --res_backward_subs_resolution          true
% 3.01/1.00  --res_orphan_elimination                true
% 3.01/1.00  --res_time_limit                        2.
% 3.01/1.00  --res_out_proof                         true
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Options
% 3.01/1.00  
% 3.01/1.00  --superposition_flag                    true
% 3.01/1.00  --sup_passive_queue_type                priority_queues
% 3.01/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.00  --demod_completeness_check              fast
% 3.01/1.00  --demod_use_ground                      true
% 3.01/1.00  --sup_to_prop_solver                    passive
% 3.01/1.00  --sup_prop_simpl_new                    true
% 3.01/1.00  --sup_prop_simpl_given                  true
% 3.01/1.00  --sup_fun_splitting                     false
% 3.01/1.00  --sup_smt_interval                      50000
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Simplification Setup
% 3.01/1.00  
% 3.01/1.00  --sup_indices_passive                   []
% 3.01/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_full_bw                           [BwDemod]
% 3.01/1.00  --sup_immed_triv                        [TrivRules]
% 3.01/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_immed_bw_main                     []
% 3.01/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  
% 3.01/1.00  ------ Combination Options
% 3.01/1.00  
% 3.01/1.00  --comb_res_mult                         3
% 3.01/1.00  --comb_sup_mult                         2
% 3.01/1.00  --comb_inst_mult                        10
% 3.01/1.00  
% 3.01/1.00  ------ Debug Options
% 3.01/1.00  
% 3.01/1.00  --dbg_backtrace                         false
% 3.01/1.00  --dbg_dump_prop_clauses                 false
% 3.01/1.00  --dbg_dump_prop_clauses_file            -
% 3.01/1.00  --dbg_out_stat                          false
% 3.01/1.00  ------ Parsing...
% 3.01/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.00  ------ Proving...
% 3.01/1.00  ------ Problem Properties 
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  clauses                                 32
% 3.01/1.00  conjectures                             17
% 3.01/1.00  EPR                                     15
% 3.01/1.00  Horn                                    25
% 3.01/1.00  unary                                   18
% 3.01/1.00  binary                                  2
% 3.01/1.00  lits                                    116
% 3.01/1.00  lits eq                                 12
% 3.01/1.00  fd_pure                                 0
% 3.01/1.00  fd_pseudo                               0
% 3.01/1.00  fd_cond                                 0
% 3.01/1.00  fd_pseudo_cond                          1
% 3.01/1.00  AC symbols                              0
% 3.01/1.00  
% 3.01/1.00  ------ Schedule dynamic 5 is on 
% 3.01/1.00  
% 3.01/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  ------ 
% 3.01/1.00  Current options:
% 3.01/1.00  ------ 
% 3.01/1.00  
% 3.01/1.00  ------ Input Options
% 3.01/1.00  
% 3.01/1.00  --out_options                           all
% 3.01/1.00  --tptp_safe_out                         true
% 3.01/1.00  --problem_path                          ""
% 3.01/1.00  --include_path                          ""
% 3.01/1.00  --clausifier                            res/vclausify_rel
% 3.01/1.00  --clausifier_options                    --mode clausify
% 3.01/1.00  --stdin                                 false
% 3.01/1.00  --stats_out                             all
% 3.01/1.00  
% 3.01/1.00  ------ General Options
% 3.01/1.00  
% 3.01/1.00  --fof                                   false
% 3.01/1.00  --time_out_real                         305.
% 3.01/1.00  --time_out_virtual                      -1.
% 3.01/1.00  --symbol_type_check                     false
% 3.01/1.00  --clausify_out                          false
% 3.01/1.00  --sig_cnt_out                           false
% 3.01/1.00  --trig_cnt_out                          false
% 3.01/1.00  --trig_cnt_out_tolerance                1.
% 3.01/1.00  --trig_cnt_out_sk_spl                   false
% 3.01/1.00  --abstr_cl_out                          false
% 3.01/1.00  
% 3.01/1.00  ------ Global Options
% 3.01/1.00  
% 3.01/1.00  --schedule                              default
% 3.01/1.00  --add_important_lit                     false
% 3.01/1.00  --prop_solver_per_cl                    1000
% 3.01/1.00  --min_unsat_core                        false
% 3.01/1.00  --soft_assumptions                      false
% 3.01/1.00  --soft_lemma_size                       3
% 3.01/1.00  --prop_impl_unit_size                   0
% 3.01/1.00  --prop_impl_unit                        []
% 3.01/1.00  --share_sel_clauses                     true
% 3.01/1.00  --reset_solvers                         false
% 3.01/1.00  --bc_imp_inh                            [conj_cone]
% 3.01/1.00  --conj_cone_tolerance                   3.
% 3.01/1.00  --extra_neg_conj                        none
% 3.01/1.00  --large_theory_mode                     true
% 3.01/1.00  --prolific_symb_bound                   200
% 3.01/1.00  --lt_threshold                          2000
% 3.01/1.00  --clause_weak_htbl                      true
% 3.01/1.00  --gc_record_bc_elim                     false
% 3.01/1.00  
% 3.01/1.00  ------ Preprocessing Options
% 3.01/1.00  
% 3.01/1.00  --preprocessing_flag                    true
% 3.01/1.00  --time_out_prep_mult                    0.1
% 3.01/1.00  --splitting_mode                        input
% 3.01/1.00  --splitting_grd                         true
% 3.01/1.00  --splitting_cvd                         false
% 3.01/1.00  --splitting_cvd_svl                     false
% 3.01/1.00  --splitting_nvd                         32
% 3.01/1.00  --sub_typing                            true
% 3.01/1.00  --prep_gs_sim                           true
% 3.01/1.00  --prep_unflatten                        true
% 3.01/1.00  --prep_res_sim                          true
% 3.01/1.00  --prep_upred                            true
% 3.01/1.00  --prep_sem_filter                       exhaustive
% 3.01/1.00  --prep_sem_filter_out                   false
% 3.01/1.00  --pred_elim                             true
% 3.01/1.00  --res_sim_input                         true
% 3.01/1.00  --eq_ax_congr_red                       true
% 3.01/1.00  --pure_diseq_elim                       true
% 3.01/1.00  --brand_transform                       false
% 3.01/1.00  --non_eq_to_eq                          false
% 3.01/1.00  --prep_def_merge                        true
% 3.01/1.00  --prep_def_merge_prop_impl              false
% 3.01/1.00  --prep_def_merge_mbd                    true
% 3.01/1.00  --prep_def_merge_tr_red                 false
% 3.01/1.00  --prep_def_merge_tr_cl                  false
% 3.01/1.00  --smt_preprocessing                     true
% 3.01/1.00  --smt_ac_axioms                         fast
% 3.01/1.00  --preprocessed_out                      false
% 3.01/1.00  --preprocessed_stats                    false
% 3.01/1.00  
% 3.01/1.00  ------ Abstraction refinement Options
% 3.01/1.00  
% 3.01/1.00  --abstr_ref                             []
% 3.01/1.00  --abstr_ref_prep                        false
% 3.01/1.00  --abstr_ref_until_sat                   false
% 3.01/1.00  --abstr_ref_sig_restrict                funpre
% 3.01/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.00  --abstr_ref_under                       []
% 3.01/1.00  
% 3.01/1.00  ------ SAT Options
% 3.01/1.00  
% 3.01/1.00  --sat_mode                              false
% 3.01/1.00  --sat_fm_restart_options                ""
% 3.01/1.00  --sat_gr_def                            false
% 3.01/1.00  --sat_epr_types                         true
% 3.01/1.00  --sat_non_cyclic_types                  false
% 3.01/1.00  --sat_finite_models                     false
% 3.01/1.00  --sat_fm_lemmas                         false
% 3.01/1.00  --sat_fm_prep                           false
% 3.01/1.00  --sat_fm_uc_incr                        true
% 3.01/1.00  --sat_out_model                         small
% 3.01/1.00  --sat_out_clauses                       false
% 3.01/1.00  
% 3.01/1.00  ------ QBF Options
% 3.01/1.00  
% 3.01/1.00  --qbf_mode                              false
% 3.01/1.00  --qbf_elim_univ                         false
% 3.01/1.00  --qbf_dom_inst                          none
% 3.01/1.00  --qbf_dom_pre_inst                      false
% 3.01/1.00  --qbf_sk_in                             false
% 3.01/1.00  --qbf_pred_elim                         true
% 3.01/1.00  --qbf_split                             512
% 3.01/1.00  
% 3.01/1.00  ------ BMC1 Options
% 3.01/1.00  
% 3.01/1.00  --bmc1_incremental                      false
% 3.01/1.00  --bmc1_axioms                           reachable_all
% 3.01/1.00  --bmc1_min_bound                        0
% 3.01/1.00  --bmc1_max_bound                        -1
% 3.01/1.00  --bmc1_max_bound_default                -1
% 3.01/1.00  --bmc1_symbol_reachability              true
% 3.01/1.00  --bmc1_property_lemmas                  false
% 3.01/1.00  --bmc1_k_induction                      false
% 3.01/1.00  --bmc1_non_equiv_states                 false
% 3.01/1.00  --bmc1_deadlock                         false
% 3.01/1.00  --bmc1_ucm                              false
% 3.01/1.00  --bmc1_add_unsat_core                   none
% 3.01/1.00  --bmc1_unsat_core_children              false
% 3.01/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.00  --bmc1_out_stat                         full
% 3.01/1.00  --bmc1_ground_init                      false
% 3.01/1.00  --bmc1_pre_inst_next_state              false
% 3.01/1.00  --bmc1_pre_inst_state                   false
% 3.01/1.00  --bmc1_pre_inst_reach_state             false
% 3.01/1.00  --bmc1_out_unsat_core                   false
% 3.01/1.00  --bmc1_aig_witness_out                  false
% 3.01/1.00  --bmc1_verbose                          false
% 3.01/1.00  --bmc1_dump_clauses_tptp                false
% 3.01/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.00  --bmc1_dump_file                        -
% 3.01/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.00  --bmc1_ucm_extend_mode                  1
% 3.01/1.00  --bmc1_ucm_init_mode                    2
% 3.01/1.00  --bmc1_ucm_cone_mode                    none
% 3.01/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.00  --bmc1_ucm_relax_model                  4
% 3.01/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.00  --bmc1_ucm_layered_model                none
% 3.01/1.00  --bmc1_ucm_max_lemma_size               10
% 3.01/1.00  
% 3.01/1.00  ------ AIG Options
% 3.01/1.00  
% 3.01/1.00  --aig_mode                              false
% 3.01/1.00  
% 3.01/1.00  ------ Instantiation Options
% 3.01/1.00  
% 3.01/1.00  --instantiation_flag                    true
% 3.01/1.00  --inst_sos_flag                         false
% 3.01/1.00  --inst_sos_phase                        true
% 3.01/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.00  --inst_lit_sel_side                     none
% 3.01/1.00  --inst_solver_per_active                1400
% 3.01/1.00  --inst_solver_calls_frac                1.
% 3.01/1.00  --inst_passive_queue_type               priority_queues
% 3.01/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.00  --inst_passive_queues_freq              [25;2]
% 3.01/1.00  --inst_dismatching                      true
% 3.01/1.00  --inst_eager_unprocessed_to_passive     true
% 3.01/1.00  --inst_prop_sim_given                   true
% 3.01/1.00  --inst_prop_sim_new                     false
% 3.01/1.00  --inst_subs_new                         false
% 3.01/1.00  --inst_eq_res_simp                      false
% 3.01/1.00  --inst_subs_given                       false
% 3.01/1.00  --inst_orphan_elimination               true
% 3.01/1.00  --inst_learning_loop_flag               true
% 3.01/1.00  --inst_learning_start                   3000
% 3.01/1.00  --inst_learning_factor                  2
% 3.01/1.00  --inst_start_prop_sim_after_learn       3
% 3.01/1.00  --inst_sel_renew                        solver
% 3.01/1.00  --inst_lit_activity_flag                true
% 3.01/1.00  --inst_restr_to_given                   false
% 3.01/1.00  --inst_activity_threshold               500
% 3.01/1.00  --inst_out_proof                        true
% 3.01/1.00  
% 3.01/1.00  ------ Resolution Options
% 3.01/1.00  
% 3.01/1.00  --resolution_flag                       false
% 3.01/1.00  --res_lit_sel                           adaptive
% 3.01/1.00  --res_lit_sel_side                      none
% 3.01/1.00  --res_ordering                          kbo
% 3.01/1.00  --res_to_prop_solver                    active
% 3.01/1.00  --res_prop_simpl_new                    false
% 3.01/1.00  --res_prop_simpl_given                  true
% 3.01/1.00  --res_passive_queue_type                priority_queues
% 3.01/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.00  --res_passive_queues_freq               [15;5]
% 3.01/1.00  --res_forward_subs                      full
% 3.01/1.00  --res_backward_subs                     full
% 3.01/1.00  --res_forward_subs_resolution           true
% 3.01/1.00  --res_backward_subs_resolution          true
% 3.01/1.00  --res_orphan_elimination                true
% 3.01/1.00  --res_time_limit                        2.
% 3.01/1.00  --res_out_proof                         true
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Options
% 3.01/1.00  
% 3.01/1.00  --superposition_flag                    true
% 3.01/1.00  --sup_passive_queue_type                priority_queues
% 3.01/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.00  --demod_completeness_check              fast
% 3.01/1.00  --demod_use_ground                      true
% 3.01/1.00  --sup_to_prop_solver                    passive
% 3.01/1.00  --sup_prop_simpl_new                    true
% 3.01/1.00  --sup_prop_simpl_given                  true
% 3.01/1.00  --sup_fun_splitting                     false
% 3.01/1.00  --sup_smt_interval                      50000
% 3.01/1.00  
% 3.01/1.00  ------ Superposition Simplification Setup
% 3.01/1.00  
% 3.01/1.00  --sup_indices_passive                   []
% 3.01/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_full_bw                           [BwDemod]
% 3.01/1.00  --sup_immed_triv                        [TrivRules]
% 3.01/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_immed_bw_main                     []
% 3.01/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.00  
% 3.01/1.00  ------ Combination Options
% 3.01/1.00  
% 3.01/1.00  --comb_res_mult                         3
% 3.01/1.00  --comb_sup_mult                         2
% 3.01/1.00  --comb_inst_mult                        10
% 3.01/1.00  
% 3.01/1.00  ------ Debug Options
% 3.01/1.00  
% 3.01/1.00  --dbg_backtrace                         false
% 3.01/1.00  --dbg_dump_prop_clauses                 false
% 3.01/1.00  --dbg_dump_prop_clauses_file            -
% 3.01/1.00  --dbg_out_stat                          false
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  ------ Proving...
% 3.01/1.00  
% 3.01/1.00  
% 3.01/1.00  % SZS status Theorem for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/1.00  
% 3.01/1.00  fof(f16,conjecture,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f17,negated_conjecture,(
% 3.01/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.01/1.00    inference(negated_conjecture,[],[f16])).
% 3.01/1.00  
% 3.01/1.00  fof(f43,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f17])).
% 3.01/1.00  
% 3.01/1.00  fof(f44,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f43])).
% 3.01/1.00  
% 3.01/1.00  fof(f53,plain,(
% 3.01/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f52,plain,(
% 3.01/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f51,plain,(
% 3.01/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f50,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f49,plain,(
% 3.01/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f48,plain,(
% 3.01/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f47,plain,(
% 3.01/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.01/1.00    introduced(choice_axiom,[])).
% 3.01/1.00  
% 3.01/1.00  fof(f54,plain,(
% 3.01/1.00    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.01/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f44,f53,f52,f51,f50,f49,f48,f47])).
% 3.01/1.00  
% 3.01/1.00  fof(f90,plain,(
% 3.01/1.00    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f89,plain,(
% 3.01/1.00    sK5 = sK6),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f11,axiom,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f33,plain,(
% 3.01/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f11])).
% 3.01/1.00  
% 3.01/1.00  fof(f34,plain,(
% 3.01/1.00    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.01/1.00    inference(flattening,[],[f33])).
% 3.01/1.00  
% 3.01/1.00  fof(f66,plain,(
% 3.01/1.00    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f34])).
% 3.01/1.00  
% 3.01/1.00  fof(f3,axiom,(
% 3.01/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f19,plain,(
% 3.01/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.01/1.00    inference(unused_predicate_definition_removal,[],[f3])).
% 3.01/1.00  
% 3.01/1.00  fof(f22,plain,(
% 3.01/1.00    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.01/1.00    inference(ennf_transformation,[],[f19])).
% 3.01/1.00  
% 3.01/1.00  fof(f57,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.01/1.00    inference(cnf_transformation,[],[f22])).
% 3.01/1.00  
% 3.01/1.00  fof(f15,axiom,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X3)) => (r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7))))))))))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f41,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | (X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3))) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f15])).
% 3.01/1.00  
% 3.01/1.00  fof(f42,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : ((r1_tmap_1(X3,X1,X4,X6) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f41])).
% 3.01/1.00  
% 3.01/1.00  fof(f46,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (((r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tmap_1(X3,X1,X4,X6))) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(nnf_transformation,[],[f42])).
% 3.01/1.00  
% 3.01/1.00  fof(f72,plain,(
% 3.01/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | X6 != X7 | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X6,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f46])).
% 3.01/1.00  
% 3.01/1.00  fof(f93,plain,(
% 3.01/1.00    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X7) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X7) | ~r1_tarski(X5,u1_struct_0(X2)) | ~r2_hidden(X7,X5) | ~v3_pre_topc(X5,X3) | ~m1_subset_1(X7,u1_struct_0(X2)) | ~m1_subset_1(X7,u1_struct_0(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(equality_resolution,[],[f72])).
% 3.01/1.00  
% 3.01/1.00  fof(f84,plain,(
% 3.01/1.00    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f83,plain,(
% 3.01/1.00    v1_funct_1(sK4)),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f4,axiom,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f23,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f4])).
% 3.01/1.00  
% 3.01/1.00  fof(f24,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.01/1.00    inference(flattening,[],[f23])).
% 3.01/1.00  
% 3.01/1.00  fof(f58,plain,(
% 3.01/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f24])).
% 3.01/1.00  
% 3.01/1.00  fof(f8,axiom,(
% 3.01/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f28,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f8])).
% 3.01/1.00  
% 3.01/1.00  fof(f62,plain,(
% 3.01/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f28])).
% 3.01/1.00  
% 3.01/1.00  fof(f7,axiom,(
% 3.01/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f27,plain,(
% 3.01/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f7])).
% 3.01/1.00  
% 3.01/1.00  fof(f61,plain,(
% 3.01/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f27])).
% 3.01/1.00  
% 3.01/1.00  fof(f6,axiom,(
% 3.01/1.00    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f26,plain,(
% 3.01/1.00    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f6])).
% 3.01/1.00  
% 3.01/1.00  fof(f60,plain,(
% 3.01/1.00    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f26])).
% 3.01/1.00  
% 3.01/1.00  fof(f76,plain,(
% 3.01/1.00    ~v2_struct_0(sK1)),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f77,plain,(
% 3.01/1.00    v2_pre_topc(sK1)),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f78,plain,(
% 3.01/1.00    l1_pre_topc(sK1)),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f81,plain,(
% 3.01/1.00    ~v2_struct_0(sK3)),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f85,plain,(
% 3.01/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f82,plain,(
% 3.01/1.00    m1_pre_topc(sK3,sK0)),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f75,plain,(
% 3.01/1.00    l1_pre_topc(sK0)),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f5,axiom,(
% 3.01/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f25,plain,(
% 3.01/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.01/1.00    inference(ennf_transformation,[],[f5])).
% 3.01/1.00  
% 3.01/1.00  fof(f59,plain,(
% 3.01/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f25])).
% 3.01/1.00  
% 3.01/1.00  fof(f80,plain,(
% 3.01/1.00    m1_pre_topc(sK2,sK0)),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f14,axiom,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f39,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f14])).
% 3.01/1.00  
% 3.01/1.00  fof(f40,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f39])).
% 3.01/1.00  
% 3.01/1.00  fof(f70,plain,(
% 3.01/1.00    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f40])).
% 3.01/1.00  
% 3.01/1.00  fof(f86,plain,(
% 3.01/1.00    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f73,plain,(
% 3.01/1.00    ~v2_struct_0(sK0)),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f74,plain,(
% 3.01/1.00    v2_pre_topc(sK0)),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f79,plain,(
% 3.01/1.00    ~v2_struct_0(sK2)),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f13,axiom,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f37,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f13])).
% 3.01/1.00  
% 3.01/1.00  fof(f38,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f37])).
% 3.01/1.00  
% 3.01/1.00  fof(f69,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f38])).
% 3.01/1.00  
% 3.01/1.00  fof(f12,axiom,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3))))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f35,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f12])).
% 3.01/1.00  
% 3.01/1.00  fof(f36,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(flattening,[],[f35])).
% 3.01/1.00  
% 3.01/1.00  fof(f45,plain,(
% 3.01/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.01/1.00    inference(nnf_transformation,[],[f36])).
% 3.01/1.00  
% 3.01/1.00  fof(f67,plain,(
% 3.01/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f45])).
% 3.01/1.00  
% 3.01/1.00  fof(f92,plain,(
% 3.01/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.01/1.00    inference(equality_resolution,[],[f67])).
% 3.01/1.00  
% 3.01/1.00  fof(f1,axiom,(
% 3.01/1.00    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f18,plain,(
% 3.01/1.00    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.01/1.00    inference(rectify,[],[f1])).
% 3.01/1.00  
% 3.01/1.00  fof(f55,plain,(
% 3.01/1.00    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.01/1.00    inference(cnf_transformation,[],[f18])).
% 3.01/1.00  
% 3.01/1.00  fof(f10,axiom,(
% 3.01/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f31,plain,(
% 3.01/1.00    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.01/1.00    inference(ennf_transformation,[],[f10])).
% 3.01/1.00  
% 3.01/1.00  fof(f32,plain,(
% 3.01/1.00    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.01/1.00    inference(flattening,[],[f31])).
% 3.01/1.00  
% 3.01/1.00  fof(f64,plain,(
% 3.01/1.00    ( ! [X0] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f32])).
% 3.01/1.00  
% 3.01/1.00  fof(f87,plain,(
% 3.01/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.01/1.00    inference(cnf_transformation,[],[f54])).
% 3.01/1.00  
% 3.01/1.00  fof(f2,axiom,(
% 3.01/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.01/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.00  
% 3.01/1.00  fof(f20,plain,(
% 3.01/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.01/1.00    inference(ennf_transformation,[],[f2])).
% 3.01/1.00  
% 3.01/1.00  fof(f21,plain,(
% 3.01/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.01/1.00    inference(flattening,[],[f20])).
% 3.01/1.00  
% 3.01/1.00  fof(f56,plain,(
% 3.01/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.01/1.00    inference(cnf_transformation,[],[f21])).
% 3.01/1.01  
% 3.01/1.01  fof(f9,axiom,(
% 3.01/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.01/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.01  
% 3.01/1.01  fof(f29,plain,(
% 3.01/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.01/1.01    inference(ennf_transformation,[],[f9])).
% 3.01/1.01  
% 3.01/1.01  fof(f30,plain,(
% 3.01/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.01/1.01    inference(flattening,[],[f29])).
% 3.01/1.01  
% 3.01/1.01  fof(f63,plain,(
% 3.01/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.01/1.01    inference(cnf_transformation,[],[f30])).
% 3.01/1.01  
% 3.01/1.01  fof(f88,plain,(
% 3.01/1.01    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.01/1.01    inference(cnf_transformation,[],[f54])).
% 3.01/1.01  
% 3.01/1.01  fof(f91,plain,(
% 3.01/1.01    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 3.01/1.01    inference(cnf_transformation,[],[f54])).
% 3.01/1.01  
% 3.01/1.01  cnf(c_19,negated_conjecture,
% 3.01/1.01      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 3.01/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2071,plain,
% 3.01/1.01      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_20,negated_conjecture,
% 3.01/1.01      ( sK5 = sK6 ),
% 3.01/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2121,plain,
% 3.01/1.01      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 3.01/1.01      inference(light_normalisation,[status(thm)],[c_2071,c_20]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_11,plain,
% 3.01/1.01      ( v3_pre_topc(k2_struct_0(X0),X0)
% 3.01/1.01      | ~ l1_pre_topc(X0)
% 3.01/1.01      | ~ v2_pre_topc(X0) ),
% 3.01/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2,plain,
% 3.01/1.01      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.01/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_16,plain,
% 3.01/1.01      ( r1_tmap_1(X0,X1,X2,X3)
% 3.01/1.01      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.01/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.01/1.01      | ~ v3_pre_topc(X6,X0)
% 3.01/1.01      | ~ m1_pre_topc(X0,X5)
% 3.01/1.01      | ~ m1_pre_topc(X4,X5)
% 3.01/1.01      | ~ m1_pre_topc(X4,X0)
% 3.01/1.01      | ~ r1_tarski(X6,u1_struct_0(X4))
% 3.01/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.01/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.01/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.01/1.01      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.01      | ~ r2_hidden(X3,X6)
% 3.01/1.01      | ~ v1_funct_1(X2)
% 3.01/1.01      | v2_struct_0(X5)
% 3.01/1.01      | v2_struct_0(X1)
% 3.01/1.01      | v2_struct_0(X4)
% 3.01/1.01      | v2_struct_0(X0)
% 3.01/1.01      | ~ l1_pre_topc(X5)
% 3.01/1.01      | ~ l1_pre_topc(X1)
% 3.01/1.01      | ~ v2_pre_topc(X5)
% 3.01/1.01      | ~ v2_pre_topc(X1) ),
% 3.01/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_25,negated_conjecture,
% 3.01/1.01      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 3.01/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_595,plain,
% 3.01/1.01      ( r1_tmap_1(X0,X1,X2,X3)
% 3.01/1.01      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 3.01/1.01      | ~ v3_pre_topc(X6,X0)
% 3.01/1.01      | ~ m1_pre_topc(X0,X5)
% 3.01/1.01      | ~ m1_pre_topc(X4,X5)
% 3.01/1.01      | ~ m1_pre_topc(X4,X0)
% 3.01/1.01      | ~ r1_tarski(X6,u1_struct_0(X4))
% 3.01/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.01/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.01/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.01/1.01      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.01      | ~ r2_hidden(X3,X6)
% 3.01/1.01      | ~ v1_funct_1(X2)
% 3.01/1.01      | v2_struct_0(X0)
% 3.01/1.01      | v2_struct_0(X1)
% 3.01/1.01      | v2_struct_0(X5)
% 3.01/1.01      | v2_struct_0(X4)
% 3.01/1.01      | ~ l1_pre_topc(X1)
% 3.01/1.01      | ~ l1_pre_topc(X5)
% 3.01/1.01      | ~ v2_pre_topc(X1)
% 3.01/1.01      | ~ v2_pre_topc(X5)
% 3.01/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.01/1.01      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.01/1.01      | sK4 != X2 ),
% 3.01/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_596,plain,
% 3.01/1.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.01/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.01/1.01      | ~ v3_pre_topc(X5,X3)
% 3.01/1.01      | ~ m1_pre_topc(X3,X2)
% 3.01/1.01      | ~ m1_pre_topc(X0,X2)
% 3.01/1.01      | ~ m1_pre_topc(X0,X3)
% 3.01/1.01      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.01/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.01/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.01/1.01      | ~ r2_hidden(X4,X5)
% 3.01/1.01      | ~ v1_funct_1(sK4)
% 3.01/1.01      | v2_struct_0(X3)
% 3.01/1.01      | v2_struct_0(X1)
% 3.01/1.01      | v2_struct_0(X2)
% 3.01/1.01      | v2_struct_0(X0)
% 3.01/1.01      | ~ l1_pre_topc(X1)
% 3.01/1.01      | ~ l1_pre_topc(X2)
% 3.01/1.01      | ~ v2_pre_topc(X1)
% 3.01/1.01      | ~ v2_pre_topc(X2)
% 3.01/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.01/1.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.01/1.01      inference(unflattening,[status(thm)],[c_595]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_26,negated_conjecture,
% 3.01/1.01      ( v1_funct_1(sK4) ),
% 3.01/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_600,plain,
% 3.01/1.01      ( ~ r2_hidden(X4,X5)
% 3.01/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.01/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.01/1.01      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.01/1.01      | ~ m1_pre_topc(X0,X3)
% 3.01/1.01      | ~ m1_pre_topc(X0,X2)
% 3.01/1.01      | ~ m1_pre_topc(X3,X2)
% 3.01/1.01      | ~ v3_pre_topc(X5,X3)
% 3.01/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.01/1.01      | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.01/1.01      | v2_struct_0(X3)
% 3.01/1.01      | v2_struct_0(X1)
% 3.01/1.01      | v2_struct_0(X2)
% 3.01/1.01      | v2_struct_0(X0)
% 3.01/1.01      | ~ l1_pre_topc(X1)
% 3.01/1.01      | ~ l1_pre_topc(X2)
% 3.01/1.01      | ~ v2_pre_topc(X1)
% 3.01/1.01      | ~ v2_pre_topc(X2)
% 3.01/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.01/1.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.01/1.01      inference(global_propositional_subsumption,
% 3.01/1.01                [status(thm)],
% 3.01/1.01                [c_596,c_26]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_601,plain,
% 3.01/1.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.01/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.01/1.01      | ~ v3_pre_topc(X5,X3)
% 3.01/1.01      | ~ m1_pre_topc(X3,X2)
% 3.01/1.01      | ~ m1_pre_topc(X0,X2)
% 3.01/1.01      | ~ m1_pre_topc(X0,X3)
% 3.01/1.01      | ~ r1_tarski(X5,u1_struct_0(X0))
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.01/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.01/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.01/1.01      | ~ r2_hidden(X4,X5)
% 3.01/1.01      | v2_struct_0(X0)
% 3.01/1.01      | v2_struct_0(X1)
% 3.01/1.01      | v2_struct_0(X2)
% 3.01/1.01      | v2_struct_0(X3)
% 3.01/1.01      | ~ l1_pre_topc(X1)
% 3.01/1.01      | ~ l1_pre_topc(X2)
% 3.01/1.01      | ~ v2_pre_topc(X1)
% 3.01/1.01      | ~ v2_pre_topc(X2)
% 3.01/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.01/1.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.01/1.01      inference(renaming,[status(thm)],[c_600]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_653,plain,
% 3.01/1.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.01/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.01/1.01      | ~ v3_pre_topc(X5,X3)
% 3.01/1.01      | ~ m1_pre_topc(X3,X2)
% 3.01/1.01      | ~ m1_pre_topc(X0,X2)
% 3.01/1.01      | ~ m1_pre_topc(X0,X3)
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.01/1.01      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
% 3.01/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.01/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.01/1.01      | ~ r2_hidden(X4,X5)
% 3.01/1.01      | v2_struct_0(X0)
% 3.01/1.01      | v2_struct_0(X2)
% 3.01/1.01      | v2_struct_0(X1)
% 3.01/1.01      | v2_struct_0(X3)
% 3.01/1.01      | ~ l1_pre_topc(X2)
% 3.01/1.01      | ~ l1_pre_topc(X1)
% 3.01/1.01      | ~ v2_pre_topc(X2)
% 3.01/1.01      | ~ v2_pre_topc(X1)
% 3.01/1.01      | X5 != X6
% 3.01/1.01      | u1_struct_0(X0) != X7
% 3.01/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.01/1.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.01/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_601]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_654,plain,
% 3.01/1.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.01/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.01/1.01      | ~ v3_pre_topc(X5,X3)
% 3.01/1.01      | ~ m1_pre_topc(X3,X2)
% 3.01/1.01      | ~ m1_pre_topc(X0,X2)
% 3.01/1.01      | ~ m1_pre_topc(X0,X3)
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.01/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.01/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.01/1.01      | ~ r2_hidden(X4,X5)
% 3.01/1.01      | v2_struct_0(X0)
% 3.01/1.01      | v2_struct_0(X1)
% 3.01/1.01      | v2_struct_0(X2)
% 3.01/1.01      | v2_struct_0(X3)
% 3.01/1.01      | ~ l1_pre_topc(X1)
% 3.01/1.01      | ~ l1_pre_topc(X2)
% 3.01/1.01      | ~ v2_pre_topc(X1)
% 3.01/1.01      | ~ v2_pre_topc(X2)
% 3.01/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.01/1.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.01/1.01      inference(unflattening,[status(thm)],[c_653]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_932,plain,
% 3.01/1.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.01/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.01/1.01      | ~ m1_pre_topc(X0,X3)
% 3.01/1.01      | ~ m1_pre_topc(X0,X2)
% 3.01/1.01      | ~ m1_pre_topc(X3,X2)
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.01/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
% 3.01/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.01/1.01      | ~ r2_hidden(X4,X5)
% 3.01/1.01      | v2_struct_0(X3)
% 3.01/1.01      | v2_struct_0(X0)
% 3.01/1.01      | v2_struct_0(X2)
% 3.01/1.01      | v2_struct_0(X1)
% 3.01/1.01      | ~ l1_pre_topc(X6)
% 3.01/1.01      | ~ l1_pre_topc(X2)
% 3.01/1.01      | ~ l1_pre_topc(X1)
% 3.01/1.01      | ~ v2_pre_topc(X6)
% 3.01/1.01      | ~ v2_pre_topc(X2)
% 3.01/1.01      | ~ v2_pre_topc(X1)
% 3.01/1.01      | X3 != X6
% 3.01/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.01/1.01      | u1_struct_0(X3) != u1_struct_0(sK3)
% 3.01/1.01      | k2_struct_0(X6) != X5 ),
% 3.01/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_654]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_933,plain,
% 3.01/1.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.01/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.01/1.01      | ~ m1_pre_topc(X0,X2)
% 3.01/1.01      | ~ m1_pre_topc(X0,X3)
% 3.01/1.01      | ~ m1_pre_topc(X3,X2)
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.01/1.01      | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.01      | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X3)))
% 3.01/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.01/1.01      | ~ r2_hidden(X4,k2_struct_0(X3))
% 3.01/1.01      | v2_struct_0(X0)
% 3.01/1.01      | v2_struct_0(X1)
% 3.01/1.01      | v2_struct_0(X2)
% 3.01/1.01      | v2_struct_0(X3)
% 3.01/1.01      | ~ l1_pre_topc(X1)
% 3.01/1.01      | ~ l1_pre_topc(X2)
% 3.01/1.01      | ~ l1_pre_topc(X3)
% 3.01/1.01      | ~ v2_pre_topc(X1)
% 3.01/1.01      | ~ v2_pre_topc(X2)
% 3.01/1.01      | ~ v2_pre_topc(X3)
% 3.01/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.01/1.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.01/1.01      inference(unflattening,[status(thm)],[c_932]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3,plain,
% 3.01/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.01      | ~ l1_pre_topc(X1)
% 3.01/1.01      | ~ v2_pre_topc(X1)
% 3.01/1.01      | v2_pre_topc(X0) ),
% 3.01/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_7,plain,
% 3.01/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.01/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_6,plain,
% 3.01/1.01      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.01/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_5,plain,
% 3.01/1.01      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.01      | ~ l1_struct_0(X0) ),
% 3.01/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_402,plain,
% 3.01/1.01      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.01      | ~ l1_pre_topc(X0) ),
% 3.01/1.01      inference(resolution,[status(thm)],[c_6,c_5]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_983,plain,
% 3.01/1.01      ( ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
% 3.01/1.01      | r1_tmap_1(X3,X1,sK4,X4)
% 3.01/1.01      | ~ m1_pre_topc(X3,X2)
% 3.01/1.01      | ~ m1_pre_topc(X0,X2)
% 3.01/1.01      | ~ m1_pre_topc(X0,X3)
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X0))
% 3.01/1.01      | ~ m1_subset_1(X4,u1_struct_0(X3))
% 3.01/1.01      | ~ m1_subset_1(k2_struct_0(X3),k1_zfmisc_1(u1_struct_0(X0)))
% 3.01/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.01/1.01      | ~ r2_hidden(X4,k2_struct_0(X3))
% 3.01/1.01      | v2_struct_0(X0)
% 3.01/1.01      | v2_struct_0(X1)
% 3.01/1.01      | v2_struct_0(X2)
% 3.01/1.01      | v2_struct_0(X3)
% 3.01/1.01      | ~ l1_pre_topc(X1)
% 3.01/1.01      | ~ l1_pre_topc(X2)
% 3.01/1.01      | ~ v2_pre_topc(X1)
% 3.01/1.01      | ~ v2_pre_topc(X2)
% 3.01/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 3.01/1.01      | u1_struct_0(X3) != u1_struct_0(sK3) ),
% 3.01/1.01      inference(forward_subsumption_resolution,
% 3.01/1.01                [status(thm)],
% 3.01/1.01                [c_933,c_3,c_7,c_402]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2053,plain,
% 3.01/1.01      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.01/1.01      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.01/1.01      | r1_tmap_1(X2,X0,k3_tmap_1(X3,X0,X1,X2,sK4),X4) != iProver_top
% 3.01/1.01      | r1_tmap_1(X1,X0,sK4,X4) = iProver_top
% 3.01/1.01      | m1_pre_topc(X1,X3) != iProver_top
% 3.01/1.01      | m1_pre_topc(X2,X3) != iProver_top
% 3.01/1.01      | m1_pre_topc(X2,X1) != iProver_top
% 3.01/1.01      | m1_subset_1(X4,u1_struct_0(X2)) != iProver_top
% 3.01/1.01      | m1_subset_1(X4,u1_struct_0(X1)) != iProver_top
% 3.01/1.01      | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 3.01/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 3.01/1.01      | r2_hidden(X4,k2_struct_0(X1)) != iProver_top
% 3.01/1.01      | v2_struct_0(X0) = iProver_top
% 3.01/1.01      | v2_struct_0(X2) = iProver_top
% 3.01/1.01      | v2_struct_0(X3) = iProver_top
% 3.01/1.01      | v2_struct_0(X1) = iProver_top
% 3.01/1.01      | l1_pre_topc(X0) != iProver_top
% 3.01/1.01      | l1_pre_topc(X3) != iProver_top
% 3.01/1.01      | v2_pre_topc(X0) != iProver_top
% 3.01/1.01      | v2_pre_topc(X3) != iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_983]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2518,plain,
% 3.01/1.01      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.01/1.01      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 3.01/1.01      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 3.01/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 3.01/1.01      | m1_pre_topc(X0,X2) != iProver_top
% 3.01/1.01      | m1_pre_topc(X1,X2) != iProver_top
% 3.01/1.01      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.01/1.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.01/1.01      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.01/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.01/1.01      | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
% 3.01/1.01      | v2_struct_0(X1) = iProver_top
% 3.01/1.01      | v2_struct_0(X0) = iProver_top
% 3.01/1.01      | v2_struct_0(X2) = iProver_top
% 3.01/1.01      | v2_struct_0(sK1) = iProver_top
% 3.01/1.01      | l1_pre_topc(X2) != iProver_top
% 3.01/1.01      | l1_pre_topc(sK1) != iProver_top
% 3.01/1.01      | v2_pre_topc(X2) != iProver_top
% 3.01/1.01      | v2_pre_topc(sK1) != iProver_top ),
% 3.01/1.01      inference(equality_resolution,[status(thm)],[c_2053]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_33,negated_conjecture,
% 3.01/1.01      ( ~ v2_struct_0(sK1) ),
% 3.01/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_40,plain,
% 3.01/1.01      ( v2_struct_0(sK1) != iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_32,negated_conjecture,
% 3.01/1.01      ( v2_pre_topc(sK1) ),
% 3.01/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_41,plain,
% 3.01/1.01      ( v2_pre_topc(sK1) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_31,negated_conjecture,
% 3.01/1.01      ( l1_pre_topc(sK1) ),
% 3.01/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_42,plain,
% 3.01/1.01      ( l1_pre_topc(sK1) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3047,plain,
% 3.01/1.01      ( v2_pre_topc(X2) != iProver_top
% 3.01/1.01      | v2_struct_0(X2) = iProver_top
% 3.01/1.01      | v2_struct_0(X0) = iProver_top
% 3.01/1.01      | v2_struct_0(X1) = iProver_top
% 3.01/1.01      | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
% 3.01/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.01/1.01      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.01/1.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.01/1.01      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.01/1.01      | m1_pre_topc(X1,X2) != iProver_top
% 3.01/1.01      | m1_pre_topc(X0,X2) != iProver_top
% 3.01/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 3.01/1.01      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 3.01/1.01      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 3.01/1.01      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.01/1.01      | l1_pre_topc(X2) != iProver_top ),
% 3.01/1.01      inference(global_propositional_subsumption,
% 3.01/1.01                [status(thm)],
% 3.01/1.01                [c_2518,c_40,c_41,c_42]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3048,plain,
% 3.01/1.01      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 3.01/1.01      | r1_tmap_1(X1,sK1,k3_tmap_1(X2,sK1,X0,X1,sK4),X3) != iProver_top
% 3.01/1.01      | r1_tmap_1(X0,sK1,sK4,X3) = iProver_top
% 3.01/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 3.01/1.01      | m1_pre_topc(X0,X2) != iProver_top
% 3.01/1.01      | m1_pre_topc(X1,X2) != iProver_top
% 3.01/1.01      | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
% 3.01/1.01      | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
% 3.01/1.01      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.01/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) != iProver_top
% 3.01/1.01      | r2_hidden(X3,k2_struct_0(X0)) != iProver_top
% 3.01/1.01      | v2_struct_0(X1) = iProver_top
% 3.01/1.01      | v2_struct_0(X0) = iProver_top
% 3.01/1.01      | v2_struct_0(X2) = iProver_top
% 3.01/1.01      | l1_pre_topc(X2) != iProver_top
% 3.01/1.01      | v2_pre_topc(X2) != iProver_top ),
% 3.01/1.01      inference(renaming,[status(thm)],[c_3047]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3067,plain,
% 3.01/1.01      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.01/1.01      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.01/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 3.01/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.01/1.01      | m1_pre_topc(sK3,X1) != iProver_top
% 3.01/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.01/1.01      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.01/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.01/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.01/1.01      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 3.01/1.01      | v2_struct_0(X1) = iProver_top
% 3.01/1.01      | v2_struct_0(X0) = iProver_top
% 3.01/1.01      | v2_struct_0(sK3) = iProver_top
% 3.01/1.01      | l1_pre_topc(X1) != iProver_top
% 3.01/1.01      | v2_pre_topc(X1) != iProver_top ),
% 3.01/1.01      inference(equality_resolution,[status(thm)],[c_3048]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_28,negated_conjecture,
% 3.01/1.01      ( ~ v2_struct_0(sK3) ),
% 3.01/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_45,plain,
% 3.01/1.01      ( v2_struct_0(sK3) != iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_24,negated_conjecture,
% 3.01/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 3.01/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_49,plain,
% 3.01/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_7215,plain,
% 3.01/1.01      ( v2_struct_0(X0) = iProver_top
% 3.01/1.01      | v2_struct_0(X1) = iProver_top
% 3.01/1.01      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 3.01/1.01      | r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.01/1.01      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.01/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 3.01/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.01/1.01      | m1_pre_topc(sK3,X1) != iProver_top
% 3.01/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.01/1.01      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.01/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.01/1.01      | l1_pre_topc(X1) != iProver_top
% 3.01/1.01      | v2_pre_topc(X1) != iProver_top ),
% 3.01/1.01      inference(global_propositional_subsumption,
% 3.01/1.01                [status(thm)],
% 3.01/1.01                [c_3067,c_45,c_49]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_7216,plain,
% 3.01/1.01      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.01/1.01      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.01/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 3.01/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.01/1.01      | m1_pre_topc(sK3,X1) != iProver_top
% 3.01/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.01/1.01      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.01/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.01/1.01      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 3.01/1.01      | v2_struct_0(X1) = iProver_top
% 3.01/1.01      | v2_struct_0(X0) = iProver_top
% 3.01/1.01      | l1_pre_topc(X1) != iProver_top
% 3.01/1.01      | v2_pre_topc(X1) != iProver_top ),
% 3.01/1.01      inference(renaming,[status(thm)],[c_7215]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_27,negated_conjecture,
% 3.01/1.01      ( m1_pre_topc(sK3,sK0) ),
% 3.01/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2067,plain,
% 3.01/1.01      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2079,plain,
% 3.01/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.01/1.01      | l1_pre_topc(X1) != iProver_top
% 3.01/1.01      | l1_pre_topc(X0) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3239,plain,
% 3.01/1.01      ( l1_pre_topc(sK0) != iProver_top
% 3.01/1.01      | l1_pre_topc(sK3) = iProver_top ),
% 3.01/1.01      inference(superposition,[status(thm)],[c_2067,c_2079]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_34,negated_conjecture,
% 3.01/1.01      ( l1_pre_topc(sK0) ),
% 3.01/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_39,plain,
% 3.01/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3560,plain,
% 3.01/1.01      ( l1_pre_topc(sK3) = iProver_top ),
% 3.01/1.01      inference(global_propositional_subsumption,
% 3.01/1.01                [status(thm)],
% 3.01/1.01                [c_3239,c_39]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_4,plain,
% 3.01/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.01/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_413,plain,
% 3.01/1.01      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.01/1.01      inference(resolution,[status(thm)],[c_6,c_4]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2055,plain,
% 3.01/1.01      ( u1_struct_0(X0) = k2_struct_0(X0)
% 3.01/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3565,plain,
% 3.01/1.01      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.01/1.01      inference(superposition,[status(thm)],[c_3560,c_2055]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_7221,plain,
% 3.01/1.01      ( r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2) != iProver_top
% 3.01/1.01      | r1_tmap_1(sK3,sK1,sK4,X2) = iProver_top
% 3.01/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 3.01/1.01      | m1_pre_topc(X0,sK3) != iProver_top
% 3.01/1.01      | m1_pre_topc(sK3,X1) != iProver_top
% 3.01/1.01      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 3.01/1.01      | m1_subset_1(X2,k2_struct_0(sK3)) != iProver_top
% 3.01/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.01/1.01      | r2_hidden(X2,k2_struct_0(sK3)) != iProver_top
% 3.01/1.01      | v2_struct_0(X1) = iProver_top
% 3.01/1.01      | v2_struct_0(X0) = iProver_top
% 3.01/1.01      | l1_pre_topc(X1) != iProver_top
% 3.01/1.01      | v2_pre_topc(X1) != iProver_top ),
% 3.01/1.01      inference(light_normalisation,[status(thm)],[c_7216,c_3565]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_7238,plain,
% 3.01/1.01      ( r1_tmap_1(sK3,sK1,sK4,sK5) = iProver_top
% 3.01/1.01      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.01/1.01      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.01/1.01      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.01/1.01      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.01/1.01      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 3.01/1.01      | m1_subset_1(sK5,k2_struct_0(sK3)) != iProver_top
% 3.01/1.01      | r2_hidden(sK5,k2_struct_0(sK3)) != iProver_top
% 3.01/1.01      | v2_struct_0(sK0) = iProver_top
% 3.01/1.01      | v2_struct_0(sK2) = iProver_top
% 3.01/1.01      | l1_pre_topc(sK0) != iProver_top
% 3.01/1.01      | v2_pre_topc(sK0) != iProver_top ),
% 3.01/1.01      inference(superposition,[status(thm)],[c_2121,c_7221]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_29,negated_conjecture,
% 3.01/1.01      ( m1_pre_topc(sK2,sK0) ),
% 3.01/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2065,plain,
% 3.01/1.01      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_15,plain,
% 3.01/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.01      | v2_struct_0(X1)
% 3.01/1.01      | v2_struct_0(X0)
% 3.01/1.01      | ~ l1_pre_topc(X1)
% 3.01/1.01      | ~ v2_pre_topc(X1)
% 3.01/1.01      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 3.01/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2073,plain,
% 3.01/1.01      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0)
% 3.01/1.01      | m1_pre_topc(X0,X1) != iProver_top
% 3.01/1.01      | v2_struct_0(X1) = iProver_top
% 3.01/1.01      | v2_struct_0(X0) = iProver_top
% 3.01/1.01      | l1_pre_topc(X1) != iProver_top
% 3.01/1.01      | v2_pre_topc(X1) != iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3910,plain,
% 3.01/1.01      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
% 3.01/1.01      | v2_struct_0(sK0) = iProver_top
% 3.01/1.01      | v2_struct_0(sK2) = iProver_top
% 3.01/1.01      | l1_pre_topc(sK0) != iProver_top
% 3.01/1.01      | v2_pre_topc(sK0) != iProver_top ),
% 3.01/1.01      inference(superposition,[status(thm)],[c_2065,c_2073]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_23,negated_conjecture,
% 3.01/1.01      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.01/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3916,plain,
% 3.01/1.01      ( k1_tsep_1(sK0,sK2,sK2) = sK3
% 3.01/1.01      | v2_struct_0(sK0) = iProver_top
% 3.01/1.01      | v2_struct_0(sK2) = iProver_top
% 3.01/1.01      | l1_pre_topc(sK0) != iProver_top
% 3.01/1.01      | v2_pre_topc(sK0) != iProver_top ),
% 3.01/1.01      inference(light_normalisation,[status(thm)],[c_3910,c_23]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_36,negated_conjecture,
% 3.01/1.01      ( ~ v2_struct_0(sK0) ),
% 3.01/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_37,plain,
% 3.01/1.01      ( v2_struct_0(sK0) != iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_35,negated_conjecture,
% 3.01/1.01      ( v2_pre_topc(sK0) ),
% 3.01/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_38,plain,
% 3.01/1.01      ( v2_pre_topc(sK0) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_30,negated_conjecture,
% 3.01/1.01      ( ~ v2_struct_0(sK2) ),
% 3.01/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_43,plain,
% 3.01/1.01      ( v2_struct_0(sK2) != iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3993,plain,
% 3.01/1.01      ( k1_tsep_1(sK0,sK2,sK2) = sK3 ),
% 3.01/1.01      inference(global_propositional_subsumption,
% 3.01/1.01                [status(thm)],
% 3.01/1.01                [c_3916,c_37,c_38,c_39,c_43]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_14,plain,
% 3.01/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.01      | ~ m1_pre_topc(X2,X1)
% 3.01/1.01      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
% 3.01/1.01      | v2_struct_0(X1)
% 3.01/1.01      | v2_struct_0(X0)
% 3.01/1.01      | v2_struct_0(X2)
% 3.01/1.01      | ~ l1_pre_topc(X1)
% 3.01/1.01      | ~ v2_pre_topc(X1) ),
% 3.01/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2074,plain,
% 3.01/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.01/1.01      | m1_pre_topc(X2,X1) != iProver_top
% 3.01/1.01      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2)) = iProver_top
% 3.01/1.01      | v2_struct_0(X1) = iProver_top
% 3.01/1.01      | v2_struct_0(X0) = iProver_top
% 3.01/1.01      | v2_struct_0(X2) = iProver_top
% 3.01/1.01      | l1_pre_topc(X1) != iProver_top
% 3.01/1.01      | v2_pre_topc(X1) != iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_4444,plain,
% 3.01/1.01      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.01/1.01      | m1_pre_topc(sK2,sK3) = iProver_top
% 3.01/1.01      | v2_struct_0(sK0) = iProver_top
% 3.01/1.01      | v2_struct_0(sK2) = iProver_top
% 3.01/1.01      | l1_pre_topc(sK0) != iProver_top
% 3.01/1.01      | v2_pre_topc(sK0) != iProver_top ),
% 3.01/1.01      inference(superposition,[status(thm)],[c_3993,c_2074]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_44,plain,
% 3.01/1.01      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_5109,plain,
% 3.01/1.01      ( m1_pre_topc(sK2,sK3) = iProver_top ),
% 3.01/1.01      inference(global_propositional_subsumption,
% 3.01/1.01                [status(thm)],
% 3.01/1.01                [c_4444,c_37,c_38,c_39,c_43,c_44]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_5114,plain,
% 3.01/1.01      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK3,sK2,sK2)
% 3.01/1.01      | v2_struct_0(sK2) = iProver_top
% 3.01/1.01      | v2_struct_0(sK3) = iProver_top
% 3.01/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.01/1.01      | v2_pre_topc(sK3) != iProver_top ),
% 3.01/1.01      inference(superposition,[status(thm)],[c_5109,c_2073]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3240,plain,
% 3.01/1.01      ( l1_pre_topc(sK0) != iProver_top
% 3.01/1.01      | l1_pre_topc(sK2) = iProver_top ),
% 3.01/1.01      inference(superposition,[status(thm)],[c_2065,c_2079]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3567,plain,
% 3.01/1.01      ( l1_pre_topc(sK2) = iProver_top ),
% 3.01/1.01      inference(global_propositional_subsumption,
% 3.01/1.01                [status(thm)],
% 3.01/1.01                [c_3240,c_39]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3572,plain,
% 3.01/1.01      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.01/1.01      inference(superposition,[status(thm)],[c_3567,c_2055]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_4249,plain,
% 3.01/1.01      ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 3.01/1.01      inference(demodulation,[status(thm)],[c_3572,c_23]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_5122,plain,
% 3.01/1.01      ( k1_tsep_1(sK3,sK2,sK2) = sK3
% 3.01/1.01      | v2_struct_0(sK2) = iProver_top
% 3.01/1.01      | v2_struct_0(sK3) = iProver_top
% 3.01/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.01/1.01      | v2_pre_topc(sK3) != iProver_top ),
% 3.01/1.01      inference(light_normalisation,[status(thm)],[c_5114,c_3572,c_4249]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2080,plain,
% 3.01/1.01      ( m1_pre_topc(X0,X1) != iProver_top
% 3.01/1.01      | l1_pre_topc(X1) != iProver_top
% 3.01/1.01      | v2_pre_topc(X1) != iProver_top
% 3.01/1.01      | v2_pre_topc(X0) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3886,plain,
% 3.01/1.01      ( l1_pre_topc(sK0) != iProver_top
% 3.01/1.01      | v2_pre_topc(sK0) != iProver_top
% 3.01/1.01      | v2_pre_topc(sK3) = iProver_top ),
% 3.01/1.01      inference(superposition,[status(thm)],[c_2067,c_2080]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_5130,plain,
% 3.01/1.01      ( k1_tsep_1(sK3,sK2,sK2) = sK3 ),
% 3.01/1.01      inference(global_propositional_subsumption,
% 3.01/1.01                [status(thm)],
% 3.01/1.01                [c_5122,c_38,c_39,c_43,c_45,c_3239,c_3886]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_13,plain,
% 3.01/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.01/1.01      | ~ m1_pre_topc(X2,X1)
% 3.01/1.01      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 3.01/1.01      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 3.01/1.01      | v2_struct_0(X1)
% 3.01/1.01      | v2_struct_0(X0)
% 3.01/1.01      | v2_struct_0(X2)
% 3.01/1.01      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 3.01/1.01      | ~ l1_pre_topc(X1)
% 3.01/1.01      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 3.01/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2075,plain,
% 3.01/1.01      ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
% 3.01/1.01      | m1_pre_topc(X1,X0) != iProver_top
% 3.01/1.01      | m1_pre_topc(X2,X0) != iProver_top
% 3.01/1.01      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) != iProver_top
% 3.01/1.01      | v1_pre_topc(k1_tsep_1(X0,X1,X2)) != iProver_top
% 3.01/1.01      | v2_struct_0(X0) = iProver_top
% 3.01/1.01      | v2_struct_0(X1) = iProver_top
% 3.01/1.01      | v2_struct_0(X2) = iProver_top
% 3.01/1.01      | v2_struct_0(k1_tsep_1(X0,X1,X2)) = iProver_top
% 3.01/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_5422,plain,
% 3.01/1.01      ( u1_struct_0(k1_tsep_1(sK3,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
% 3.01/1.01      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.01/1.01      | m1_pre_topc(sK3,sK3) != iProver_top
% 3.01/1.01      | v1_pre_topc(k1_tsep_1(sK3,sK2,sK2)) != iProver_top
% 3.01/1.01      | v2_struct_0(k1_tsep_1(sK3,sK2,sK2)) = iProver_top
% 3.01/1.01      | v2_struct_0(sK2) = iProver_top
% 3.01/1.01      | v2_struct_0(sK3) = iProver_top
% 3.01/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.01/1.01      inference(superposition,[status(thm)],[c_5130,c_2075]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_5431,plain,
% 3.01/1.01      ( k2_xboole_0(k2_struct_0(sK2),k2_struct_0(sK2)) = k2_struct_0(sK3)
% 3.01/1.01      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.01/1.01      | m1_pre_topc(sK3,sK3) != iProver_top
% 3.01/1.01      | v1_pre_topc(sK3) != iProver_top
% 3.01/1.01      | v2_struct_0(sK2) = iProver_top
% 3.01/1.01      | v2_struct_0(sK3) = iProver_top
% 3.01/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.01/1.01      inference(light_normalisation,
% 3.01/1.01                [status(thm)],
% 3.01/1.01                [c_5422,c_3565,c_3572,c_5130]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_0,plain,
% 3.01/1.01      ( k2_xboole_0(X0,X0) = X0 ),
% 3.01/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_5432,plain,
% 3.01/1.01      ( k2_struct_0(sK2) = k2_struct_0(sK3)
% 3.01/1.01      | m1_pre_topc(sK2,sK3) != iProver_top
% 3.01/1.01      | m1_pre_topc(sK3,sK3) != iProver_top
% 3.01/1.01      | v1_pre_topc(sK3) != iProver_top
% 3.01/1.01      | v2_struct_0(sK2) = iProver_top
% 3.01/1.01      | v2_struct_0(sK3) = iProver_top
% 3.01/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 3.01/1.01      inference(demodulation,[status(thm)],[c_5431,c_0]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_46,plain,
% 3.01/1.01      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_10,plain,
% 3.01/1.01      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.01/1.01      | ~ l1_pre_topc(X0)
% 3.01/1.01      | ~ v2_pre_topc(X0) ),
% 3.01/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2077,plain,
% 3.01/1.01      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 3.01/1.01      | l1_pre_topc(X0) != iProver_top
% 3.01/1.01      | v2_pre_topc(X0) != iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3365,plain,
% 3.01/1.01      ( v1_pre_topc(sK3) = iProver_top
% 3.01/1.01      | l1_pre_topc(sK2) != iProver_top
% 3.01/1.01      | v2_pre_topc(sK2) != iProver_top ),
% 3.01/1.01      inference(superposition,[status(thm)],[c_23,c_2077]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3368,plain,
% 3.01/1.01      ( v1_pre_topc(sK3) = iProver_top
% 3.01/1.01      | v2_pre_topc(sK2) != iProver_top ),
% 3.01/1.01      inference(global_propositional_subsumption,
% 3.01/1.01                [status(thm)],
% 3.01/1.01                [c_3365,c_39,c_3240]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3887,plain,
% 3.01/1.01      ( l1_pre_topc(sK0) != iProver_top
% 3.01/1.01      | v2_pre_topc(sK0) != iProver_top
% 3.01/1.01      | v2_pre_topc(sK2) = iProver_top ),
% 3.01/1.01      inference(superposition,[status(thm)],[c_2065,c_2080]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_5421,plain,
% 3.01/1.01      ( u1_struct_0(k1_tsep_1(sK0,sK2,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
% 3.01/1.01      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.01/1.01      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.01/1.01      | v1_pre_topc(k1_tsep_1(sK0,sK2,sK2)) != iProver_top
% 3.01/1.01      | v2_struct_0(k1_tsep_1(sK0,sK2,sK2)) = iProver_top
% 3.01/1.01      | v2_struct_0(sK0) = iProver_top
% 3.01/1.01      | v2_struct_0(sK2) = iProver_top
% 3.01/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.01/1.01      inference(superposition,[status(thm)],[c_3993,c_2075]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_5448,plain,
% 3.01/1.01      ( k2_xboole_0(k2_struct_0(sK2),k2_struct_0(sK2)) = k2_struct_0(sK3)
% 3.01/1.01      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.01/1.01      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.01/1.01      | v1_pre_topc(sK3) != iProver_top
% 3.01/1.01      | v2_struct_0(sK0) = iProver_top
% 3.01/1.01      | v2_struct_0(sK2) = iProver_top
% 3.01/1.01      | v2_struct_0(sK3) = iProver_top
% 3.01/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.01/1.01      inference(light_normalisation,
% 3.01/1.01                [status(thm)],
% 3.01/1.01                [c_5421,c_3565,c_3572,c_3993]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_5449,plain,
% 3.01/1.01      ( k2_struct_0(sK2) = k2_struct_0(sK3)
% 3.01/1.01      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.01/1.01      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.01/1.01      | v1_pre_topc(sK3) != iProver_top
% 3.01/1.01      | v2_struct_0(sK0) = iProver_top
% 3.01/1.01      | v2_struct_0(sK2) = iProver_top
% 3.01/1.01      | v2_struct_0(sK3) = iProver_top
% 3.01/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 3.01/1.01      inference(demodulation,[status(thm)],[c_5448,c_0]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_5518,plain,
% 3.01/1.01      ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
% 3.01/1.01      inference(global_propositional_subsumption,
% 3.01/1.01                [status(thm)],
% 3.01/1.01                [c_5432,c_37,c_38,c_39,c_43,c_44,c_45,c_46,c_3368,c_3887,
% 3.01/1.01                 c_5449]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2056,plain,
% 3.01/1.01      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.01/1.01      | l1_pre_topc(X0) != iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_5529,plain,
% 3.01/1.01      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.01/1.01      | l1_pre_topc(sK2) != iProver_top ),
% 3.01/1.01      inference(superposition,[status(thm)],[c_5518,c_2056]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_22,negated_conjecture,
% 3.01/1.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 3.01/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2069,plain,
% 3.01/1.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_4150,plain,
% 3.01/1.01      ( m1_subset_1(sK5,k2_struct_0(sK3)) = iProver_top ),
% 3.01/1.01      inference(demodulation,[status(thm)],[c_3565,c_2069]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_1,plain,
% 3.01/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.01/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2081,plain,
% 3.01/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 3.01/1.01      | r2_hidden(X0,X1) = iProver_top
% 3.01/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3255,plain,
% 3.01/1.01      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 3.01/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.01/1.01      inference(superposition,[status(thm)],[c_2069,c_2081]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_50,plain,
% 3.01/1.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2408,plain,
% 3.01/1.01      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 3.01/1.01      | r2_hidden(sK5,u1_struct_0(sK3))
% 3.01/1.01      | v1_xboole_0(u1_struct_0(sK3)) ),
% 3.01/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2409,plain,
% 3.01/1.01      ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 3.01/1.01      | r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 3.01/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_2408]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_8,plain,
% 3.01/1.01      ( v2_struct_0(X0)
% 3.01/1.01      | ~ l1_struct_0(X0)
% 3.01/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.01/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_388,plain,
% 3.01/1.01      ( v2_struct_0(X0)
% 3.01/1.01      | ~ l1_pre_topc(X0)
% 3.01/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.01/1.01      inference(resolution,[status(thm)],[c_6,c_8]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2531,plain,
% 3.01/1.01      ( v2_struct_0(sK3)
% 3.01/1.01      | ~ l1_pre_topc(sK3)
% 3.01/1.01      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 3.01/1.01      inference(instantiation,[status(thm)],[c_388]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2532,plain,
% 3.01/1.01      ( v2_struct_0(sK3) = iProver_top
% 3.01/1.01      | l1_pre_topc(sK3) != iProver_top
% 3.01/1.01      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_2531]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_3613,plain,
% 3.01/1.01      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top ),
% 3.01/1.01      inference(global_propositional_subsumption,
% 3.01/1.01                [status(thm)],
% 3.01/1.01                [c_3255,c_39,c_45,c_50,c_2409,c_2532,c_3239]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_4148,plain,
% 3.01/1.01      ( r2_hidden(sK5,k2_struct_0(sK3)) = iProver_top ),
% 3.01/1.01      inference(demodulation,[status(thm)],[c_3565,c_3613]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_21,negated_conjecture,
% 3.01/1.01      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.01/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2070,plain,
% 3.01/1.01      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_2108,plain,
% 3.01/1.01      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 3.01/1.01      inference(light_normalisation,[status(thm)],[c_2070,c_20]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_18,negated_conjecture,
% 3.01/1.01      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 3.01/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(c_53,plain,
% 3.01/1.01      ( r1_tmap_1(sK3,sK1,sK4,sK5) != iProver_top ),
% 3.01/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.01/1.01  
% 3.01/1.01  cnf(contradiction,plain,
% 3.01/1.01      ( $false ),
% 3.01/1.01      inference(minisat,
% 3.01/1.01                [status(thm)],
% 3.01/1.01                [c_7238,c_5529,c_4444,c_4150,c_4148,c_3240,c_2108,c_53,
% 3.01/1.01                 c_46,c_44,c_43,c_39,c_38,c_37]) ).
% 3.01/1.01  
% 3.01/1.01  
% 3.01/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/1.01  
% 3.01/1.01  ------                               Statistics
% 3.01/1.01  
% 3.01/1.01  ------ General
% 3.01/1.01  
% 3.01/1.01  abstr_ref_over_cycles:                  0
% 3.01/1.01  abstr_ref_under_cycles:                 0
% 3.01/1.01  gc_basic_clause_elim:                   0
% 3.01/1.01  forced_gc_time:                         0
% 3.01/1.01  parsing_time:                           0.011
% 3.01/1.01  unif_index_cands_time:                  0.
% 3.01/1.01  unif_index_add_time:                    0.
% 3.01/1.01  orderings_time:                         0.
% 3.01/1.01  out_proof_time:                         0.015
% 3.01/1.01  total_time:                             0.263
% 3.01/1.01  num_of_symbols:                         61
% 3.01/1.01  num_of_terms:                           6603
% 3.01/1.01  
% 3.01/1.01  ------ Preprocessing
% 3.01/1.01  
% 3.01/1.01  num_of_splits:                          0
% 3.01/1.01  num_of_split_atoms:                     0
% 3.01/1.01  num_of_reused_defs:                     0
% 3.01/1.01  num_eq_ax_congr_red:                    19
% 3.01/1.01  num_of_sem_filtered_clauses:            1
% 3.01/1.01  num_of_subtypes:                        0
% 3.01/1.01  monotx_restored_types:                  0
% 3.01/1.01  sat_num_of_epr_types:                   0
% 3.01/1.01  sat_num_of_non_cyclic_types:            0
% 3.01/1.01  sat_guarded_non_collapsed_types:        0
% 3.01/1.01  num_pure_diseq_elim:                    0
% 3.01/1.01  simp_replaced_by:                       0
% 3.01/1.01  res_preprocessed:                       170
% 3.01/1.01  prep_upred:                             0
% 3.01/1.01  prep_unflattend:                        27
% 3.01/1.01  smt_new_axioms:                         0
% 3.01/1.01  pred_elim_cands:                        9
% 3.01/1.01  pred_elim:                              5
% 3.01/1.01  pred_elim_cl:                           5
% 3.01/1.01  pred_elim_cycles:                       13
% 3.01/1.01  merged_defs:                            0
% 3.01/1.01  merged_defs_ncl:                        0
% 3.01/1.01  bin_hyper_res:                          0
% 3.01/1.01  prep_cycles:                            4
% 3.01/1.01  pred_elim_time:                         0.035
% 3.01/1.01  splitting_time:                         0.
% 3.01/1.01  sem_filter_time:                        0.
% 3.01/1.01  monotx_time:                            0.001
% 3.01/1.01  subtype_inf_time:                       0.
% 3.01/1.01  
% 3.01/1.01  ------ Problem properties
% 3.01/1.01  
% 3.01/1.01  clauses:                                32
% 3.01/1.01  conjectures:                            17
% 3.01/1.01  epr:                                    15
% 3.01/1.01  horn:                                   25
% 3.01/1.01  ground:                                 17
% 3.01/1.01  unary:                                  18
% 3.01/1.01  binary:                                 2
% 3.01/1.01  lits:                                   116
% 3.01/1.01  lits_eq:                                12
% 3.01/1.01  fd_pure:                                0
% 3.01/1.01  fd_pseudo:                              0
% 3.01/1.01  fd_cond:                                0
% 3.01/1.01  fd_pseudo_cond:                         1
% 3.01/1.01  ac_symbols:                             0
% 3.01/1.01  
% 3.01/1.01  ------ Propositional Solver
% 3.01/1.01  
% 3.01/1.01  prop_solver_calls:                      27
% 3.01/1.01  prop_fast_solver_calls:                 2060
% 3.01/1.01  smt_solver_calls:                       0
% 3.01/1.01  smt_fast_solver_calls:                  0
% 3.01/1.01  prop_num_of_clauses:                    2368
% 3.01/1.01  prop_preprocess_simplified:             6351
% 3.01/1.01  prop_fo_subsumed:                       71
% 3.01/1.01  prop_solver_time:                       0.
% 3.01/1.01  smt_solver_time:                        0.
% 3.01/1.01  smt_fast_solver_time:                   0.
% 3.01/1.01  prop_fast_solver_time:                  0.
% 3.01/1.01  prop_unsat_core_time:                   0.
% 3.01/1.01  
% 3.01/1.01  ------ QBF
% 3.01/1.01  
% 3.01/1.01  qbf_q_res:                              0
% 3.01/1.01  qbf_num_tautologies:                    0
% 3.01/1.01  qbf_prep_cycles:                        0
% 3.01/1.01  
% 3.01/1.01  ------ BMC1
% 3.01/1.01  
% 3.01/1.01  bmc1_current_bound:                     -1
% 3.01/1.01  bmc1_last_solved_bound:                 -1
% 3.01/1.01  bmc1_unsat_core_size:                   -1
% 3.01/1.01  bmc1_unsat_core_parents_size:           -1
% 3.01/1.01  bmc1_merge_next_fun:                    0
% 3.01/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.01/1.01  
% 3.01/1.01  ------ Instantiation
% 3.01/1.01  
% 3.01/1.01  inst_num_of_clauses:                    748
% 3.01/1.01  inst_num_in_passive:                    40
% 3.01/1.01  inst_num_in_active:                     388
% 3.01/1.01  inst_num_in_unprocessed:                320
% 3.01/1.01  inst_num_of_loops:                      420
% 3.01/1.01  inst_num_of_learning_restarts:          0
% 3.01/1.01  inst_num_moves_active_passive:          29
% 3.01/1.01  inst_lit_activity:                      0
% 3.01/1.01  inst_lit_activity_moves:                0
% 3.01/1.01  inst_num_tautologies:                   0
% 3.01/1.01  inst_num_prop_implied:                  0
% 3.01/1.01  inst_num_existing_simplified:           0
% 3.01/1.01  inst_num_eq_res_simplified:             0
% 3.01/1.01  inst_num_child_elim:                    0
% 3.01/1.01  inst_num_of_dismatching_blockings:      65
% 3.01/1.01  inst_num_of_non_proper_insts:           622
% 3.01/1.01  inst_num_of_duplicates:                 0
% 3.01/1.01  inst_inst_num_from_inst_to_res:         0
% 3.01/1.01  inst_dismatching_checking_time:         0.
% 3.01/1.01  
% 3.01/1.01  ------ Resolution
% 3.01/1.01  
% 3.01/1.01  res_num_of_clauses:                     0
% 3.01/1.01  res_num_in_passive:                     0
% 3.01/1.01  res_num_in_active:                      0
% 3.01/1.01  res_num_of_loops:                       174
% 3.01/1.01  res_forward_subset_subsumed:            46
% 3.01/1.01  res_backward_subset_subsumed:           0
% 3.01/1.01  res_forward_subsumed:                   0
% 3.01/1.01  res_backward_subsumed:                  0
% 3.01/1.01  res_forward_subsumption_resolution:     6
% 3.01/1.01  res_backward_subsumption_resolution:    0
% 3.01/1.01  res_clause_to_clause_subsumption:       443
% 3.01/1.01  res_orphan_elimination:                 0
% 3.01/1.01  res_tautology_del:                      96
% 3.01/1.01  res_num_eq_res_simplified:              0
% 3.01/1.01  res_num_sel_changes:                    0
% 3.01/1.01  res_moves_from_active_to_pass:          0
% 3.01/1.01  
% 3.01/1.01  ------ Superposition
% 3.01/1.01  
% 3.01/1.01  sup_time_total:                         0.
% 3.01/1.01  sup_time_generating:                    0.
% 3.01/1.01  sup_time_sim_full:                      0.
% 3.01/1.01  sup_time_sim_immed:                     0.
% 3.01/1.01  
% 3.01/1.01  sup_num_of_clauses:                     107
% 3.01/1.01  sup_num_in_active:                      67
% 3.01/1.01  sup_num_in_passive:                     40
% 3.01/1.01  sup_num_of_loops:                       82
% 3.01/1.01  sup_fw_superposition:                   59
% 3.01/1.01  sup_bw_superposition:                   29
% 3.01/1.01  sup_immediate_simplified:               16
% 3.01/1.01  sup_given_eliminated:                   0
% 3.01/1.01  comparisons_done:                       0
% 3.01/1.01  comparisons_avoided:                    0
% 3.01/1.01  
% 3.01/1.01  ------ Simplifications
% 3.01/1.01  
% 3.01/1.01  
% 3.01/1.01  sim_fw_subset_subsumed:                 5
% 3.01/1.01  sim_bw_subset_subsumed:                 2
% 3.01/1.01  sim_fw_subsumed:                        4
% 3.01/1.01  sim_bw_subsumed:                        0
% 3.01/1.01  sim_fw_subsumption_res:                 0
% 3.01/1.01  sim_bw_subsumption_res:                 0
% 3.01/1.01  sim_tautology_del:                      0
% 3.01/1.01  sim_eq_tautology_del:                   0
% 3.01/1.01  sim_eq_res_simp:                        0
% 3.01/1.01  sim_fw_demodulated:                     2
% 3.01/1.01  sim_bw_demodulated:                     15
% 3.01/1.01  sim_light_normalised:                   14
% 3.01/1.01  sim_joinable_taut:                      0
% 3.01/1.01  sim_joinable_simp:                      0
% 3.01/1.01  sim_ac_normalised:                      0
% 3.01/1.01  sim_smt_subsumption:                    0
% 3.01/1.01  
%------------------------------------------------------------------------------
