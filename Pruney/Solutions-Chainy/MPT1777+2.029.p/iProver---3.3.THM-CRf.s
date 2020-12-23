%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:30 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  245 (1381 expanded)
%              Number of clauses        :  143 ( 335 expanded)
%              Number of leaves         :   27 ( 577 expanded)
%              Depth                    :   31
%              Number of atoms          : 1524 (18588 expanded)
%              Number of equality atoms :  433 (2815 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ~ r1_tmap_1(X3,X1,X4,X5)
          & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
          & X5 = X6
          & m1_subset_1(X6,u1_struct_0(X2)) )
     => ( ~ r1_tmap_1(X3,X1,X4,X5)
        & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK10)
        & sK10 = X5
        & m1_subset_1(sK10,u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(X3,X1,X4,X5)
              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(X2)) )
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ? [X6] :
            ( ~ r1_tmap_1(X3,X1,X4,sK9)
            & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
            & sK9 = X6
            & m1_subset_1(X6,u1_struct_0(X2)) )
        & m1_subset_1(sK9,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
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
                ( ~ r1_tmap_1(X3,X1,sK8,X5)
                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK8),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(X2)) )
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
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
                    ( ~ r1_tmap_1(sK7,X1,X4,X5)
                    & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK7,X2,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X2)) )
                & m1_subset_1(X5,u1_struct_0(sK7)) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK7
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & m1_pre_topc(sK7,X0)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
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
                        & r1_tmap_1(sK6,X1,k3_tmap_1(X0,X1,X3,sK6,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(sK6)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
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
                            ( ~ r1_tmap_1(X3,sK5,X4,X5)
                            & r1_tmap_1(X2,sK5,k3_tmap_1(X0,sK5,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK5)
        & v2_pre_topc(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
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
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK4)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK4)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,
    ( ~ r1_tmap_1(sK7,sK5,sK8,sK9)
    & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)
    & sK9 = sK10
    & m1_subset_1(sK10,u1_struct_0(sK6))
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
    & v1_funct_1(sK8)
    & m1_pre_topc(sK7,sK4)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f46,f72,f71,f70,f69,f68,f67,f66])).

fof(f119,plain,(
    m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f73])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f111,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f73])).

fof(f112,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f73])).

fof(f117,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f73])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f94,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f105,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f123,plain,(
    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f73])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f11,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f99,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f121,plain,(
    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f73])).

fof(f120,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f73])).

fof(f113,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f73])).

fof(f114,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f73])).

fof(f115,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f73])).

fof(f118,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f73])).

fof(f122,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f73])).

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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f110,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f73])).

fof(f127,plain,(
    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(cnf_transformation,[],[f73])).

fof(f126,plain,(
    sK9 = sK10 ),
    inference(cnf_transformation,[],[f73])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f132,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f102])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

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
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(flattening,[],[f41])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_tmap_1(X1,X0,X2,X4)
                              | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) ) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(nnf_transformation,[],[f42])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X4)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
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
    inference(cnf_transformation,[],[f65])).

fof(f134,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
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

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f116,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f73])).

fof(f128,plain,(
    ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f73])).

fof(f125,plain,(
    m1_subset_1(sK10,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f73])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f48,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f25,f47])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
            & r1_tarski(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).

fof(f86,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_45,negated_conjecture,
    ( m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3059,plain,
    ( m1_pre_topc(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3084,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6654,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3059,c_3084])).

cnf(c_53,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_56,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_52,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_57,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_6943,plain,
    ( v2_pre_topc(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6654,c_56,c_57])).

cnf(c_47,negated_conjecture,
    ( m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_3057,plain,
    ( m1_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3071,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5565,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3057,c_3071])).

cnf(c_5999,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5565,c_57])).

cnf(c_31,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3067,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_41,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_300,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_20])).

cnf(c_301,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_300])).

cnf(c_3049,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_301])).

cnf(c_4968,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | m1_pre_topc(X0,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_41,c_3049])).

cnf(c_5136,plain,
    ( m1_pre_topc(sK6,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3067,c_4968])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f99])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_786,plain,
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
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_43])).

cnf(c_787,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(sK8)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_791,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_787,c_44])).

cnf(c_792,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(renaming,[status(thm)],[c_791])).

cnf(c_3047,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK8,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK8,X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_4081,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3047])).

cnf(c_51,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_58,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_50,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_59,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_49,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_60,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_4437,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4081,c_58,c_59,c_60])).

cnf(c_4438,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4437])).

cnf(c_4448,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4438])).

cnf(c_46,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_63,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_64,plain,
    ( m1_pre_topc(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_67,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_3792,plain,
    ( ~ m1_pre_topc(sK7,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_4326,plain,
    ( ~ m1_pre_topc(sK7,sK4)
    | ~ l1_pre_topc(sK4)
    | l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_3792])).

cnf(c_4327,plain,
    ( m1_pre_topc(sK7,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4326])).

cnf(c_4581,plain,
    ( m1_pre_topc(X0,sK7) != iProver_top
    | k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
    | v2_pre_topc(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4448,c_57,c_63,c_64,c_67,c_4327])).

cnf(c_4582,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
    | m1_pre_topc(X0,sK7) != iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_4581])).

cnf(c_5298,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k2_tmap_1(sK7,sK5,sK8,sK6)
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5136,c_4582])).

cnf(c_6005,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k2_tmap_1(sK7,sK5,sK8,sK6)
    | v2_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5999,c_5298])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_735,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
    | u1_struct_0(X4) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | sK8 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_43])).

cnf(c_736,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_1(sK8)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_735])).

cnf(c_740,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_736,c_44])).

cnf(c_741,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(renaming,[status(thm)],[c_740])).

cnf(c_35,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_772,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_741,c_35])).

cnf(c_3048,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK8,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK8)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_4225,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3048])).

cnf(c_4684,plain,
    ( v2_pre_topc(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
    | l1_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4225,c_58,c_59,c_60])).

cnf(c_4685,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4684])).

cnf(c_4696,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_pre_topc(sK7,X1) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4685])).

cnf(c_5364,plain,
    ( m1_pre_topc(sK7,X1) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4696,c_67])).

cnf(c_5365,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_pre_topc(sK7,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5364])).

cnf(c_5377,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(X0,sK5,sK7,sK6,sK8)
    | m1_pre_topc(sK7,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5136,c_5365])).

cnf(c_5417,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8)
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3059,c_5377])).

cnf(c_54,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_55,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_6130,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5417,c_55,c_56,c_57,c_5565])).

cnf(c_6378,plain,
    ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k2_tmap_1(sK7,sK5,sK8,sK6)
    | v2_pre_topc(sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6005,c_6130])).

cnf(c_6948,plain,
    ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k2_tmap_1(sK7,sK5,sK8,sK6) ),
    inference(superposition,[status(thm)],[c_6943,c_6378])).

cnf(c_37,negated_conjecture,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_3063,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_38,negated_conjecture,
    ( sK9 = sK10 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_3132,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3063,c_38])).

cnf(c_7210,plain,
    ( r1_tmap_1(sK6,sK5,k2_tmap_1(sK7,sK5,sK8,sK6),sK9) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6948,c_3132])).

cnf(c_18,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_28,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_30,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_291,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_30])).

cnf(c_292,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_291])).

cnf(c_558,plain,
    ( v1_tsep_1(X0,X1)
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | X1 != X3
    | u1_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_292])).

cnf(c_559,plain,
    ( v1_tsep_1(X0,X1)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_563,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_559,c_30])).

cnf(c_564,plain,
    ( v1_tsep_1(X0,X1)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_563])).

cnf(c_33,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
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
    inference(cnf_transformation,[],[f134])).

cnf(c_679,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X6))
    | ~ m1_pre_topc(X5,X6)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | X4 != X5
    | X0 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_564,c_33])).

cnf(c_680,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_716,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_680,c_21])).

cnf(c_831,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X0))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_716,c_43])).

cnf(c_832,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
    | r1_tmap_1(X2,X1,sK8,X3)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK8)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X2) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_831])).

cnf(c_836,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
    | r1_tmap_1(X2,X1,sK8,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X2) != u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_832,c_44])).

cnf(c_837,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
    | r1_tmap_1(X2,X1,sK8,X3)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X2) != u1_struct_0(sK7) ),
    inference(renaming,[status(thm)],[c_836])).

cnf(c_3046,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK8,X2),X3) != iProver_top
    | r1_tmap_1(X1,X0,sK8,X3) = iProver_top
    | r2_hidden(u1_struct_0(X2),u1_pre_topc(X1)) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_837])).

cnf(c_4208,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
    | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X1,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3046])).

cnf(c_2287,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3493,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2287])).

cnf(c_3749,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK7,X1,sK8,X0),X2)
    | r1_tmap_1(sK7,X1,sK8,X2)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7))
    | ~ m1_pre_topc(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK7)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(sK7) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_3750,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
    | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X1,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3749])).

cnf(c_4558,plain,
    ( l1_pre_topc(X0) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
    | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X1,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4208,c_57,c_63,c_64,c_3493,c_3750,c_4327])).

cnf(c_4559,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
    | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X1,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_4558])).

cnf(c_4576,plain,
    ( r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4559])).

cnf(c_4835,plain,
    ( v2_struct_0(X0) = iProver_top
    | r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4576,c_58,c_59,c_60,c_67])).

cnf(c_4836,plain,
    ( r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_4835])).

cnf(c_7218,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(sK6,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7210,c_4836])).

cnf(c_48,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_61,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_36,negated_conjecture,
    ( ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_71,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK10,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_3062,plain,
    ( m1_subset_1(sK10,u1_struct_0(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3116,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3062,c_38])).

cnf(c_10602,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7218,c_56,c_57,c_61,c_71,c_3116,c_5136,c_5565,c_6654])).

cnf(c_22,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3069,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6517,plain,
    ( m1_pre_topc(X0,sK6) = iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_41,c_3069])).

cnf(c_6630,plain,
    ( m1_pre_topc(X0,sK7) != iProver_top
    | m1_pre_topc(X0,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6517,c_57,c_5565])).

cnf(c_6631,plain,
    ( m1_pre_topc(X0,sK6) = iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_6630])).

cnf(c_6638,plain,
    ( m1_pre_topc(sK7,sK6) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3067,c_6631])).

cnf(c_6768,plain,
    ( m1_pre_topc(sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6638,c_57,c_64,c_4327])).

cnf(c_32,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3066,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3087,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6386,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3066,c_3087])).

cnf(c_8361,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3066,c_6386])).

cnf(c_107,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8992,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1)
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8361,c_107])).

cnf(c_8993,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_8992])).

cnf(c_9008,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK6)
    | m1_pre_topc(sK6,sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6768,c_8993])).

cnf(c_9005,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK6)
    | m1_pre_topc(sK7,sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5136,c_8993])).

cnf(c_9291,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9008,c_57,c_64,c_4327,c_5565,c_6638,c_9005])).

cnf(c_10606,plain,
    ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10602,c_9291])).

cnf(c_17,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_8786,plain,
    ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_8787,plain,
    ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) = iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8786])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10606,c_8787,c_6654,c_4327,c_64,c_57,c_56])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.57/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.57/0.98  
% 3.57/0.98  ------  iProver source info
% 3.57/0.98  
% 3.57/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.57/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.57/0.98  git: non_committed_changes: false
% 3.57/0.98  git: last_make_outside_of_git: false
% 3.57/0.98  
% 3.57/0.98  ------ 
% 3.57/0.98  
% 3.57/0.98  ------ Input Options
% 3.57/0.98  
% 3.57/0.98  --out_options                           all
% 3.57/0.98  --tptp_safe_out                         true
% 3.57/0.98  --problem_path                          ""
% 3.57/0.98  --include_path                          ""
% 3.57/0.98  --clausifier                            res/vclausify_rel
% 3.57/0.98  --clausifier_options                    --mode clausify
% 3.57/0.98  --stdin                                 false
% 3.57/0.98  --stats_out                             all
% 3.57/0.98  
% 3.57/0.98  ------ General Options
% 3.57/0.98  
% 3.57/0.98  --fof                                   false
% 3.57/0.98  --time_out_real                         305.
% 3.57/0.98  --time_out_virtual                      -1.
% 3.57/0.98  --symbol_type_check                     false
% 3.57/0.98  --clausify_out                          false
% 3.57/0.98  --sig_cnt_out                           false
% 3.57/0.98  --trig_cnt_out                          false
% 3.57/0.98  --trig_cnt_out_tolerance                1.
% 3.57/0.98  --trig_cnt_out_sk_spl                   false
% 3.57/0.98  --abstr_cl_out                          false
% 3.57/0.98  
% 3.57/0.98  ------ Global Options
% 3.57/0.98  
% 3.57/0.98  --schedule                              default
% 3.57/0.98  --add_important_lit                     false
% 3.57/0.98  --prop_solver_per_cl                    1000
% 3.57/0.98  --min_unsat_core                        false
% 3.57/0.98  --soft_assumptions                      false
% 3.57/0.98  --soft_lemma_size                       3
% 3.57/0.98  --prop_impl_unit_size                   0
% 3.57/0.98  --prop_impl_unit                        []
% 3.57/0.98  --share_sel_clauses                     true
% 3.57/0.98  --reset_solvers                         false
% 3.57/0.98  --bc_imp_inh                            [conj_cone]
% 3.57/0.98  --conj_cone_tolerance                   3.
% 3.57/0.98  --extra_neg_conj                        none
% 3.57/0.98  --large_theory_mode                     true
% 3.57/0.98  --prolific_symb_bound                   200
% 3.57/0.98  --lt_threshold                          2000
% 3.57/0.98  --clause_weak_htbl                      true
% 3.57/0.98  --gc_record_bc_elim                     false
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing Options
% 3.57/0.98  
% 3.57/0.98  --preprocessing_flag                    true
% 3.57/0.98  --time_out_prep_mult                    0.1
% 3.57/0.98  --splitting_mode                        input
% 3.57/0.98  --splitting_grd                         true
% 3.57/0.98  --splitting_cvd                         false
% 3.57/0.98  --splitting_cvd_svl                     false
% 3.57/0.98  --splitting_nvd                         32
% 3.57/0.98  --sub_typing                            true
% 3.57/0.98  --prep_gs_sim                           true
% 3.57/0.98  --prep_unflatten                        true
% 3.57/0.98  --prep_res_sim                          true
% 3.57/0.98  --prep_upred                            true
% 3.57/0.98  --prep_sem_filter                       exhaustive
% 3.57/0.98  --prep_sem_filter_out                   false
% 3.57/0.98  --pred_elim                             true
% 3.57/0.98  --res_sim_input                         true
% 3.57/0.98  --eq_ax_congr_red                       true
% 3.57/0.98  --pure_diseq_elim                       true
% 3.57/0.98  --brand_transform                       false
% 3.57/0.98  --non_eq_to_eq                          false
% 3.57/0.98  --prep_def_merge                        true
% 3.57/0.98  --prep_def_merge_prop_impl              false
% 3.57/0.98  --prep_def_merge_mbd                    true
% 3.57/0.98  --prep_def_merge_tr_red                 false
% 3.57/0.98  --prep_def_merge_tr_cl                  false
% 3.57/0.98  --smt_preprocessing                     true
% 3.57/0.98  --smt_ac_axioms                         fast
% 3.57/0.98  --preprocessed_out                      false
% 3.57/0.98  --preprocessed_stats                    false
% 3.57/0.98  
% 3.57/0.98  ------ Abstraction refinement Options
% 3.57/0.98  
% 3.57/0.98  --abstr_ref                             []
% 3.57/0.98  --abstr_ref_prep                        false
% 3.57/0.98  --abstr_ref_until_sat                   false
% 3.57/0.98  --abstr_ref_sig_restrict                funpre
% 3.57/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.98  --abstr_ref_under                       []
% 3.57/0.98  
% 3.57/0.98  ------ SAT Options
% 3.57/0.98  
% 3.57/0.98  --sat_mode                              false
% 3.57/0.98  --sat_fm_restart_options                ""
% 3.57/0.98  --sat_gr_def                            false
% 3.57/0.98  --sat_epr_types                         true
% 3.57/0.98  --sat_non_cyclic_types                  false
% 3.57/0.98  --sat_finite_models                     false
% 3.57/0.98  --sat_fm_lemmas                         false
% 3.57/0.98  --sat_fm_prep                           false
% 3.57/0.98  --sat_fm_uc_incr                        true
% 3.57/0.98  --sat_out_model                         small
% 3.57/0.98  --sat_out_clauses                       false
% 3.57/0.98  
% 3.57/0.98  ------ QBF Options
% 3.57/0.98  
% 3.57/0.98  --qbf_mode                              false
% 3.57/0.98  --qbf_elim_univ                         false
% 3.57/0.98  --qbf_dom_inst                          none
% 3.57/0.98  --qbf_dom_pre_inst                      false
% 3.57/0.98  --qbf_sk_in                             false
% 3.57/0.98  --qbf_pred_elim                         true
% 3.57/0.98  --qbf_split                             512
% 3.57/0.98  
% 3.57/0.98  ------ BMC1 Options
% 3.57/0.98  
% 3.57/0.98  --bmc1_incremental                      false
% 3.57/0.98  --bmc1_axioms                           reachable_all
% 3.57/0.98  --bmc1_min_bound                        0
% 3.57/0.98  --bmc1_max_bound                        -1
% 3.57/0.98  --bmc1_max_bound_default                -1
% 3.57/0.98  --bmc1_symbol_reachability              true
% 3.57/0.98  --bmc1_property_lemmas                  false
% 3.57/0.98  --bmc1_k_induction                      false
% 3.57/0.98  --bmc1_non_equiv_states                 false
% 3.57/0.98  --bmc1_deadlock                         false
% 3.57/0.98  --bmc1_ucm                              false
% 3.57/0.98  --bmc1_add_unsat_core                   none
% 3.57/0.98  --bmc1_unsat_core_children              false
% 3.57/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.98  --bmc1_out_stat                         full
% 3.57/0.98  --bmc1_ground_init                      false
% 3.57/0.98  --bmc1_pre_inst_next_state              false
% 3.57/0.98  --bmc1_pre_inst_state                   false
% 3.57/0.98  --bmc1_pre_inst_reach_state             false
% 3.57/0.98  --bmc1_out_unsat_core                   false
% 3.57/0.98  --bmc1_aig_witness_out                  false
% 3.57/0.98  --bmc1_verbose                          false
% 3.57/0.98  --bmc1_dump_clauses_tptp                false
% 3.57/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.98  --bmc1_dump_file                        -
% 3.57/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.98  --bmc1_ucm_extend_mode                  1
% 3.57/0.98  --bmc1_ucm_init_mode                    2
% 3.57/0.98  --bmc1_ucm_cone_mode                    none
% 3.57/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.98  --bmc1_ucm_relax_model                  4
% 3.57/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.98  --bmc1_ucm_layered_model                none
% 3.57/0.98  --bmc1_ucm_max_lemma_size               10
% 3.57/0.98  
% 3.57/0.98  ------ AIG Options
% 3.57/0.98  
% 3.57/0.98  --aig_mode                              false
% 3.57/0.98  
% 3.57/0.98  ------ Instantiation Options
% 3.57/0.98  
% 3.57/0.98  --instantiation_flag                    true
% 3.57/0.98  --inst_sos_flag                         false
% 3.57/0.98  --inst_sos_phase                        true
% 3.57/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.98  --inst_lit_sel_side                     num_symb
% 3.57/0.98  --inst_solver_per_active                1400
% 3.57/0.98  --inst_solver_calls_frac                1.
% 3.57/0.98  --inst_passive_queue_type               priority_queues
% 3.57/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.98  --inst_passive_queues_freq              [25;2]
% 3.57/0.98  --inst_dismatching                      true
% 3.57/0.98  --inst_eager_unprocessed_to_passive     true
% 3.57/0.98  --inst_prop_sim_given                   true
% 3.57/0.98  --inst_prop_sim_new                     false
% 3.57/0.98  --inst_subs_new                         false
% 3.57/0.98  --inst_eq_res_simp                      false
% 3.57/0.98  --inst_subs_given                       false
% 3.57/0.98  --inst_orphan_elimination               true
% 3.57/0.98  --inst_learning_loop_flag               true
% 3.57/0.98  --inst_learning_start                   3000
% 3.57/0.98  --inst_learning_factor                  2
% 3.57/0.98  --inst_start_prop_sim_after_learn       3
% 3.57/0.98  --inst_sel_renew                        solver
% 3.57/0.98  --inst_lit_activity_flag                true
% 3.57/0.98  --inst_restr_to_given                   false
% 3.57/0.98  --inst_activity_threshold               500
% 3.57/0.98  --inst_out_proof                        true
% 3.57/0.98  
% 3.57/0.98  ------ Resolution Options
% 3.57/0.98  
% 3.57/0.98  --resolution_flag                       true
% 3.57/0.98  --res_lit_sel                           adaptive
% 3.57/0.98  --res_lit_sel_side                      none
% 3.57/0.98  --res_ordering                          kbo
% 3.57/0.98  --res_to_prop_solver                    active
% 3.57/0.98  --res_prop_simpl_new                    false
% 3.57/0.98  --res_prop_simpl_given                  true
% 3.57/0.98  --res_passive_queue_type                priority_queues
% 3.57/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.98  --res_passive_queues_freq               [15;5]
% 3.57/0.98  --res_forward_subs                      full
% 3.57/0.98  --res_backward_subs                     full
% 3.57/0.98  --res_forward_subs_resolution           true
% 3.57/0.98  --res_backward_subs_resolution          true
% 3.57/0.98  --res_orphan_elimination                true
% 3.57/0.98  --res_time_limit                        2.
% 3.57/0.98  --res_out_proof                         true
% 3.57/0.98  
% 3.57/0.98  ------ Superposition Options
% 3.57/0.98  
% 3.57/0.98  --superposition_flag                    true
% 3.57/0.98  --sup_passive_queue_type                priority_queues
% 3.57/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.57/0.98  --demod_completeness_check              fast
% 3.57/0.98  --demod_use_ground                      true
% 3.57/0.98  --sup_to_prop_solver                    passive
% 3.57/0.98  --sup_prop_simpl_new                    true
% 3.57/0.98  --sup_prop_simpl_given                  true
% 3.57/0.98  --sup_fun_splitting                     false
% 3.57/0.98  --sup_smt_interval                      50000
% 3.57/0.98  
% 3.57/0.98  ------ Superposition Simplification Setup
% 3.57/0.98  
% 3.57/0.98  --sup_indices_passive                   []
% 3.57/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.98  --sup_full_bw                           [BwDemod]
% 3.57/0.98  --sup_immed_triv                        [TrivRules]
% 3.57/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.98  --sup_immed_bw_main                     []
% 3.57/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.98  
% 3.57/0.98  ------ Combination Options
% 3.57/0.98  
% 3.57/0.98  --comb_res_mult                         3
% 3.57/0.98  --comb_sup_mult                         2
% 3.57/0.98  --comb_inst_mult                        10
% 3.57/0.98  
% 3.57/0.98  ------ Debug Options
% 3.57/0.98  
% 3.57/0.98  --dbg_backtrace                         false
% 3.57/0.98  --dbg_dump_prop_clauses                 false
% 3.57/0.98  --dbg_dump_prop_clauses_file            -
% 3.57/0.98  --dbg_out_stat                          false
% 3.57/0.98  ------ Parsing...
% 3.57/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.57/0.98  ------ Proving...
% 3.57/0.98  ------ Problem Properties 
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  clauses                                 46
% 3.57/0.98  conjectures                             17
% 3.57/0.98  EPR                                     19
% 3.57/0.98  Horn                                    35
% 3.57/0.98  unary                                   20
% 3.57/0.98  binary                                  6
% 3.57/0.98  lits                                    150
% 3.57/0.98  lits eq                                 14
% 3.57/0.98  fd_pure                                 0
% 3.57/0.98  fd_pseudo                               0
% 3.57/0.98  fd_cond                                 0
% 3.57/0.98  fd_pseudo_cond                          1
% 3.57/0.98  AC symbols                              0
% 3.57/0.98  
% 3.57/0.98  ------ Schedule dynamic 5 is on 
% 3.57/0.98  
% 3.57/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  ------ 
% 3.57/0.98  Current options:
% 3.57/0.98  ------ 
% 3.57/0.98  
% 3.57/0.98  ------ Input Options
% 3.57/0.98  
% 3.57/0.98  --out_options                           all
% 3.57/0.98  --tptp_safe_out                         true
% 3.57/0.98  --problem_path                          ""
% 3.57/0.98  --include_path                          ""
% 3.57/0.98  --clausifier                            res/vclausify_rel
% 3.57/0.98  --clausifier_options                    --mode clausify
% 3.57/0.98  --stdin                                 false
% 3.57/0.98  --stats_out                             all
% 3.57/0.98  
% 3.57/0.98  ------ General Options
% 3.57/0.98  
% 3.57/0.98  --fof                                   false
% 3.57/0.98  --time_out_real                         305.
% 3.57/0.98  --time_out_virtual                      -1.
% 3.57/0.98  --symbol_type_check                     false
% 3.57/0.98  --clausify_out                          false
% 3.57/0.98  --sig_cnt_out                           false
% 3.57/0.98  --trig_cnt_out                          false
% 3.57/0.98  --trig_cnt_out_tolerance                1.
% 3.57/0.98  --trig_cnt_out_sk_spl                   false
% 3.57/0.98  --abstr_cl_out                          false
% 3.57/0.98  
% 3.57/0.98  ------ Global Options
% 3.57/0.98  
% 3.57/0.98  --schedule                              default
% 3.57/0.98  --add_important_lit                     false
% 3.57/0.98  --prop_solver_per_cl                    1000
% 3.57/0.98  --min_unsat_core                        false
% 3.57/0.98  --soft_assumptions                      false
% 3.57/0.98  --soft_lemma_size                       3
% 3.57/0.98  --prop_impl_unit_size                   0
% 3.57/0.98  --prop_impl_unit                        []
% 3.57/0.98  --share_sel_clauses                     true
% 3.57/0.98  --reset_solvers                         false
% 3.57/0.98  --bc_imp_inh                            [conj_cone]
% 3.57/0.98  --conj_cone_tolerance                   3.
% 3.57/0.98  --extra_neg_conj                        none
% 3.57/0.98  --large_theory_mode                     true
% 3.57/0.98  --prolific_symb_bound                   200
% 3.57/0.98  --lt_threshold                          2000
% 3.57/0.98  --clause_weak_htbl                      true
% 3.57/0.98  --gc_record_bc_elim                     false
% 3.57/0.98  
% 3.57/0.98  ------ Preprocessing Options
% 3.57/0.98  
% 3.57/0.98  --preprocessing_flag                    true
% 3.57/0.98  --time_out_prep_mult                    0.1
% 3.57/0.98  --splitting_mode                        input
% 3.57/0.98  --splitting_grd                         true
% 3.57/0.98  --splitting_cvd                         false
% 3.57/0.98  --splitting_cvd_svl                     false
% 3.57/0.98  --splitting_nvd                         32
% 3.57/0.98  --sub_typing                            true
% 3.57/0.98  --prep_gs_sim                           true
% 3.57/0.98  --prep_unflatten                        true
% 3.57/0.98  --prep_res_sim                          true
% 3.57/0.98  --prep_upred                            true
% 3.57/0.98  --prep_sem_filter                       exhaustive
% 3.57/0.98  --prep_sem_filter_out                   false
% 3.57/0.98  --pred_elim                             true
% 3.57/0.98  --res_sim_input                         true
% 3.57/0.98  --eq_ax_congr_red                       true
% 3.57/0.98  --pure_diseq_elim                       true
% 3.57/0.98  --brand_transform                       false
% 3.57/0.98  --non_eq_to_eq                          false
% 3.57/0.98  --prep_def_merge                        true
% 3.57/0.98  --prep_def_merge_prop_impl              false
% 3.57/0.98  --prep_def_merge_mbd                    true
% 3.57/0.98  --prep_def_merge_tr_red                 false
% 3.57/0.98  --prep_def_merge_tr_cl                  false
% 3.57/0.98  --smt_preprocessing                     true
% 3.57/0.98  --smt_ac_axioms                         fast
% 3.57/0.98  --preprocessed_out                      false
% 3.57/0.98  --preprocessed_stats                    false
% 3.57/0.98  
% 3.57/0.98  ------ Abstraction refinement Options
% 3.57/0.98  
% 3.57/0.98  --abstr_ref                             []
% 3.57/0.98  --abstr_ref_prep                        false
% 3.57/0.98  --abstr_ref_until_sat                   false
% 3.57/0.98  --abstr_ref_sig_restrict                funpre
% 3.57/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/0.98  --abstr_ref_under                       []
% 3.57/0.98  
% 3.57/0.98  ------ SAT Options
% 3.57/0.98  
% 3.57/0.98  --sat_mode                              false
% 3.57/0.98  --sat_fm_restart_options                ""
% 3.57/0.98  --sat_gr_def                            false
% 3.57/0.98  --sat_epr_types                         true
% 3.57/0.98  --sat_non_cyclic_types                  false
% 3.57/0.98  --sat_finite_models                     false
% 3.57/0.98  --sat_fm_lemmas                         false
% 3.57/0.98  --sat_fm_prep                           false
% 3.57/0.98  --sat_fm_uc_incr                        true
% 3.57/0.98  --sat_out_model                         small
% 3.57/0.98  --sat_out_clauses                       false
% 3.57/0.98  
% 3.57/0.98  ------ QBF Options
% 3.57/0.98  
% 3.57/0.98  --qbf_mode                              false
% 3.57/0.98  --qbf_elim_univ                         false
% 3.57/0.98  --qbf_dom_inst                          none
% 3.57/0.98  --qbf_dom_pre_inst                      false
% 3.57/0.98  --qbf_sk_in                             false
% 3.57/0.98  --qbf_pred_elim                         true
% 3.57/0.98  --qbf_split                             512
% 3.57/0.98  
% 3.57/0.98  ------ BMC1 Options
% 3.57/0.98  
% 3.57/0.98  --bmc1_incremental                      false
% 3.57/0.98  --bmc1_axioms                           reachable_all
% 3.57/0.98  --bmc1_min_bound                        0
% 3.57/0.98  --bmc1_max_bound                        -1
% 3.57/0.98  --bmc1_max_bound_default                -1
% 3.57/0.98  --bmc1_symbol_reachability              true
% 3.57/0.98  --bmc1_property_lemmas                  false
% 3.57/0.98  --bmc1_k_induction                      false
% 3.57/0.98  --bmc1_non_equiv_states                 false
% 3.57/0.98  --bmc1_deadlock                         false
% 3.57/0.98  --bmc1_ucm                              false
% 3.57/0.98  --bmc1_add_unsat_core                   none
% 3.57/0.98  --bmc1_unsat_core_children              false
% 3.57/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/0.98  --bmc1_out_stat                         full
% 3.57/0.98  --bmc1_ground_init                      false
% 3.57/0.98  --bmc1_pre_inst_next_state              false
% 3.57/0.98  --bmc1_pre_inst_state                   false
% 3.57/0.98  --bmc1_pre_inst_reach_state             false
% 3.57/0.98  --bmc1_out_unsat_core                   false
% 3.57/0.98  --bmc1_aig_witness_out                  false
% 3.57/0.98  --bmc1_verbose                          false
% 3.57/0.98  --bmc1_dump_clauses_tptp                false
% 3.57/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.57/0.98  --bmc1_dump_file                        -
% 3.57/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.57/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.57/0.98  --bmc1_ucm_extend_mode                  1
% 3.57/0.98  --bmc1_ucm_init_mode                    2
% 3.57/0.98  --bmc1_ucm_cone_mode                    none
% 3.57/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.57/0.98  --bmc1_ucm_relax_model                  4
% 3.57/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.57/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/0.98  --bmc1_ucm_layered_model                none
% 3.57/0.98  --bmc1_ucm_max_lemma_size               10
% 3.57/0.98  
% 3.57/0.98  ------ AIG Options
% 3.57/0.98  
% 3.57/0.98  --aig_mode                              false
% 3.57/0.98  
% 3.57/0.98  ------ Instantiation Options
% 3.57/0.98  
% 3.57/0.98  --instantiation_flag                    true
% 3.57/0.98  --inst_sos_flag                         false
% 3.57/0.98  --inst_sos_phase                        true
% 3.57/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/0.98  --inst_lit_sel_side                     none
% 3.57/0.98  --inst_solver_per_active                1400
% 3.57/0.98  --inst_solver_calls_frac                1.
% 3.57/0.98  --inst_passive_queue_type               priority_queues
% 3.57/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/0.98  --inst_passive_queues_freq              [25;2]
% 3.57/0.98  --inst_dismatching                      true
% 3.57/0.98  --inst_eager_unprocessed_to_passive     true
% 3.57/0.98  --inst_prop_sim_given                   true
% 3.57/0.98  --inst_prop_sim_new                     false
% 3.57/0.98  --inst_subs_new                         false
% 3.57/0.98  --inst_eq_res_simp                      false
% 3.57/0.98  --inst_subs_given                       false
% 3.57/0.98  --inst_orphan_elimination               true
% 3.57/0.98  --inst_learning_loop_flag               true
% 3.57/0.98  --inst_learning_start                   3000
% 3.57/0.98  --inst_learning_factor                  2
% 3.57/0.98  --inst_start_prop_sim_after_learn       3
% 3.57/0.98  --inst_sel_renew                        solver
% 3.57/0.98  --inst_lit_activity_flag                true
% 3.57/0.98  --inst_restr_to_given                   false
% 3.57/0.98  --inst_activity_threshold               500
% 3.57/0.98  --inst_out_proof                        true
% 3.57/0.98  
% 3.57/0.98  ------ Resolution Options
% 3.57/0.98  
% 3.57/0.98  --resolution_flag                       false
% 3.57/0.98  --res_lit_sel                           adaptive
% 3.57/0.98  --res_lit_sel_side                      none
% 3.57/0.98  --res_ordering                          kbo
% 3.57/0.98  --res_to_prop_solver                    active
% 3.57/0.98  --res_prop_simpl_new                    false
% 3.57/0.98  --res_prop_simpl_given                  true
% 3.57/0.98  --res_passive_queue_type                priority_queues
% 3.57/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/0.98  --res_passive_queues_freq               [15;5]
% 3.57/0.98  --res_forward_subs                      full
% 3.57/0.98  --res_backward_subs                     full
% 3.57/0.98  --res_forward_subs_resolution           true
% 3.57/0.98  --res_backward_subs_resolution          true
% 3.57/0.98  --res_orphan_elimination                true
% 3.57/0.98  --res_time_limit                        2.
% 3.57/0.98  --res_out_proof                         true
% 3.57/0.98  
% 3.57/0.98  ------ Superposition Options
% 3.57/0.98  
% 3.57/0.98  --superposition_flag                    true
% 3.57/0.98  --sup_passive_queue_type                priority_queues
% 3.57/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.57/0.98  --demod_completeness_check              fast
% 3.57/0.98  --demod_use_ground                      true
% 3.57/0.98  --sup_to_prop_solver                    passive
% 3.57/0.98  --sup_prop_simpl_new                    true
% 3.57/0.98  --sup_prop_simpl_given                  true
% 3.57/0.98  --sup_fun_splitting                     false
% 3.57/0.98  --sup_smt_interval                      50000
% 3.57/0.98  
% 3.57/0.98  ------ Superposition Simplification Setup
% 3.57/0.98  
% 3.57/0.98  --sup_indices_passive                   []
% 3.57/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.57/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.98  --sup_full_bw                           [BwDemod]
% 3.57/0.98  --sup_immed_triv                        [TrivRules]
% 3.57/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.98  --sup_immed_bw_main                     []
% 3.57/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.57/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.57/0.98  
% 3.57/0.98  ------ Combination Options
% 3.57/0.98  
% 3.57/0.98  --comb_res_mult                         3
% 3.57/0.98  --comb_sup_mult                         2
% 3.57/0.98  --comb_inst_mult                        10
% 3.57/0.98  
% 3.57/0.98  ------ Debug Options
% 3.57/0.98  
% 3.57/0.98  --dbg_backtrace                         false
% 3.57/0.98  --dbg_dump_prop_clauses                 false
% 3.57/0.98  --dbg_dump_prop_clauses_file            -
% 3.57/0.98  --dbg_out_stat                          false
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  ------ Proving...
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  % SZS status Theorem for theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  fof(f19,conjecture,(
% 3.57/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.98  
% 3.57/0.98  fof(f20,negated_conjecture,(
% 3.57/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.57/0.98    inference(negated_conjecture,[],[f19])).
% 3.57/0.98  
% 3.57/0.98  fof(f45,plain,(
% 3.57/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.57/0.98    inference(ennf_transformation,[],[f20])).
% 3.57/0.98  
% 3.57/0.98  fof(f46,plain,(
% 3.57/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.57/0.98    inference(flattening,[],[f45])).
% 3.57/0.98  
% 3.57/0.98  fof(f72,plain,(
% 3.57/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK10) & sK10 = X5 & m1_subset_1(sK10,u1_struct_0(X2)))) )),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f71,plain,(
% 3.57/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK9) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK9 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK9,u1_struct_0(X3)))) )),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f70,plain,(
% 3.57/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK8,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK8),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f69,plain,(
% 3.57/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK7,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK7,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK7 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK7,X0) & ~v2_struct_0(sK7))) )),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f68,plain,(
% 3.57/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK6,X1,k3_tmap_1(X0,X1,X3,sK6,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f67,plain,(
% 3.57/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK5,X4,X5) & r1_tmap_1(X2,sK5,k3_tmap_1(X0,sK5,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))) )),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f66,plain,(
% 3.57/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 3.57/0.98    introduced(choice_axiom,[])).
% 3.57/0.98  
% 3.57/0.98  fof(f73,plain,(
% 3.57/0.98    ((((((~r1_tmap_1(sK7,sK5,sK8,sK9) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) & sK9 = sK10 & m1_subset_1(sK10,u1_struct_0(sK6))) & m1_subset_1(sK9,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(sK8)) & m1_pre_topc(sK7,sK4) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 3.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f46,f72,f71,f70,f69,f68,f67,f66])).
% 3.57/0.99  
% 3.57/0.99  fof(f119,plain,(
% 3.57/0.99    m1_pre_topc(sK7,sK4)),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f4,axiom,(
% 3.57/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f22,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.57/0.99    inference(ennf_transformation,[],[f4])).
% 3.57/0.99  
% 3.57/0.99  fof(f23,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.57/0.99    inference(flattening,[],[f22])).
% 3.57/0.99  
% 3.57/0.99  fof(f79,plain,(
% 3.57/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f23])).
% 3.57/0.99  
% 3.57/0.99  fof(f111,plain,(
% 3.57/0.99    v2_pre_topc(sK4)),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f112,plain,(
% 3.57/0.99    l1_pre_topc(sK4)),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f117,plain,(
% 3.57/0.99    m1_pre_topc(sK6,sK4)),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f7,axiom,(
% 3.57/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f27,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(ennf_transformation,[],[f7])).
% 3.57/0.99  
% 3.57/0.99  fof(f94,plain,(
% 3.57/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f27])).
% 3.57/0.99  
% 3.57/0.99  fof(f15,axiom,(
% 3.57/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f39,plain,(
% 3.57/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(ennf_transformation,[],[f15])).
% 3.57/0.99  
% 3.57/0.99  fof(f105,plain,(
% 3.57/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f39])).
% 3.57/0.99  
% 3.57/0.99  fof(f123,plain,(
% 3.57/0.99    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f10,axiom,(
% 3.57/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f31,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(ennf_transformation,[],[f10])).
% 3.57/0.99  
% 3.57/0.99  fof(f62,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(nnf_transformation,[],[f31])).
% 3.57/0.99  
% 3.57/0.99  fof(f97,plain,(
% 3.57/0.99    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f62])).
% 3.57/0.99  
% 3.57/0.99  fof(f11,axiom,(
% 3.57/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f32,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.57/0.99    inference(ennf_transformation,[],[f11])).
% 3.57/0.99  
% 3.57/0.99  fof(f33,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.57/0.99    inference(flattening,[],[f32])).
% 3.57/0.99  
% 3.57/0.99  fof(f99,plain,(
% 3.57/0.99    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f33])).
% 3.57/0.99  
% 3.57/0.99  fof(f121,plain,(
% 3.57/0.99    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f120,plain,(
% 3.57/0.99    v1_funct_1(sK8)),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f113,plain,(
% 3.57/0.99    ~v2_struct_0(sK5)),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f114,plain,(
% 3.57/0.99    v2_pre_topc(sK5)),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f115,plain,(
% 3.57/0.99    l1_pre_topc(sK5)),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f118,plain,(
% 3.57/0.99    ~v2_struct_0(sK7)),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f122,plain,(
% 3.57/0.99    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f12,axiom,(
% 3.57/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f34,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.57/0.99    inference(ennf_transformation,[],[f12])).
% 3.57/0.99  
% 3.57/0.99  fof(f35,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.57/0.99    inference(flattening,[],[f34])).
% 3.57/0.99  
% 3.57/0.99  fof(f100,plain,(
% 3.57/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f35])).
% 3.57/0.99  
% 3.57/0.99  fof(f18,axiom,(
% 3.57/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f43,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.57/0.99    inference(ennf_transformation,[],[f18])).
% 3.57/0.99  
% 3.57/0.99  fof(f44,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.57/0.99    inference(flattening,[],[f43])).
% 3.57/0.99  
% 3.57/0.99  fof(f109,plain,(
% 3.57/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f44])).
% 3.57/0.99  
% 3.57/0.99  fof(f110,plain,(
% 3.57/0.99    ~v2_struct_0(sK4)),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f127,plain,(
% 3.57/0.99    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f126,plain,(
% 3.57/0.99    sK9 = sK10),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f6,axiom,(
% 3.57/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f26,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(ennf_transformation,[],[f6])).
% 3.57/0.99  
% 3.57/0.99  fof(f61,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(nnf_transformation,[],[f26])).
% 3.57/0.99  
% 3.57/0.99  fof(f93,plain,(
% 3.57/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f61])).
% 3.57/0.99  
% 3.57/0.99  fof(f13,axiom,(
% 3.57/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f36,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.57/0.99    inference(ennf_transformation,[],[f13])).
% 3.57/0.99  
% 3.57/0.99  fof(f37,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.57/0.99    inference(flattening,[],[f36])).
% 3.57/0.99  
% 3.57/0.99  fof(f63,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.57/0.99    inference(nnf_transformation,[],[f37])).
% 3.57/0.99  
% 3.57/0.99  fof(f64,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.57/0.99    inference(flattening,[],[f63])).
% 3.57/0.99  
% 3.57/0.99  fof(f102,plain,(
% 3.57/0.99    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f64])).
% 3.57/0.99  
% 3.57/0.99  fof(f132,plain,(
% 3.57/0.99    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.57/0.99    inference(equality_resolution,[],[f102])).
% 3.57/0.99  
% 3.57/0.99  fof(f14,axiom,(
% 3.57/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f38,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(ennf_transformation,[],[f14])).
% 3.57/0.99  
% 3.57/0.99  fof(f104,plain,(
% 3.57/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f38])).
% 3.57/0.99  
% 3.57/0.99  fof(f17,axiom,(
% 3.57/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f41,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.57/0.99    inference(ennf_transformation,[],[f17])).
% 3.57/0.99  
% 3.57/0.99  fof(f42,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.57/0.99    inference(flattening,[],[f41])).
% 3.57/0.99  
% 3.57/0.99  fof(f65,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4))) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.57/0.99    inference(nnf_transformation,[],[f42])).
% 3.57/0.99  
% 3.57/0.99  fof(f108,plain,(
% 3.57/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f65])).
% 3.57/0.99  
% 3.57/0.99  fof(f134,plain,(
% 3.57/0.99    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.57/0.99    inference(equality_resolution,[],[f108])).
% 3.57/0.99  
% 3.57/0.99  fof(f8,axiom,(
% 3.57/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f28,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.57/0.99    inference(ennf_transformation,[],[f8])).
% 3.57/0.99  
% 3.57/0.99  fof(f29,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.57/0.99    inference(flattening,[],[f28])).
% 3.57/0.99  
% 3.57/0.99  fof(f95,plain,(
% 3.57/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f29])).
% 3.57/0.99  
% 3.57/0.99  fof(f116,plain,(
% 3.57/0.99    ~v2_struct_0(sK6)),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f128,plain,(
% 3.57/0.99    ~r1_tmap_1(sK7,sK5,sK8,sK9)),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f125,plain,(
% 3.57/0.99    m1_subset_1(sK10,u1_struct_0(sK6))),
% 3.57/0.99    inference(cnf_transformation,[],[f73])).
% 3.57/0.99  
% 3.57/0.99  fof(f9,axiom,(
% 3.57/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f30,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(ennf_transformation,[],[f9])).
% 3.57/0.99  
% 3.57/0.99  fof(f96,plain,(
% 3.57/0.99    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f30])).
% 3.57/0.99  
% 3.57/0.99  fof(f16,axiom,(
% 3.57/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f40,plain,(
% 3.57/0.99    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(ennf_transformation,[],[f16])).
% 3.57/0.99  
% 3.57/0.99  fof(f106,plain,(
% 3.57/0.99    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f40])).
% 3.57/0.99  
% 3.57/0.99  fof(f1,axiom,(
% 3.57/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f49,plain,(
% 3.57/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.57/0.99    inference(nnf_transformation,[],[f1])).
% 3.57/0.99  
% 3.57/0.99  fof(f50,plain,(
% 3.57/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.57/0.99    inference(flattening,[],[f49])).
% 3.57/0.99  
% 3.57/0.99  fof(f76,plain,(
% 3.57/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f50])).
% 3.57/0.99  
% 3.57/0.99  fof(f5,axiom,(
% 3.57/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.57/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.99  
% 3.57/0.99  fof(f21,plain,(
% 3.57/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.57/0.99    inference(rectify,[],[f5])).
% 3.57/0.99  
% 3.57/0.99  fof(f24,plain,(
% 3.57/0.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(ennf_transformation,[],[f21])).
% 3.57/0.99  
% 3.57/0.99  fof(f25,plain,(
% 3.57/0.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(flattening,[],[f24])).
% 3.57/0.99  
% 3.57/0.99  fof(f47,plain,(
% 3.57/0.99    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.57/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.57/0.99  
% 3.57/0.99  fof(f48,plain,(
% 3.57/0.99    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(definition_folding,[],[f25,f47])).
% 3.57/0.99  
% 3.57/0.99  fof(f56,plain,(
% 3.57/0.99    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(nnf_transformation,[],[f48])).
% 3.57/0.99  
% 3.57/0.99  fof(f57,plain,(
% 3.57/0.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(flattening,[],[f56])).
% 3.57/0.99  
% 3.57/0.99  fof(f58,plain,(
% 3.57/0.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(rectify,[],[f57])).
% 3.57/0.99  
% 3.57/0.99  fof(f59,plain,(
% 3.57/0.99    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.57/0.99    introduced(choice_axiom,[])).
% 3.57/0.99  
% 3.57/0.99  fof(f60,plain,(
% 3.57/0.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.57/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f58,f59])).
% 3.57/0.99  
% 3.57/0.99  fof(f86,plain,(
% 3.57/0.99    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.57/0.99    inference(cnf_transformation,[],[f60])).
% 3.57/0.99  
% 3.57/0.99  cnf(c_45,negated_conjecture,
% 3.57/0.99      ( m1_pre_topc(sK7,sK4) ),
% 3.57/0.99      inference(cnf_transformation,[],[f119]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3059,plain,
% 3.57/0.99      ( m1_pre_topc(sK7,sK4) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | v2_pre_topc(X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3084,plain,
% 3.57/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.57/0.99      | l1_pre_topc(X1) != iProver_top
% 3.57/0.99      | v2_pre_topc(X1) != iProver_top
% 3.57/0.99      | v2_pre_topc(X0) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6654,plain,
% 3.57/0.99      ( l1_pre_topc(sK4) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK4) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK7) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3059,c_3084]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_53,negated_conjecture,
% 3.57/0.99      ( v2_pre_topc(sK4) ),
% 3.57/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_56,plain,
% 3.57/0.99      ( v2_pre_topc(sK4) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_52,negated_conjecture,
% 3.57/0.99      ( l1_pre_topc(sK4) ),
% 3.57/0.99      inference(cnf_transformation,[],[f112]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_57,plain,
% 3.57/0.99      ( l1_pre_topc(sK4) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6943,plain,
% 3.57/0.99      ( v2_pre_topc(sK7) = iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_6654,c_56,c_57]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_47,negated_conjecture,
% 3.57/0.99      ( m1_pre_topc(sK6,sK4) ),
% 3.57/0.99      inference(cnf_transformation,[],[f117]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3057,plain,
% 3.57/0.99      ( m1_pre_topc(sK6,sK4) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_20,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3071,plain,
% 3.57/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.57/0.99      | l1_pre_topc(X1) != iProver_top
% 3.57/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5565,plain,
% 3.57/0.99      ( l1_pre_topc(sK4) != iProver_top
% 3.57/0.99      | l1_pre_topc(sK6) = iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3057,c_3071]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5999,plain,
% 3.57/0.99      ( l1_pre_topc(sK6) = iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_5565,c_57]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_31,plain,
% 3.57/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3067,plain,
% 3.57/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.57/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_41,negated_conjecture,
% 3.57/0.99      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
% 3.57/0.99      inference(cnf_transformation,[],[f123]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_24,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.57/0.99      | ~ l1_pre_topc(X0)
% 3.57/0.99      | ~ l1_pre_topc(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_300,plain,
% 3.57/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.57/0.99      | ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ l1_pre_topc(X1) ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_24,c_20]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_301,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.57/0.99      | ~ l1_pre_topc(X1) ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_300]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3049,plain,
% 3.57/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.57/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.57/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_301]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4968,plain,
% 3.57/0.99      ( m1_pre_topc(X0,sK6) != iProver_top
% 3.57/0.99      | m1_pre_topc(X0,sK7) = iProver_top
% 3.57/0.99      | l1_pre_topc(sK6) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_41,c_3049]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5136,plain,
% 3.57/0.99      ( m1_pre_topc(sK6,sK7) = iProver_top
% 3.57/0.99      | l1_pre_topc(sK6) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3067,c_4968]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_25,plain,
% 3.57/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.57/0.99      | ~ m1_pre_topc(X3,X1)
% 3.57/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.57/0.99      | ~ v1_funct_1(X0)
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | v2_struct_0(X2)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ l1_pre_topc(X2)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X2)
% 3.57/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.57/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_43,negated_conjecture,
% 3.57/0.99      ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
% 3.57/0.99      inference(cnf_transformation,[],[f121]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_786,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.57/0.99      | ~ v1_funct_1(X2)
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | v2_struct_0(X3)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ l1_pre_topc(X3)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X3)
% 3.57/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 3.57/0.99      | u1_struct_0(X3) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK7)
% 3.57/0.99      | sK8 != X2 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_43]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_787,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.57/0.99      | ~ v1_funct_1(sK8)
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | v2_struct_0(X2)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ l1_pre_topc(X2)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X2)
% 3.57/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
% 3.57/0.99      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_786]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_44,negated_conjecture,
% 3.57/0.99      ( v1_funct_1(sK8) ),
% 3.57/0.99      inference(cnf_transformation,[],[f120]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_791,plain,
% 3.57/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.57/0.99      | ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | v2_struct_0(X2)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ l1_pre_topc(X2)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X2)
% 3.57/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
% 3.57/0.99      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_787,c_44]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_792,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | v2_struct_0(X2)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ l1_pre_topc(X2)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X2)
% 3.57/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
% 3.57/0.99      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_791]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3047,plain,
% 3.57/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK8,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK8,X2)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.57/0.99      | m1_pre_topc(X2,X0) != iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.57/0.99      | v2_struct_0(X0) = iProver_top
% 3.57/0.99      | v2_struct_0(X1) = iProver_top
% 3.57/0.99      | l1_pre_topc(X0) != iProver_top
% 3.57/0.99      | l1_pre_topc(X1) != iProver_top
% 3.57/0.99      | v2_pre_topc(X0) != iProver_top
% 3.57/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4081,plain,
% 3.57/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
% 3.57/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.57/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.57/0.99      | v2_struct_0(X0) = iProver_top
% 3.57/0.99      | v2_struct_0(sK5) = iProver_top
% 3.57/0.99      | l1_pre_topc(X0) != iProver_top
% 3.57/0.99      | l1_pre_topc(sK5) != iProver_top
% 3.57/0.99      | v2_pre_topc(X0) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK5) != iProver_top ),
% 3.57/0.99      inference(equality_resolution,[status(thm)],[c_3047]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_51,negated_conjecture,
% 3.57/0.99      ( ~ v2_struct_0(sK5) ),
% 3.57/0.99      inference(cnf_transformation,[],[f113]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_58,plain,
% 3.57/0.99      ( v2_struct_0(sK5) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_50,negated_conjecture,
% 3.57/0.99      ( v2_pre_topc(sK5) ),
% 3.57/0.99      inference(cnf_transformation,[],[f114]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_59,plain,
% 3.57/0.99      ( v2_pre_topc(sK5) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_49,negated_conjecture,
% 3.57/0.99      ( l1_pre_topc(sK5) ),
% 3.57/0.99      inference(cnf_transformation,[],[f115]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_60,plain,
% 3.57/0.99      ( l1_pre_topc(sK5) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4437,plain,
% 3.57/0.99      ( v2_pre_topc(X0) != iProver_top
% 3.57/0.99      | v2_struct_0(X0) = iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.57/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.57/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.57/0.99      | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
% 3.57/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_4081,c_58,c_59,c_60]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4438,plain,
% 3.57/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
% 3.57/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.57/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.57/0.99      | v2_struct_0(X0) = iProver_top
% 3.57/0.99      | l1_pre_topc(X0) != iProver_top
% 3.57/0.99      | v2_pre_topc(X0) != iProver_top ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_4437]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4448,plain,
% 3.57/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
% 3.57/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
% 3.57/0.99      | v2_struct_0(sK7) = iProver_top
% 3.57/0.99      | l1_pre_topc(sK7) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(equality_resolution,[status(thm)],[c_4438]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_46,negated_conjecture,
% 3.57/0.99      ( ~ v2_struct_0(sK7) ),
% 3.57/0.99      inference(cnf_transformation,[],[f118]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_63,plain,
% 3.57/0.99      ( v2_struct_0(sK7) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_64,plain,
% 3.57/0.99      ( m1_pre_topc(sK7,sK4) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_42,negated_conjecture,
% 3.57/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
% 3.57/0.99      inference(cnf_transformation,[],[f122]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_67,plain,
% 3.57/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3792,plain,
% 3.57/0.99      ( ~ m1_pre_topc(sK7,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK7) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4326,plain,
% 3.57/0.99      ( ~ m1_pre_topc(sK7,sK4) | ~ l1_pre_topc(sK4) | l1_pre_topc(sK7) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_3792]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4327,plain,
% 3.57/0.99      ( m1_pre_topc(sK7,sK4) != iProver_top
% 3.57/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.57/0.99      | l1_pre_topc(sK7) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_4326]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4581,plain,
% 3.57/0.99      ( m1_pre_topc(X0,sK7) != iProver_top
% 3.57/0.99      | k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
% 3.57/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_4448,c_57,c_63,c_64,c_67,c_4327]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4582,plain,
% 3.57/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
% 3.57/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_4581]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5298,plain,
% 3.57/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k2_tmap_1(sK7,sK5,sK8,sK6)
% 3.57/0.99      | l1_pre_topc(sK6) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_5136,c_4582]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6005,plain,
% 3.57/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k2_tmap_1(sK7,sK5,sK8,sK6)
% 3.57/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_5999,c_5298]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_26,plain,
% 3.57/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.57/0.99      | ~ m1_pre_topc(X3,X4)
% 3.57/0.99      | ~ m1_pre_topc(X3,X1)
% 3.57/0.99      | ~ m1_pre_topc(X1,X4)
% 3.57/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.57/0.99      | ~ v1_funct_1(X0)
% 3.57/0.99      | v2_struct_0(X4)
% 3.57/0.99      | v2_struct_0(X2)
% 3.57/0.99      | ~ l1_pre_topc(X4)
% 3.57/0.99      | ~ l1_pre_topc(X2)
% 3.57/0.99      | ~ v2_pre_topc(X4)
% 3.57/0.99      | ~ v2_pre_topc(X2)
% 3.57/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_735,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ m1_pre_topc(X0,X2)
% 3.57/0.99      | ~ m1_pre_topc(X1,X2)
% 3.57/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 3.57/0.99      | ~ v1_funct_1(X3)
% 3.57/0.99      | v2_struct_0(X4)
% 3.57/0.99      | v2_struct_0(X2)
% 3.57/0.99      | ~ l1_pre_topc(X4)
% 3.57/0.99      | ~ l1_pre_topc(X2)
% 3.57/0.99      | ~ v2_pre_topc(X4)
% 3.57/0.99      | ~ v2_pre_topc(X2)
% 3.57/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 3.57/0.99      | u1_struct_0(X4) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK7)
% 3.57/0.99      | sK8 != X3 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_43]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_736,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ m1_pre_topc(X0,X2)
% 3.57/0.99      | ~ m1_pre_topc(X1,X2)
% 3.57/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.57/0.99      | ~ v1_funct_1(sK8)
% 3.57/0.99      | v2_struct_0(X2)
% 3.57/0.99      | v2_struct_0(X3)
% 3.57/0.99      | ~ l1_pre_topc(X2)
% 3.57/0.99      | ~ l1_pre_topc(X3)
% 3.57/0.99      | ~ v2_pre_topc(X2)
% 3.57/0.99      | ~ v2_pre_topc(X3)
% 3.57/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
% 3.57/0.99      | u1_struct_0(X3) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_735]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_740,plain,
% 3.57/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.57/0.99      | ~ m1_pre_topc(X1,X2)
% 3.57/0.99      | ~ m1_pre_topc(X0,X2)
% 3.57/0.99      | ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | v2_struct_0(X2)
% 3.57/0.99      | v2_struct_0(X3)
% 3.57/0.99      | ~ l1_pre_topc(X2)
% 3.57/0.99      | ~ l1_pre_topc(X3)
% 3.57/0.99      | ~ v2_pre_topc(X2)
% 3.57/0.99      | ~ v2_pre_topc(X3)
% 3.57/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
% 3.57/0.99      | u1_struct_0(X3) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_736,c_44]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_741,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ m1_pre_topc(X0,X2)
% 3.57/0.99      | ~ m1_pre_topc(X1,X2)
% 3.57/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.57/0.99      | v2_struct_0(X2)
% 3.57/0.99      | v2_struct_0(X3)
% 3.57/0.99      | ~ l1_pre_topc(X2)
% 3.57/0.99      | ~ l1_pre_topc(X3)
% 3.57/0.99      | ~ v2_pre_topc(X2)
% 3.57/0.99      | ~ v2_pre_topc(X3)
% 3.57/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
% 3.57/0.99      | u1_struct_0(X3) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_740]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_35,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ m1_pre_topc(X2,X0)
% 3.57/0.99      | m1_pre_topc(X2,X1)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_772,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ m1_pre_topc(X1,X2)
% 3.57/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.57/0.99      | v2_struct_0(X2)
% 3.57/0.99      | v2_struct_0(X3)
% 3.57/0.99      | ~ l1_pre_topc(X2)
% 3.57/0.99      | ~ l1_pre_topc(X3)
% 3.57/0.99      | ~ v2_pre_topc(X2)
% 3.57/0.99      | ~ v2_pre_topc(X3)
% 3.57/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
% 3.57/0.99      | u1_struct_0(X3) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.57/0.99      inference(forward_subsumption_resolution,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_741,c_35]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3048,plain,
% 3.57/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK8,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK8)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.57/0.99      | m1_pre_topc(X2,X0) != iProver_top
% 3.57/0.99      | m1_pre_topc(X0,X3) != iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.57/0.99      | v2_struct_0(X3) = iProver_top
% 3.57/0.99      | v2_struct_0(X1) = iProver_top
% 3.57/0.99      | l1_pre_topc(X3) != iProver_top
% 3.57/0.99      | l1_pre_topc(X1) != iProver_top
% 3.57/0.99      | v2_pre_topc(X3) != iProver_top
% 3.57/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4225,plain,
% 3.57/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
% 3.57/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.57/0.99      | m1_pre_topc(X0,X2) != iProver_top
% 3.57/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.57/0.99      | v2_struct_0(X2) = iProver_top
% 3.57/0.99      | v2_struct_0(sK5) = iProver_top
% 3.57/0.99      | l1_pre_topc(X2) != iProver_top
% 3.57/0.99      | l1_pre_topc(sK5) != iProver_top
% 3.57/0.99      | v2_pre_topc(X2) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK5) != iProver_top ),
% 3.57/0.99      inference(equality_resolution,[status(thm)],[c_3048]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4684,plain,
% 3.57/0.99      ( v2_pre_topc(X2) != iProver_top
% 3.57/0.99      | v2_struct_0(X2) = iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.57/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.57/0.99      | m1_pre_topc(X0,X2) != iProver_top
% 3.57/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.57/0.99      | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
% 3.57/0.99      | l1_pre_topc(X2) != iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_4225,c_58,c_59,c_60]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4685,plain,
% 3.57/0.99      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
% 3.57/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.57/0.99      | m1_pre_topc(X0,X2) != iProver_top
% 3.57/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.57/0.99      | v2_struct_0(X2) = iProver_top
% 3.57/0.99      | l1_pre_topc(X2) != iProver_top
% 3.57/0.99      | v2_pre_topc(X2) != iProver_top ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_4684]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4696,plain,
% 3.57/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
% 3.57/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.57/0.99      | m1_pre_topc(sK7,X1) != iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
% 3.57/0.99      | v2_struct_0(X1) = iProver_top
% 3.57/0.99      | l1_pre_topc(X1) != iProver_top
% 3.57/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.57/0.99      inference(equality_resolution,[status(thm)],[c_4685]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5364,plain,
% 3.57/0.99      ( m1_pre_topc(sK7,X1) != iProver_top
% 3.57/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.57/0.99      | k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
% 3.57/0.99      | v2_struct_0(X1) = iProver_top
% 3.57/0.99      | l1_pre_topc(X1) != iProver_top
% 3.57/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_4696,c_67]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5365,plain,
% 3.57/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
% 3.57/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.57/0.99      | m1_pre_topc(sK7,X1) != iProver_top
% 3.57/0.99      | v2_struct_0(X1) = iProver_top
% 3.57/0.99      | l1_pre_topc(X1) != iProver_top
% 3.57/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_5364]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5377,plain,
% 3.57/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(X0,sK5,sK7,sK6,sK8)
% 3.57/0.99      | m1_pre_topc(sK7,X0) != iProver_top
% 3.57/0.99      | v2_struct_0(X0) = iProver_top
% 3.57/0.99      | l1_pre_topc(X0) != iProver_top
% 3.57/0.99      | l1_pre_topc(sK6) != iProver_top
% 3.57/0.99      | v2_pre_topc(X0) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_5136,c_5365]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_5417,plain,
% 3.57/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8)
% 3.57/0.99      | v2_struct_0(sK4) = iProver_top
% 3.57/0.99      | l1_pre_topc(sK4) != iProver_top
% 3.57/0.99      | l1_pre_topc(sK6) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK4) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3059,c_5377]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_54,negated_conjecture,
% 3.57/0.99      ( ~ v2_struct_0(sK4) ),
% 3.57/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_55,plain,
% 3.57/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6130,plain,
% 3.57/0.99      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8) ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_5417,c_55,c_56,c_57,c_5565]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6378,plain,
% 3.57/0.99      ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k2_tmap_1(sK7,sK5,sK8,sK6)
% 3.57/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_6005,c_6130]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6948,plain,
% 3.57/0.99      ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k2_tmap_1(sK7,sK5,sK8,sK6) ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_6943,c_6378]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_37,negated_conjecture,
% 3.57/0.99      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
% 3.57/0.99      inference(cnf_transformation,[],[f127]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3063,plain,
% 3.57/0.99      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_38,negated_conjecture,
% 3.57/0.99      ( sK9 = sK10 ),
% 3.57/0.99      inference(cnf_transformation,[],[f126]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3132,plain,
% 3.57/0.99      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) = iProver_top ),
% 3.57/0.99      inference(light_normalisation,[status(thm)],[c_3063,c_38]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7210,plain,
% 3.57/0.99      ( r1_tmap_1(sK6,sK5,k2_tmap_1(sK7,sK5,sK8,sK6),sK9) = iProver_top ),
% 3.57/0.99      inference(demodulation,[status(thm)],[c_6948,c_3132]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_18,plain,
% 3.57/0.99      ( v3_pre_topc(X0,X1)
% 3.57/0.99      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.57/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.99      | ~ l1_pre_topc(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_28,plain,
% 3.57/0.99      ( v1_tsep_1(X0,X1)
% 3.57/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.57/0.99      | ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f132]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_30,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.99      | ~ l1_pre_topc(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_291,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.57/0.99      | v1_tsep_1(X0,X1)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X1) ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_28,c_30]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_292,plain,
% 3.57/0.99      ( v1_tsep_1(X0,X1)
% 3.57/0.99      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.57/0.99      | ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X1) ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_291]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_558,plain,
% 3.57/0.99      ( v1_tsep_1(X0,X1)
% 3.57/0.99      | ~ r2_hidden(X2,u1_pre_topc(X3))
% 3.57/0.99      | ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.57/0.99      | ~ l1_pre_topc(X3)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | X1 != X3
% 3.57/0.99      | u1_struct_0(X0) != X2 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_292]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_559,plain,
% 3.57/0.99      ( v1_tsep_1(X0,X1)
% 3.57/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 3.57/0.99      | ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X1) ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_558]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_563,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 3.57/0.99      | v1_tsep_1(X0,X1)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X1) ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_559,c_30]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_564,plain,
% 3.57/0.99      ( v1_tsep_1(X0,X1)
% 3.57/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 3.57/0.99      | ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X1) ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_563]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_33,plain,
% 3.57/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.57/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.57/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.57/0.99      | ~ v1_tsep_1(X4,X0)
% 3.57/0.99      | ~ m1_pre_topc(X4,X0)
% 3.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.57/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.57/0.99      | ~ v1_funct_1(X2)
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | v2_struct_0(X0)
% 3.57/0.99      | v2_struct_0(X4)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ l1_pre_topc(X0)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f134]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_679,plain,
% 3.57/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.57/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.57/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.57/0.99      | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X6))
% 3.57/0.99      | ~ m1_pre_topc(X5,X6)
% 3.57/0.99      | ~ m1_pre_topc(X4,X0)
% 3.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.57/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.57/0.99      | ~ v1_funct_1(X2)
% 3.57/0.99      | v2_struct_0(X4)
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | v2_struct_0(X0)
% 3.57/0.99      | ~ l1_pre_topc(X6)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ l1_pre_topc(X0)
% 3.57/0.99      | ~ v2_pre_topc(X6)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X0)
% 3.57/0.99      | X4 != X5
% 3.57/0.99      | X0 != X6 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_564,c_33]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_680,plain,
% 3.57/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.57/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.57/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.57/0.99      | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X0))
% 3.57/0.99      | ~ m1_pre_topc(X4,X0)
% 3.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.57/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.57/0.99      | ~ v1_funct_1(X2)
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | v2_struct_0(X4)
% 3.57/0.99      | v2_struct_0(X0)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ l1_pre_topc(X0)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X0) ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_679]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_21,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.57/0.99      | m1_subset_1(X2,u1_struct_0(X1))
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | v2_struct_0(X0)
% 3.57/0.99      | ~ l1_pre_topc(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_716,plain,
% 3.57/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.57/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.57/0.99      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.57/0.99      | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X0))
% 3.57/0.99      | ~ m1_pre_topc(X4,X0)
% 3.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.57/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.57/0.99      | ~ v1_funct_1(X2)
% 3.57/0.99      | v2_struct_0(X0)
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | v2_struct_0(X4)
% 3.57/0.99      | ~ l1_pre_topc(X0)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X0)
% 3.57/0.99      | ~ v2_pre_topc(X1) ),
% 3.57/0.99      inference(forward_subsumption_resolution,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_680,c_21]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_831,plain,
% 3.57/0.99      ( r1_tmap_1(X0,X1,X2,X3)
% 3.57/0.99      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.57/0.99      | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X0))
% 3.57/0.99      | ~ m1_pre_topc(X4,X0)
% 3.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.57/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.57/0.99      | ~ v1_funct_1(X2)
% 3.57/0.99      | v2_struct_0(X0)
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | v2_struct_0(X4)
% 3.57/0.99      | ~ l1_pre_topc(X0)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X0)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.57/0.99      | sK8 != X2 ),
% 3.57/0.99      inference(resolution_lifted,[status(thm)],[c_716,c_43]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_832,plain,
% 3.57/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
% 3.57/0.99      | r1_tmap_1(X2,X1,sK8,X3)
% 3.57/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
% 3.57/0.99      | ~ m1_pre_topc(X0,X2)
% 3.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.57/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.57/0.99      | ~ v1_funct_1(sK8)
% 3.57/0.99      | v2_struct_0(X2)
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | v2_struct_0(X0)
% 3.57/0.99      | ~ l1_pre_topc(X2)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X2)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X2) != u1_struct_0(sK7) ),
% 3.57/0.99      inference(unflattening,[status(thm)],[c_831]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_836,plain,
% 3.57/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.57/0.99      | ~ m1_pre_topc(X0,X2)
% 3.57/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
% 3.57/0.99      | r1_tmap_1(X2,X1,sK8,X3)
% 3.57/0.99      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
% 3.57/0.99      | v2_struct_0(X2)
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | v2_struct_0(X0)
% 3.57/0.99      | ~ l1_pre_topc(X2)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X2)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X2) != u1_struct_0(sK7) ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_832,c_44]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_837,plain,
% 3.57/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
% 3.57/0.99      | r1_tmap_1(X2,X1,sK8,X3)
% 3.57/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
% 3.57/0.99      | ~ m1_pre_topc(X0,X2)
% 3.57/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.57/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.57/0.99      | v2_struct_0(X0)
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | v2_struct_0(X2)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ l1_pre_topc(X2)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(X2)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X2) != u1_struct_0(sK7) ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_836]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3046,plain,
% 3.57/0.99      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK7)
% 3.57/0.99      | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK8,X2),X3) != iProver_top
% 3.57/0.99      | r1_tmap_1(X1,X0,sK8,X3) = iProver_top
% 3.57/0.99      | r2_hidden(u1_struct_0(X2),u1_pre_topc(X1)) != iProver_top
% 3.57/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 3.57/0.99      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 3.57/0.99      | v2_struct_0(X0) = iProver_top
% 3.57/0.99      | v2_struct_0(X2) = iProver_top
% 3.57/0.99      | v2_struct_0(X1) = iProver_top
% 3.57/0.99      | l1_pre_topc(X0) != iProver_top
% 3.57/0.99      | l1_pre_topc(X1) != iProver_top
% 3.57/0.99      | v2_pre_topc(X0) != iProver_top
% 3.57/0.99      | v2_pre_topc(X1) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_837]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4208,plain,
% 3.57/0.99      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.57/0.99      | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
% 3.57/0.99      | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
% 3.57/0.99      | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
% 3.57/0.99      | m1_pre_topc(X1,sK7) != iProver_top
% 3.57/0.99      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
% 3.57/0.99      | v2_struct_0(X1) = iProver_top
% 3.57/0.99      | v2_struct_0(X0) = iProver_top
% 3.57/0.99      | v2_struct_0(sK7) = iProver_top
% 3.57/0.99      | l1_pre_topc(X0) != iProver_top
% 3.57/0.99      | l1_pre_topc(sK7) != iProver_top
% 3.57/0.99      | v2_pre_topc(X0) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(equality_resolution,[status(thm)],[c_3046]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_2287,plain,( X0 = X0 ),theory(equality) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3493,plain,
% 3.57/0.99      ( u1_struct_0(sK7) = u1_struct_0(sK7) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_2287]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3749,plain,
% 3.57/0.99      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK7,X1,sK8,X0),X2)
% 3.57/0.99      | r1_tmap_1(sK7,X1,sK8,X2)
% 3.57/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7))
% 3.57/0.99      | ~ m1_pre_topc(X0,sK7)
% 3.57/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.57/0.99      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1))))
% 3.57/0.99      | v2_struct_0(X0)
% 3.57/0.99      | v2_struct_0(X1)
% 3.57/0.99      | v2_struct_0(sK7)
% 3.57/0.99      | ~ l1_pre_topc(X1)
% 3.57/0.99      | ~ l1_pre_topc(sK7)
% 3.57/0.99      | ~ v2_pre_topc(X1)
% 3.57/0.99      | ~ v2_pre_topc(sK7)
% 3.57/0.99      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(sK7) != u1_struct_0(sK7) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_837]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3750,plain,
% 3.57/0.99      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.57/0.99      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 3.57/0.99      | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
% 3.57/0.99      | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
% 3.57/0.99      | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
% 3.57/0.99      | m1_pre_topc(X1,sK7) != iProver_top
% 3.57/0.99      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
% 3.57/0.99      | v2_struct_0(X0) = iProver_top
% 3.57/0.99      | v2_struct_0(X1) = iProver_top
% 3.57/0.99      | v2_struct_0(sK7) = iProver_top
% 3.57/0.99      | l1_pre_topc(X0) != iProver_top
% 3.57/0.99      | l1_pre_topc(sK7) != iProver_top
% 3.57/0.99      | v2_pre_topc(X0) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_3749]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4558,plain,
% 3.57/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.57/0.99      | u1_struct_0(X0) != u1_struct_0(sK5)
% 3.57/0.99      | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
% 3.57/0.99      | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
% 3.57/0.99      | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
% 3.57/0.99      | m1_pre_topc(X1,sK7) != iProver_top
% 3.57/0.99      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
% 3.57/0.99      | v2_struct_0(X1) = iProver_top
% 3.57/0.99      | v2_struct_0(X0) = iProver_top
% 3.57/0.99      | v2_pre_topc(X0) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_4208,c_57,c_63,c_64,c_3493,c_3750,c_4327]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4559,plain,
% 3.57/0.99      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.57/0.99      | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
% 3.57/0.99      | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
% 3.57/0.99      | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
% 3.57/0.99      | m1_pre_topc(X1,sK7) != iProver_top
% 3.57/0.99      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
% 3.57/0.99      | v2_struct_0(X1) = iProver_top
% 3.57/0.99      | v2_struct_0(X0) = iProver_top
% 3.57/0.99      | l1_pre_topc(X0) != iProver_top
% 3.57/0.99      | v2_pre_topc(X0) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_4558]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4576,plain,
% 3.57/0.99      ( r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
% 3.57/0.99      | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
% 3.57/0.99      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 3.57/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.57/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.57/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
% 3.57/0.99      | v2_struct_0(X0) = iProver_top
% 3.57/0.99      | v2_struct_0(sK5) = iProver_top
% 3.57/0.99      | l1_pre_topc(sK5) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK5) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(equality_resolution,[status(thm)],[c_4559]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4835,plain,
% 3.57/0.99      ( v2_struct_0(X0) = iProver_top
% 3.57/0.99      | r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
% 3.57/0.99      | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
% 3.57/0.99      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 3.57/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.57/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_4576,c_58,c_59,c_60,c_67]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_4836,plain,
% 3.57/0.99      ( r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
% 3.57/0.99      | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
% 3.57/0.99      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 3.57/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.57/0.99      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.57/0.99      | v2_struct_0(X0) = iProver_top
% 3.57/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_4835]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_7218,plain,
% 3.57/0.99      ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
% 3.57/0.99      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
% 3.57/0.99      | m1_pre_topc(sK6,sK7) != iProver_top
% 3.57/0.99      | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
% 3.57/0.99      | v2_struct_0(sK6) = iProver_top
% 3.57/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_7210,c_4836]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_48,negated_conjecture,
% 3.57/0.99      ( ~ v2_struct_0(sK6) ),
% 3.57/0.99      inference(cnf_transformation,[],[f116]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_61,plain,
% 3.57/0.99      ( v2_struct_0(sK6) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_36,negated_conjecture,
% 3.57/0.99      ( ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
% 3.57/0.99      inference(cnf_transformation,[],[f128]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_71,plain,
% 3.57/0.99      ( r1_tmap_1(sK7,sK5,sK8,sK9) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_39,negated_conjecture,
% 3.57/0.99      ( m1_subset_1(sK10,u1_struct_0(sK6)) ),
% 3.57/0.99      inference(cnf_transformation,[],[f125]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3062,plain,
% 3.57/0.99      ( m1_subset_1(sK10,u1_struct_0(sK6)) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3116,plain,
% 3.57/0.99      ( m1_subset_1(sK9,u1_struct_0(sK6)) = iProver_top ),
% 3.57/0.99      inference(light_normalisation,[status(thm)],[c_3062,c_38]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10602,plain,
% 3.57/0.99      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_7218,c_56,c_57,c_61,c_71,c_3116,c_5136,c_5565,c_6654]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_22,plain,
% 3.57/0.99      ( m1_pre_topc(X0,X1)
% 3.57/0.99      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.57/0.99      | ~ l1_pre_topc(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3069,plain,
% 3.57/0.99      ( m1_pre_topc(X0,X1) = iProver_top
% 3.57/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.57/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6517,plain,
% 3.57/0.99      ( m1_pre_topc(X0,sK6) = iProver_top
% 3.57/0.99      | m1_pre_topc(X0,sK7) != iProver_top
% 3.57/0.99      | l1_pre_topc(sK6) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_41,c_3069]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6630,plain,
% 3.57/0.99      ( m1_pre_topc(X0,sK7) != iProver_top
% 3.57/0.99      | m1_pre_topc(X0,sK6) = iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_6517,c_57,c_5565]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6631,plain,
% 3.57/0.99      ( m1_pre_topc(X0,sK6) = iProver_top
% 3.57/0.99      | m1_pre_topc(X0,sK7) != iProver_top ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_6630]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6638,plain,
% 3.57/0.99      ( m1_pre_topc(sK7,sK6) = iProver_top
% 3.57/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3067,c_6631]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6768,plain,
% 3.57/0.99      ( m1_pre_topc(sK7,sK6) = iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_6638,c_57,c_64,c_4327]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_32,plain,
% 3.57/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.57/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.57/0.99      | ~ l1_pre_topc(X1) ),
% 3.57/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3066,plain,
% 3.57/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.57/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.57/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_0,plain,
% 3.57/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.57/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_3087,plain,
% 3.57/0.99      ( X0 = X1
% 3.57/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.57/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_6386,plain,
% 3.57/0.99      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.57/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.57/0.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.57/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3066,c_3087]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_8361,plain,
% 3.57/0.99      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.57/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.57/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 3.57/0.99      | l1_pre_topc(X0) != iProver_top
% 3.57/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_3066,c_6386]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_107,plain,
% 3.57/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.57/0.99      | l1_pre_topc(X1) != iProver_top
% 3.57/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_8992,plain,
% 3.57/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.57/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.57/0.99      | u1_struct_0(X0) = u1_struct_0(X1)
% 3.57/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_8361,c_107]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_8993,plain,
% 3.57/0.99      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.57/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 3.57/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.57/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.57/0.99      inference(renaming,[status(thm)],[c_8992]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_9008,plain,
% 3.57/0.99      ( u1_struct_0(sK7) = u1_struct_0(sK6)
% 3.57/0.99      | m1_pre_topc(sK6,sK7) != iProver_top
% 3.57/0.99      | l1_pre_topc(sK6) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_6768,c_8993]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_9005,plain,
% 3.57/0.99      ( u1_struct_0(sK7) = u1_struct_0(sK6)
% 3.57/0.99      | m1_pre_topc(sK7,sK6) != iProver_top
% 3.57/0.99      | l1_pre_topc(sK6) != iProver_top
% 3.57/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(superposition,[status(thm)],[c_5136,c_8993]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_9291,plain,
% 3.57/0.99      ( u1_struct_0(sK7) = u1_struct_0(sK6) ),
% 3.57/0.99      inference(global_propositional_subsumption,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_9008,c_57,c_64,c_4327,c_5565,c_6638,c_9005]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_10606,plain,
% 3.57/0.99      ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top ),
% 3.57/0.99      inference(light_normalisation,[status(thm)],[c_10602,c_9291]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_17,plain,
% 3.57/0.99      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 3.57/0.99      | ~ l1_pre_topc(X0)
% 3.57/0.99      | ~ v2_pre_topc(X0) ),
% 3.57/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_8786,plain,
% 3.57/0.99      ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.57/0.99      | ~ l1_pre_topc(sK7)
% 3.57/0.99      | ~ v2_pre_topc(sK7) ),
% 3.57/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(c_8787,plain,
% 3.57/0.99      ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) = iProver_top
% 3.57/0.99      | l1_pre_topc(sK7) != iProver_top
% 3.57/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.57/0.99      inference(predicate_to_equality,[status(thm)],[c_8786]) ).
% 3.57/0.99  
% 3.57/0.99  cnf(contradiction,plain,
% 3.57/0.99      ( $false ),
% 3.57/0.99      inference(minisat,
% 3.57/0.99                [status(thm)],
% 3.57/0.99                [c_10606,c_8787,c_6654,c_4327,c_64,c_57,c_56]) ).
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.57/0.99  
% 3.57/0.99  ------                               Statistics
% 3.57/0.99  
% 3.57/0.99  ------ General
% 3.57/0.99  
% 3.57/0.99  abstr_ref_over_cycles:                  0
% 3.57/0.99  abstr_ref_under_cycles:                 0
% 3.57/0.99  gc_basic_clause_elim:                   0
% 3.57/0.99  forced_gc_time:                         0
% 3.57/0.99  parsing_time:                           0.013
% 3.57/0.99  unif_index_cands_time:                  0.
% 3.57/0.99  unif_index_add_time:                    0.
% 3.57/0.99  orderings_time:                         0.
% 3.57/0.99  out_proof_time:                         0.019
% 3.57/0.99  total_time:                             0.307
% 3.57/0.99  num_of_symbols:                         65
% 3.57/0.99  num_of_terms:                           6345
% 3.57/0.99  
% 3.57/0.99  ------ Preprocessing
% 3.57/0.99  
% 3.57/0.99  num_of_splits:                          0
% 3.57/0.99  num_of_split_atoms:                     0
% 3.57/0.99  num_of_reused_defs:                     0
% 3.57/0.99  num_eq_ax_congr_red:                    29
% 3.57/0.99  num_of_sem_filtered_clauses:            1
% 3.57/0.99  num_of_subtypes:                        0
% 3.57/0.99  monotx_restored_types:                  0
% 3.57/0.99  sat_num_of_epr_types:                   0
% 3.57/0.99  sat_num_of_non_cyclic_types:            0
% 3.57/0.99  sat_guarded_non_collapsed_types:        0
% 3.57/0.99  num_pure_diseq_elim:                    0
% 3.57/0.99  simp_replaced_by:                       0
% 3.57/0.99  res_preprocessed:                       231
% 3.57/0.99  prep_upred:                             0
% 3.57/0.99  prep_unflattend:                        24
% 3.57/0.99  smt_new_axioms:                         0
% 3.57/0.99  pred_elim_cands:                        9
% 3.57/0.99  pred_elim:                              4
% 3.57/0.99  pred_elim_cl:                           6
% 3.57/0.99  pred_elim_cycles:                       6
% 3.57/0.99  merged_defs:                            0
% 3.57/0.99  merged_defs_ncl:                        0
% 3.57/0.99  bin_hyper_res:                          0
% 3.57/0.99  prep_cycles:                            4
% 3.57/0.99  pred_elim_time:                         0.033
% 3.57/0.99  splitting_time:                         0.
% 3.57/0.99  sem_filter_time:                        0.
% 3.57/0.99  monotx_time:                            0.001
% 3.57/0.99  subtype_inf_time:                       0.
% 3.57/0.99  
% 3.57/0.99  ------ Problem properties
% 3.57/0.99  
% 3.57/0.99  clauses:                                46
% 3.57/0.99  conjectures:                            17
% 3.57/0.99  epr:                                    19
% 3.57/0.99  horn:                                   35
% 3.57/0.99  ground:                                 17
% 3.57/0.99  unary:                                  20
% 3.57/0.99  binary:                                 6
% 3.57/0.99  lits:                                   150
% 3.57/0.99  lits_eq:                                14
% 3.57/0.99  fd_pure:                                0
% 3.57/0.99  fd_pseudo:                              0
% 3.57/0.99  fd_cond:                                0
% 3.57/0.99  fd_pseudo_cond:                         1
% 3.57/0.99  ac_symbols:                             0
% 3.57/0.99  
% 3.57/0.99  ------ Propositional Solver
% 3.57/0.99  
% 3.57/0.99  prop_solver_calls:                      28
% 3.57/0.99  prop_fast_solver_calls:                 2508
% 3.57/0.99  smt_solver_calls:                       0
% 3.57/0.99  smt_fast_solver_calls:                  0
% 3.57/0.99  prop_num_of_clauses:                    3306
% 3.57/0.99  prop_preprocess_simplified:             9606
% 3.57/0.99  prop_fo_subsumed:                       101
% 3.57/0.99  prop_solver_time:                       0.
% 3.57/0.99  smt_solver_time:                        0.
% 3.57/0.99  smt_fast_solver_time:                   0.
% 3.57/0.99  prop_fast_solver_time:                  0.
% 3.57/0.99  prop_unsat_core_time:                   0.
% 3.57/0.99  
% 3.57/0.99  ------ QBF
% 3.57/0.99  
% 3.57/0.99  qbf_q_res:                              0
% 3.57/0.99  qbf_num_tautologies:                    0
% 3.57/0.99  qbf_prep_cycles:                        0
% 3.57/0.99  
% 3.57/0.99  ------ BMC1
% 3.57/0.99  
% 3.57/0.99  bmc1_current_bound:                     -1
% 3.57/0.99  bmc1_last_solved_bound:                 -1
% 3.57/0.99  bmc1_unsat_core_size:                   -1
% 3.57/0.99  bmc1_unsat_core_parents_size:           -1
% 3.57/0.99  bmc1_merge_next_fun:                    0
% 3.57/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.57/0.99  
% 3.57/0.99  ------ Instantiation
% 3.57/0.99  
% 3.57/0.99  inst_num_of_clauses:                    960
% 3.57/0.99  inst_num_in_passive:                    43
% 3.57/0.99  inst_num_in_active:                     521
% 3.57/0.99  inst_num_in_unprocessed:                396
% 3.57/0.99  inst_num_of_loops:                      550
% 3.57/0.99  inst_num_of_learning_restarts:          0
% 3.57/0.99  inst_num_moves_active_passive:          26
% 3.57/0.99  inst_lit_activity:                      0
% 3.57/0.99  inst_lit_activity_moves:                0
% 3.57/0.99  inst_num_tautologies:                   0
% 3.57/0.99  inst_num_prop_implied:                  0
% 3.57/0.99  inst_num_existing_simplified:           0
% 3.57/0.99  inst_num_eq_res_simplified:             0
% 3.57/0.99  inst_num_child_elim:                    0
% 3.57/0.99  inst_num_of_dismatching_blockings:      295
% 3.57/0.99  inst_num_of_non_proper_insts:           1198
% 3.57/0.99  inst_num_of_duplicates:                 0
% 3.57/0.99  inst_inst_num_from_inst_to_res:         0
% 3.57/0.99  inst_dismatching_checking_time:         0.
% 3.57/0.99  
% 3.57/0.99  ------ Resolution
% 3.57/0.99  
% 3.57/0.99  res_num_of_clauses:                     0
% 3.57/0.99  res_num_in_passive:                     0
% 3.57/0.99  res_num_in_active:                      0
% 3.57/0.99  res_num_of_loops:                       235
% 3.57/0.99  res_forward_subset_subsumed:            124
% 3.57/0.99  res_backward_subset_subsumed:           0
% 3.57/0.99  res_forward_subsumed:                   0
% 3.57/0.99  res_backward_subsumed:                  0
% 3.57/0.99  res_forward_subsumption_resolution:     3
% 3.57/0.99  res_backward_subsumption_resolution:    0
% 3.57/0.99  res_clause_to_clause_subsumption:       631
% 3.57/0.99  res_orphan_elimination:                 0
% 3.57/0.99  res_tautology_del:                      145
% 3.57/0.99  res_num_eq_res_simplified:              0
% 3.57/0.99  res_num_sel_changes:                    0
% 3.57/0.99  res_moves_from_active_to_pass:          0
% 3.57/0.99  
% 3.57/0.99  ------ Superposition
% 3.57/0.99  
% 3.57/0.99  sup_time_total:                         0.
% 3.57/0.99  sup_time_generating:                    0.
% 3.57/0.99  sup_time_sim_full:                      0.
% 3.57/0.99  sup_time_sim_immed:                     0.
% 3.57/0.99  
% 3.57/0.99  sup_num_of_clauses:                     138
% 3.57/0.99  sup_num_in_active:                      96
% 3.57/0.99  sup_num_in_passive:                     42
% 3.57/0.99  sup_num_of_loops:                       108
% 3.57/0.99  sup_fw_superposition:                   66
% 3.57/0.99  sup_bw_superposition:                   85
% 3.57/0.99  sup_immediate_simplified:               42
% 3.57/0.99  sup_given_eliminated:                   0
% 3.57/0.99  comparisons_done:                       0
% 3.57/0.99  comparisons_avoided:                    0
% 3.57/0.99  
% 3.57/0.99  ------ Simplifications
% 3.57/0.99  
% 3.57/0.99  
% 3.57/0.99  sim_fw_subset_subsumed:                 17
% 3.57/0.99  sim_bw_subset_subsumed:                 9
% 3.57/0.99  sim_fw_subsumed:                        9
% 3.57/0.99  sim_bw_subsumed:                        0
% 3.57/0.99  sim_fw_subsumption_res:                 0
% 3.57/0.99  sim_bw_subsumption_res:                 0
% 3.57/0.99  sim_tautology_del:                      14
% 3.57/0.99  sim_eq_tautology_del:                   4
% 3.57/0.99  sim_eq_res_simp:                        0
% 3.57/0.99  sim_fw_demodulated:                     3
% 3.57/0.99  sim_bw_demodulated:                     8
% 3.57/0.99  sim_light_normalised:                   24
% 3.57/0.99  sim_joinable_taut:                      0
% 3.57/0.99  sim_joinable_simp:                      0
% 3.57/0.99  sim_ac_normalised:                      0
% 3.57/0.99  sim_smt_subsumption:                    0
% 3.57/0.99  
%------------------------------------------------------------------------------
