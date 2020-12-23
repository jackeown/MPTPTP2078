%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:26 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  261 (2684 expanded)
%              Number of clauses        :  155 ( 673 expanded)
%              Number of leaves         :   28 (1111 expanded)
%              Depth                    :   30
%              Number of atoms          : 1578 (34894 expanded)
%              Number of equality atoms :  470 (5377 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(negated_conjecture,[],[f20])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f74,plain,(
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

fof(f73,plain,(
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

fof(f72,plain,(
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

fof(f71,plain,(
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

fof(f70,plain,(
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

fof(f69,plain,(
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

fof(f68,plain,
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

fof(f75,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f50,f74,f73,f72,f71,f70,f69,f68])).

fof(f122,plain,(
    m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f75])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f109,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f126,plain,(
    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f75])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(cnf_transformation,[],[f30])).

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

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f102,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f124,plain,(
    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f75])).

fof(f123,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f75])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f116,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f75])).

fof(f117,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f75])).

fof(f118,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f75])).

fof(f125,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f75])).

fof(f113,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f75])).

fof(f114,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f75])).

fof(f115,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f75])).

fof(f120,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f75])).

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

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f101,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f121,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f75])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f130,plain,(
    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(cnf_transformation,[],[f75])).

fof(f129,plain,(
    sK9 = sK10 ),
    inference(cnf_transformation,[],[f75])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f15,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f66,plain,(
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
    inference(flattening,[],[f65])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f133,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f106])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f111,plain,(
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
    inference(cnf_transformation,[],[f67])).

fof(f135,plain,(
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
    inference(equality_resolution,[],[f111])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f78,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f22,plain,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f51,plain,(
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

fof(f52,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f28,f51])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f52])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f60,plain,(
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
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f60,f61])).

fof(f86,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f131,plain,(
    ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f75])).

fof(f127,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f75])).

fof(f119,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_46,negated_conjecture,
    ( m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_3279,plain,
    ( m1_pre_topc(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_33,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3286,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_42,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_309,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_18])).

cnf(c_310,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_309])).

cnf(c_3269,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_5240,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | m1_pre_topc(X0,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_42,c_3269])).

cnf(c_5505,plain,
    ( m1_pre_topc(sK6,sK7) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3286,c_5240])).

cnf(c_26,plain,
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
    inference(cnf_transformation,[],[f102])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_816,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ v1_funct_1(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
    | u1_struct_0(X4) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | sK8 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_44])).

cnf(c_817,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_1(sK8)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_816])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_821,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_817,c_45])).

cnf(c_822,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(renaming,[status(thm)],[c_821])).

cnf(c_36,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_853,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_822,c_36])).

cnf(c_3268,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK8,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK8)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_4563,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3268])).

cnf(c_52,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_59,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_51,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_60,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_50,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_61,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_5092,plain,
    ( l1_pre_topc(X2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
    | v2_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4563,c_59,c_60,c_61])).

cnf(c_5093,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_pre_topc(X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5092])).

cnf(c_5104,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_pre_topc(sK7,X1) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5093])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_68,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_5761,plain,
    ( m1_pre_topc(sK7,X1) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5104,c_68])).

cnf(c_5762,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_pre_topc(sK7,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5761])).

cnf(c_5774,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(X0,sK5,sK7,sK6,sK8)
    | m1_pre_topc(sK7,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5505,c_5762])).

cnf(c_5814,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8)
    | v2_struct_0(sK4) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3279,c_5774])).

cnf(c_55,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_54,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_53,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_48,negated_conjecture,
    ( m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_5853,plain,
    ( v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK6)
    | k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5814])).

cnf(c_4406,plain,
    ( ~ m1_pre_topc(sK6,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_5908,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_4406])).

cnf(c_7108,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5814,c_55,c_54,c_53,c_48,c_5853,c_5908])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f101])).

cnf(c_867,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
    | u1_struct_0(X3) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_44])).

cnf(c_868,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(sK8)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_867])).

cnf(c_872,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_868,c_45])).

cnf(c_873,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK7) ),
    inference(renaming,[status(thm)],[c_872])).

cnf(c_3267,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK8,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK8,X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_873])).

cnf(c_4374,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3267])).

cnf(c_4825,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4374,c_59,c_60,c_61])).

cnf(c_4826,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4825])).

cnf(c_4836,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4826])).

cnf(c_47,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_64,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_4956,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
    | m1_pre_topc(X0,sK7) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4836,c_64,c_68])).

cnf(c_5682,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k2_tmap_1(sK7,sK5,sK8,sK6)
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_5505,c_4956])).

cnf(c_7112,plain,
    ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k2_tmap_1(sK7,sK5,sK8,sK6)
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7108,c_5682])).

cnf(c_57,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_58,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_63,plain,
    ( m1_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_65,plain,
    ( m1_pre_topc(sK7,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_5909,plain,
    ( m1_pre_topc(sK6,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5908])).

cnf(c_4430,plain,
    ( ~ m1_pre_topc(sK7,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_5925,plain,
    ( ~ m1_pre_topc(sK7,sK4)
    | ~ l1_pre_topc(sK4)
    | l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_4430])).

cnf(c_5926,plain,
    ( m1_pre_topc(sK7,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5925])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4661,plain,
    ( ~ m1_pre_topc(sK7,X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK7)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6126,plain,
    ( ~ m1_pre_topc(sK7,sK4)
    | ~ v2_pre_topc(sK4)
    | v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_4661])).

cnf(c_6127,plain,
    ( m1_pre_topc(sK7,sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK7) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6126])).

cnf(c_11940,plain,
    ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k2_tmap_1(sK7,sK5,sK8,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7112,c_57,c_58,c_63,c_65,c_5909,c_5926,c_6127])).

cnf(c_38,negated_conjecture,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_3283,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_39,negated_conjecture,
    ( sK9 = sK10 ),
    inference(cnf_transformation,[],[f129])).

cnf(c_3353,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3283,c_39])).

cnf(c_11943,plain,
    ( r1_tmap_1(sK6,sK5,k2_tmap_1(sK7,sK5,sK8,sK6),sK9) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11940,c_3353])).

cnf(c_16,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_30,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_32,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_298,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_32])).

cnf(c_299,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_298])).

cnf(c_639,plain,
    ( v1_tsep_1(X0,X1)
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | u1_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_299])).

cnf(c_640,plain,
    ( v1_tsep_1(X0,X1)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_644,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_640,c_32])).

cnf(c_645,plain,
    ( v1_tsep_1(X0,X1)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_644])).

cnf(c_34,plain,
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
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_760,plain,
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
    | ~ v2_pre_topc(X6)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X6)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | X4 != X5
    | X0 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_645,c_34])).

cnf(c_761,plain,
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
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_760])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_797,plain,
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
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_761,c_22])).

cnf(c_912,plain,
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
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK7)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_797,c_44])).

cnf(c_913,plain,
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
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X2) != u1_struct_0(sK7) ),
    inference(unflattening,[status(thm)],[c_912])).

cnf(c_917,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
    | r1_tmap_1(X2,X1,sK8,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X2) != u1_struct_0(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_913,c_45])).

cnf(c_918,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
    | r1_tmap_1(X2,X1,sK8,X3)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(X2) != u1_struct_0(sK7) ),
    inference(renaming,[status(thm)],[c_917])).

cnf(c_3266,plain,
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
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_918])).

cnf(c_4546,plain,
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
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3266])).

cnf(c_2448,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3745,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2448])).

cnf(c_4023,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK7,X1,sK8,X0),X2)
    | r1_tmap_1(sK7,X1,sK8,X2)
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7))
    | ~ m1_pre_topc(X0,sK7)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK7)
    | u1_struct_0(X1) != u1_struct_0(sK5)
    | u1_struct_0(sK7) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_4024,plain,
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
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4023])).

cnf(c_4932,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X1,sK7) != iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
    | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
    | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4546,c_64,c_3745,c_4024])).

cnf(c_4933,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK5)
    | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
    | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X1,sK7) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_4932])).

cnf(c_4951,plain,
    ( r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4933])).

cnf(c_5166,plain,
    ( v2_pre_topc(sK7) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4951,c_59,c_60,c_61,c_68])).

cnf(c_5167,plain,
    ( r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
    | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_5166])).

cnf(c_11947,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(sK6,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_11943,c_5167])).

cnf(c_3295,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6019,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3279,c_3295])).

cnf(c_6303,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6019,c_58,c_65,c_5926])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3309,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6308,plain,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7
    | v1_pre_topc(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6303,c_3309])).

cnf(c_28,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3288,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7483,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5505,c_3288])).

cnf(c_7487,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v1_pre_topc(sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7483,c_42])).

cnf(c_7737,plain,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6308,c_58,c_63,c_65,c_5909,c_5926,c_7487])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3292,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7607,plain,
    ( g1_pre_topc(X0,X1) != sK7
    | u1_struct_0(sK6) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_42,c_3292])).

cnf(c_19,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_5478,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_5483,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5478])).

cnf(c_7608,plain,
    ( g1_pre_topc(X0,X1) != sK7
    | u1_struct_0(sK6) = X0
    | m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_42,c_3292])).

cnf(c_7629,plain,
    ( u1_struct_0(sK6) = X0
    | g1_pre_topc(X0,X1) != sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7607,c_58,c_63,c_5483,c_5909,c_7608])).

cnf(c_7630,plain,
    ( g1_pre_topc(X0,X1) != sK7
    | u1_struct_0(sK6) = X0 ),
    inference(renaming,[status(thm)],[c_7629])).

cnf(c_7741,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK6) ),
    inference(superposition,[status(thm)],[c_7737,c_7630])).

cnf(c_11948,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
    | r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top
    | m1_pre_topc(sK6,sK7) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(sK6) = iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11947,c_7741])).

cnf(c_7908,plain,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK6)) = sK7 ),
    inference(demodulation,[status(thm)],[c_7741,c_42])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3293,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8470,plain,
    ( g1_pre_topc(X0,X1) != sK7
    | u1_pre_topc(sK6) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7908,c_3293])).

cnf(c_3294,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7921,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7741,c_3294])).

cnf(c_8472,plain,
    ( g1_pre_topc(X0,X1) != sK7
    | u1_pre_topc(sK6) = X1
    | m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7908,c_3293])).

cnf(c_9010,plain,
    ( u1_pre_topc(sK6) = X1
    | g1_pre_topc(X0,X1) != sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8470,c_58,c_63,c_5909,c_7921,c_8472])).

cnf(c_9011,plain,
    ( g1_pre_topc(X0,X1) != sK7
    | u1_pre_topc(sK6) = X1 ),
    inference(renaming,[status(thm)],[c_9010])).

cnf(c_9015,plain,
    ( u1_pre_topc(sK7) = u1_pre_topc(sK6) ),
    inference(superposition,[status(thm)],[c_7737,c_9011])).

cnf(c_15,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3296,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10002,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) = iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9015,c_3296])).

cnf(c_10065,plain,
    ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) = iProver_top
    | v2_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10002,c_7741])).

cnf(c_3277,plain,
    ( m1_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_3308,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8519,plain,
    ( v2_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK6) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3277,c_3308])).

cnf(c_37,negated_conjecture,
    ( ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_72,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_69,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_49,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_62,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11948,c_10065,c_8519,c_6127,c_5926,c_5909,c_5505,c_72,c_69,c_65,c_63,c_62,c_58,c_57])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:34:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.51/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/0.99  
% 3.51/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.51/0.99  
% 3.51/0.99  ------  iProver source info
% 3.51/0.99  
% 3.51/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.51/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.51/0.99  git: non_committed_changes: false
% 3.51/0.99  git: last_make_outside_of_git: false
% 3.51/0.99  
% 3.51/0.99  ------ 
% 3.51/0.99  
% 3.51/0.99  ------ Input Options
% 3.51/0.99  
% 3.51/0.99  --out_options                           all
% 3.51/0.99  --tptp_safe_out                         true
% 3.51/0.99  --problem_path                          ""
% 3.51/0.99  --include_path                          ""
% 3.51/0.99  --clausifier                            res/vclausify_rel
% 3.51/0.99  --clausifier_options                    --mode clausify
% 3.51/0.99  --stdin                                 false
% 3.51/0.99  --stats_out                             all
% 3.51/0.99  
% 3.51/0.99  ------ General Options
% 3.51/0.99  
% 3.51/0.99  --fof                                   false
% 3.51/0.99  --time_out_real                         305.
% 3.51/0.99  --time_out_virtual                      -1.
% 3.51/0.99  --symbol_type_check                     false
% 3.51/0.99  --clausify_out                          false
% 3.51/0.99  --sig_cnt_out                           false
% 3.51/0.99  --trig_cnt_out                          false
% 3.51/0.99  --trig_cnt_out_tolerance                1.
% 3.51/0.99  --trig_cnt_out_sk_spl                   false
% 3.51/0.99  --abstr_cl_out                          false
% 3.51/0.99  
% 3.51/0.99  ------ Global Options
% 3.51/0.99  
% 3.51/0.99  --schedule                              default
% 3.51/0.99  --add_important_lit                     false
% 3.51/0.99  --prop_solver_per_cl                    1000
% 3.51/0.99  --min_unsat_core                        false
% 3.51/0.99  --soft_assumptions                      false
% 3.51/0.99  --soft_lemma_size                       3
% 3.51/0.99  --prop_impl_unit_size                   0
% 3.51/0.99  --prop_impl_unit                        []
% 3.51/0.99  --share_sel_clauses                     true
% 3.51/0.99  --reset_solvers                         false
% 3.51/0.99  --bc_imp_inh                            [conj_cone]
% 3.51/0.99  --conj_cone_tolerance                   3.
% 3.51/0.99  --extra_neg_conj                        none
% 3.51/0.99  --large_theory_mode                     true
% 3.51/0.99  --prolific_symb_bound                   200
% 3.51/0.99  --lt_threshold                          2000
% 3.51/0.99  --clause_weak_htbl                      true
% 3.51/0.99  --gc_record_bc_elim                     false
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing Options
% 3.51/0.99  
% 3.51/0.99  --preprocessing_flag                    true
% 3.51/0.99  --time_out_prep_mult                    0.1
% 3.51/0.99  --splitting_mode                        input
% 3.51/0.99  --splitting_grd                         true
% 3.51/0.99  --splitting_cvd                         false
% 3.51/0.99  --splitting_cvd_svl                     false
% 3.51/0.99  --splitting_nvd                         32
% 3.51/0.99  --sub_typing                            true
% 3.51/0.99  --prep_gs_sim                           true
% 3.51/0.99  --prep_unflatten                        true
% 3.51/0.99  --prep_res_sim                          true
% 3.51/0.99  --prep_upred                            true
% 3.51/0.99  --prep_sem_filter                       exhaustive
% 3.51/0.99  --prep_sem_filter_out                   false
% 3.51/0.99  --pred_elim                             true
% 3.51/0.99  --res_sim_input                         true
% 3.51/0.99  --eq_ax_congr_red                       true
% 3.51/0.99  --pure_diseq_elim                       true
% 3.51/0.99  --brand_transform                       false
% 3.51/0.99  --non_eq_to_eq                          false
% 3.51/0.99  --prep_def_merge                        true
% 3.51/0.99  --prep_def_merge_prop_impl              false
% 3.51/0.99  --prep_def_merge_mbd                    true
% 3.51/0.99  --prep_def_merge_tr_red                 false
% 3.51/0.99  --prep_def_merge_tr_cl                  false
% 3.51/0.99  --smt_preprocessing                     true
% 3.51/0.99  --smt_ac_axioms                         fast
% 3.51/0.99  --preprocessed_out                      false
% 3.51/0.99  --preprocessed_stats                    false
% 3.51/0.99  
% 3.51/0.99  ------ Abstraction refinement Options
% 3.51/0.99  
% 3.51/0.99  --abstr_ref                             []
% 3.51/0.99  --abstr_ref_prep                        false
% 3.51/0.99  --abstr_ref_until_sat                   false
% 3.51/0.99  --abstr_ref_sig_restrict                funpre
% 3.51/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.99  --abstr_ref_under                       []
% 3.51/0.99  
% 3.51/0.99  ------ SAT Options
% 3.51/0.99  
% 3.51/0.99  --sat_mode                              false
% 3.51/0.99  --sat_fm_restart_options                ""
% 3.51/0.99  --sat_gr_def                            false
% 3.51/0.99  --sat_epr_types                         true
% 3.51/0.99  --sat_non_cyclic_types                  false
% 3.51/0.99  --sat_finite_models                     false
% 3.51/0.99  --sat_fm_lemmas                         false
% 3.51/0.99  --sat_fm_prep                           false
% 3.51/0.99  --sat_fm_uc_incr                        true
% 3.51/0.99  --sat_out_model                         small
% 3.51/0.99  --sat_out_clauses                       false
% 3.51/0.99  
% 3.51/0.99  ------ QBF Options
% 3.51/0.99  
% 3.51/0.99  --qbf_mode                              false
% 3.51/0.99  --qbf_elim_univ                         false
% 3.51/0.99  --qbf_dom_inst                          none
% 3.51/0.99  --qbf_dom_pre_inst                      false
% 3.51/0.99  --qbf_sk_in                             false
% 3.51/0.99  --qbf_pred_elim                         true
% 3.51/0.99  --qbf_split                             512
% 3.51/0.99  
% 3.51/0.99  ------ BMC1 Options
% 3.51/0.99  
% 3.51/0.99  --bmc1_incremental                      false
% 3.51/0.99  --bmc1_axioms                           reachable_all
% 3.51/0.99  --bmc1_min_bound                        0
% 3.51/0.99  --bmc1_max_bound                        -1
% 3.51/0.99  --bmc1_max_bound_default                -1
% 3.51/0.99  --bmc1_symbol_reachability              true
% 3.51/0.99  --bmc1_property_lemmas                  false
% 3.51/0.99  --bmc1_k_induction                      false
% 3.51/0.99  --bmc1_non_equiv_states                 false
% 3.51/0.99  --bmc1_deadlock                         false
% 3.51/0.99  --bmc1_ucm                              false
% 3.51/0.99  --bmc1_add_unsat_core                   none
% 3.51/0.99  --bmc1_unsat_core_children              false
% 3.51/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.99  --bmc1_out_stat                         full
% 3.51/0.99  --bmc1_ground_init                      false
% 3.51/0.99  --bmc1_pre_inst_next_state              false
% 3.51/0.99  --bmc1_pre_inst_state                   false
% 3.51/0.99  --bmc1_pre_inst_reach_state             false
% 3.51/0.99  --bmc1_out_unsat_core                   false
% 3.51/0.99  --bmc1_aig_witness_out                  false
% 3.51/0.99  --bmc1_verbose                          false
% 3.51/0.99  --bmc1_dump_clauses_tptp                false
% 3.51/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.99  --bmc1_dump_file                        -
% 3.51/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.99  --bmc1_ucm_extend_mode                  1
% 3.51/0.99  --bmc1_ucm_init_mode                    2
% 3.51/0.99  --bmc1_ucm_cone_mode                    none
% 3.51/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.99  --bmc1_ucm_relax_model                  4
% 3.51/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.99  --bmc1_ucm_layered_model                none
% 3.51/0.99  --bmc1_ucm_max_lemma_size               10
% 3.51/0.99  
% 3.51/0.99  ------ AIG Options
% 3.51/0.99  
% 3.51/0.99  --aig_mode                              false
% 3.51/0.99  
% 3.51/0.99  ------ Instantiation Options
% 3.51/0.99  
% 3.51/0.99  --instantiation_flag                    true
% 3.51/0.99  --inst_sos_flag                         false
% 3.51/0.99  --inst_sos_phase                        true
% 3.51/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel_side                     num_symb
% 3.51/0.99  --inst_solver_per_active                1400
% 3.51/0.99  --inst_solver_calls_frac                1.
% 3.51/0.99  --inst_passive_queue_type               priority_queues
% 3.51/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.99  --inst_passive_queues_freq              [25;2]
% 3.51/0.99  --inst_dismatching                      true
% 3.51/0.99  --inst_eager_unprocessed_to_passive     true
% 3.51/0.99  --inst_prop_sim_given                   true
% 3.51/0.99  --inst_prop_sim_new                     false
% 3.51/0.99  --inst_subs_new                         false
% 3.51/0.99  --inst_eq_res_simp                      false
% 3.51/0.99  --inst_subs_given                       false
% 3.51/0.99  --inst_orphan_elimination               true
% 3.51/0.99  --inst_learning_loop_flag               true
% 3.51/0.99  --inst_learning_start                   3000
% 3.51/0.99  --inst_learning_factor                  2
% 3.51/0.99  --inst_start_prop_sim_after_learn       3
% 3.51/0.99  --inst_sel_renew                        solver
% 3.51/0.99  --inst_lit_activity_flag                true
% 3.51/0.99  --inst_restr_to_given                   false
% 3.51/0.99  --inst_activity_threshold               500
% 3.51/0.99  --inst_out_proof                        true
% 3.51/0.99  
% 3.51/0.99  ------ Resolution Options
% 3.51/0.99  
% 3.51/0.99  --resolution_flag                       true
% 3.51/0.99  --res_lit_sel                           adaptive
% 3.51/0.99  --res_lit_sel_side                      none
% 3.51/0.99  --res_ordering                          kbo
% 3.51/0.99  --res_to_prop_solver                    active
% 3.51/0.99  --res_prop_simpl_new                    false
% 3.51/0.99  --res_prop_simpl_given                  true
% 3.51/0.99  --res_passive_queue_type                priority_queues
% 3.51/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.99  --res_passive_queues_freq               [15;5]
% 3.51/0.99  --res_forward_subs                      full
% 3.51/0.99  --res_backward_subs                     full
% 3.51/0.99  --res_forward_subs_resolution           true
% 3.51/0.99  --res_backward_subs_resolution          true
% 3.51/0.99  --res_orphan_elimination                true
% 3.51/0.99  --res_time_limit                        2.
% 3.51/0.99  --res_out_proof                         true
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Options
% 3.51/0.99  
% 3.51/0.99  --superposition_flag                    true
% 3.51/0.99  --sup_passive_queue_type                priority_queues
% 3.51/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.99  --demod_completeness_check              fast
% 3.51/0.99  --demod_use_ground                      true
% 3.51/0.99  --sup_to_prop_solver                    passive
% 3.51/0.99  --sup_prop_simpl_new                    true
% 3.51/0.99  --sup_prop_simpl_given                  true
% 3.51/0.99  --sup_fun_splitting                     false
% 3.51/0.99  --sup_smt_interval                      50000
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Simplification Setup
% 3.51/0.99  
% 3.51/0.99  --sup_indices_passive                   []
% 3.51/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_full_bw                           [BwDemod]
% 3.51/0.99  --sup_immed_triv                        [TrivRules]
% 3.51/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_immed_bw_main                     []
% 3.51/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  
% 3.51/0.99  ------ Combination Options
% 3.51/0.99  
% 3.51/0.99  --comb_res_mult                         3
% 3.51/0.99  --comb_sup_mult                         2
% 3.51/0.99  --comb_inst_mult                        10
% 3.51/0.99  
% 3.51/0.99  ------ Debug Options
% 3.51/0.99  
% 3.51/0.99  --dbg_backtrace                         false
% 3.51/0.99  --dbg_dump_prop_clauses                 false
% 3.51/0.99  --dbg_dump_prop_clauses_file            -
% 3.51/0.99  --dbg_out_stat                          false
% 3.51/0.99  ------ Parsing...
% 3.51/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.51/0.99  ------ Proving...
% 3.51/0.99  ------ Problem Properties 
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  clauses                                 49
% 3.51/0.99  conjectures                             17
% 3.51/0.99  EPR                                     17
% 3.51/0.99  Horn                                    38
% 3.51/0.99  unary                                   19
% 3.51/0.99  binary                                  7
% 3.51/0.99  lits                                    161
% 3.51/0.99  lits eq                                 18
% 3.51/0.99  fd_pure                                 0
% 3.51/0.99  fd_pseudo                               0
% 3.51/0.99  fd_cond                                 0
% 3.51/0.99  fd_pseudo_cond                          2
% 3.51/0.99  AC symbols                              0
% 3.51/0.99  
% 3.51/0.99  ------ Schedule dynamic 5 is on 
% 3.51/0.99  
% 3.51/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  ------ 
% 3.51/0.99  Current options:
% 3.51/0.99  ------ 
% 3.51/0.99  
% 3.51/0.99  ------ Input Options
% 3.51/0.99  
% 3.51/0.99  --out_options                           all
% 3.51/0.99  --tptp_safe_out                         true
% 3.51/0.99  --problem_path                          ""
% 3.51/0.99  --include_path                          ""
% 3.51/0.99  --clausifier                            res/vclausify_rel
% 3.51/0.99  --clausifier_options                    --mode clausify
% 3.51/0.99  --stdin                                 false
% 3.51/0.99  --stats_out                             all
% 3.51/0.99  
% 3.51/0.99  ------ General Options
% 3.51/0.99  
% 3.51/0.99  --fof                                   false
% 3.51/0.99  --time_out_real                         305.
% 3.51/0.99  --time_out_virtual                      -1.
% 3.51/0.99  --symbol_type_check                     false
% 3.51/0.99  --clausify_out                          false
% 3.51/0.99  --sig_cnt_out                           false
% 3.51/0.99  --trig_cnt_out                          false
% 3.51/0.99  --trig_cnt_out_tolerance                1.
% 3.51/0.99  --trig_cnt_out_sk_spl                   false
% 3.51/0.99  --abstr_cl_out                          false
% 3.51/0.99  
% 3.51/0.99  ------ Global Options
% 3.51/0.99  
% 3.51/0.99  --schedule                              default
% 3.51/0.99  --add_important_lit                     false
% 3.51/0.99  --prop_solver_per_cl                    1000
% 3.51/0.99  --min_unsat_core                        false
% 3.51/0.99  --soft_assumptions                      false
% 3.51/0.99  --soft_lemma_size                       3
% 3.51/0.99  --prop_impl_unit_size                   0
% 3.51/0.99  --prop_impl_unit                        []
% 3.51/0.99  --share_sel_clauses                     true
% 3.51/0.99  --reset_solvers                         false
% 3.51/0.99  --bc_imp_inh                            [conj_cone]
% 3.51/0.99  --conj_cone_tolerance                   3.
% 3.51/0.99  --extra_neg_conj                        none
% 3.51/0.99  --large_theory_mode                     true
% 3.51/0.99  --prolific_symb_bound                   200
% 3.51/0.99  --lt_threshold                          2000
% 3.51/0.99  --clause_weak_htbl                      true
% 3.51/0.99  --gc_record_bc_elim                     false
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing Options
% 3.51/0.99  
% 3.51/0.99  --preprocessing_flag                    true
% 3.51/0.99  --time_out_prep_mult                    0.1
% 3.51/0.99  --splitting_mode                        input
% 3.51/0.99  --splitting_grd                         true
% 3.51/0.99  --splitting_cvd                         false
% 3.51/0.99  --splitting_cvd_svl                     false
% 3.51/0.99  --splitting_nvd                         32
% 3.51/0.99  --sub_typing                            true
% 3.51/0.99  --prep_gs_sim                           true
% 3.51/0.99  --prep_unflatten                        true
% 3.51/0.99  --prep_res_sim                          true
% 3.51/0.99  --prep_upred                            true
% 3.51/0.99  --prep_sem_filter                       exhaustive
% 3.51/0.99  --prep_sem_filter_out                   false
% 3.51/0.99  --pred_elim                             true
% 3.51/1.00  --res_sim_input                         true
% 3.51/1.00  --eq_ax_congr_red                       true
% 3.51/1.00  --pure_diseq_elim                       true
% 3.51/1.00  --brand_transform                       false
% 3.51/1.00  --non_eq_to_eq                          false
% 3.51/1.00  --prep_def_merge                        true
% 3.51/1.00  --prep_def_merge_prop_impl              false
% 3.51/1.00  --prep_def_merge_mbd                    true
% 3.51/1.00  --prep_def_merge_tr_red                 false
% 3.51/1.00  --prep_def_merge_tr_cl                  false
% 3.51/1.00  --smt_preprocessing                     true
% 3.51/1.00  --smt_ac_axioms                         fast
% 3.51/1.00  --preprocessed_out                      false
% 3.51/1.00  --preprocessed_stats                    false
% 3.51/1.00  
% 3.51/1.00  ------ Abstraction refinement Options
% 3.51/1.00  
% 3.51/1.00  --abstr_ref                             []
% 3.51/1.00  --abstr_ref_prep                        false
% 3.51/1.00  --abstr_ref_until_sat                   false
% 3.51/1.00  --abstr_ref_sig_restrict                funpre
% 3.51/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/1.00  --abstr_ref_under                       []
% 3.51/1.00  
% 3.51/1.00  ------ SAT Options
% 3.51/1.00  
% 3.51/1.00  --sat_mode                              false
% 3.51/1.00  --sat_fm_restart_options                ""
% 3.51/1.00  --sat_gr_def                            false
% 3.51/1.00  --sat_epr_types                         true
% 3.51/1.00  --sat_non_cyclic_types                  false
% 3.51/1.00  --sat_finite_models                     false
% 3.51/1.00  --sat_fm_lemmas                         false
% 3.51/1.00  --sat_fm_prep                           false
% 3.51/1.00  --sat_fm_uc_incr                        true
% 3.51/1.00  --sat_out_model                         small
% 3.51/1.00  --sat_out_clauses                       false
% 3.51/1.00  
% 3.51/1.00  ------ QBF Options
% 3.51/1.00  
% 3.51/1.00  --qbf_mode                              false
% 3.51/1.00  --qbf_elim_univ                         false
% 3.51/1.00  --qbf_dom_inst                          none
% 3.51/1.00  --qbf_dom_pre_inst                      false
% 3.51/1.00  --qbf_sk_in                             false
% 3.51/1.00  --qbf_pred_elim                         true
% 3.51/1.00  --qbf_split                             512
% 3.51/1.00  
% 3.51/1.00  ------ BMC1 Options
% 3.51/1.00  
% 3.51/1.00  --bmc1_incremental                      false
% 3.51/1.00  --bmc1_axioms                           reachable_all
% 3.51/1.00  --bmc1_min_bound                        0
% 3.51/1.00  --bmc1_max_bound                        -1
% 3.51/1.00  --bmc1_max_bound_default                -1
% 3.51/1.00  --bmc1_symbol_reachability              true
% 3.51/1.00  --bmc1_property_lemmas                  false
% 3.51/1.00  --bmc1_k_induction                      false
% 3.51/1.00  --bmc1_non_equiv_states                 false
% 3.51/1.00  --bmc1_deadlock                         false
% 3.51/1.00  --bmc1_ucm                              false
% 3.51/1.00  --bmc1_add_unsat_core                   none
% 3.51/1.00  --bmc1_unsat_core_children              false
% 3.51/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/1.00  --bmc1_out_stat                         full
% 3.51/1.00  --bmc1_ground_init                      false
% 3.51/1.00  --bmc1_pre_inst_next_state              false
% 3.51/1.00  --bmc1_pre_inst_state                   false
% 3.51/1.00  --bmc1_pre_inst_reach_state             false
% 3.51/1.00  --bmc1_out_unsat_core                   false
% 3.51/1.00  --bmc1_aig_witness_out                  false
% 3.51/1.00  --bmc1_verbose                          false
% 3.51/1.00  --bmc1_dump_clauses_tptp                false
% 3.51/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.51/1.00  --bmc1_dump_file                        -
% 3.51/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.51/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.51/1.00  --bmc1_ucm_extend_mode                  1
% 3.51/1.00  --bmc1_ucm_init_mode                    2
% 3.51/1.00  --bmc1_ucm_cone_mode                    none
% 3.51/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.51/1.00  --bmc1_ucm_relax_model                  4
% 3.51/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.51/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/1.00  --bmc1_ucm_layered_model                none
% 3.51/1.00  --bmc1_ucm_max_lemma_size               10
% 3.51/1.00  
% 3.51/1.00  ------ AIG Options
% 3.51/1.00  
% 3.51/1.00  --aig_mode                              false
% 3.51/1.00  
% 3.51/1.00  ------ Instantiation Options
% 3.51/1.00  
% 3.51/1.00  --instantiation_flag                    true
% 3.51/1.00  --inst_sos_flag                         false
% 3.51/1.00  --inst_sos_phase                        true
% 3.51/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/1.00  --inst_lit_sel_side                     none
% 3.51/1.00  --inst_solver_per_active                1400
% 3.51/1.00  --inst_solver_calls_frac                1.
% 3.51/1.00  --inst_passive_queue_type               priority_queues
% 3.51/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/1.00  --inst_passive_queues_freq              [25;2]
% 3.51/1.00  --inst_dismatching                      true
% 3.51/1.00  --inst_eager_unprocessed_to_passive     true
% 3.51/1.00  --inst_prop_sim_given                   true
% 3.51/1.00  --inst_prop_sim_new                     false
% 3.51/1.00  --inst_subs_new                         false
% 3.51/1.00  --inst_eq_res_simp                      false
% 3.51/1.00  --inst_subs_given                       false
% 3.51/1.00  --inst_orphan_elimination               true
% 3.51/1.00  --inst_learning_loop_flag               true
% 3.51/1.00  --inst_learning_start                   3000
% 3.51/1.00  --inst_learning_factor                  2
% 3.51/1.00  --inst_start_prop_sim_after_learn       3
% 3.51/1.00  --inst_sel_renew                        solver
% 3.51/1.00  --inst_lit_activity_flag                true
% 3.51/1.00  --inst_restr_to_given                   false
% 3.51/1.00  --inst_activity_threshold               500
% 3.51/1.00  --inst_out_proof                        true
% 3.51/1.00  
% 3.51/1.00  ------ Resolution Options
% 3.51/1.00  
% 3.51/1.00  --resolution_flag                       false
% 3.51/1.00  --res_lit_sel                           adaptive
% 3.51/1.00  --res_lit_sel_side                      none
% 3.51/1.00  --res_ordering                          kbo
% 3.51/1.00  --res_to_prop_solver                    active
% 3.51/1.00  --res_prop_simpl_new                    false
% 3.51/1.00  --res_prop_simpl_given                  true
% 3.51/1.00  --res_passive_queue_type                priority_queues
% 3.51/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/1.00  --res_passive_queues_freq               [15;5]
% 3.51/1.00  --res_forward_subs                      full
% 3.51/1.00  --res_backward_subs                     full
% 3.51/1.00  --res_forward_subs_resolution           true
% 3.51/1.00  --res_backward_subs_resolution          true
% 3.51/1.00  --res_orphan_elimination                true
% 3.51/1.00  --res_time_limit                        2.
% 3.51/1.00  --res_out_proof                         true
% 3.51/1.00  
% 3.51/1.00  ------ Superposition Options
% 3.51/1.00  
% 3.51/1.00  --superposition_flag                    true
% 3.51/1.00  --sup_passive_queue_type                priority_queues
% 3.51/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.51/1.00  --demod_completeness_check              fast
% 3.51/1.00  --demod_use_ground                      true
% 3.51/1.00  --sup_to_prop_solver                    passive
% 3.51/1.00  --sup_prop_simpl_new                    true
% 3.51/1.00  --sup_prop_simpl_given                  true
% 3.51/1.00  --sup_fun_splitting                     false
% 3.51/1.00  --sup_smt_interval                      50000
% 3.51/1.00  
% 3.51/1.00  ------ Superposition Simplification Setup
% 3.51/1.00  
% 3.51/1.00  --sup_indices_passive                   []
% 3.51/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/1.00  --sup_full_bw                           [BwDemod]
% 3.51/1.00  --sup_immed_triv                        [TrivRules]
% 3.51/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/1.00  --sup_immed_bw_main                     []
% 3.51/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/1.00  
% 3.51/1.00  ------ Combination Options
% 3.51/1.00  
% 3.51/1.00  --comb_res_mult                         3
% 3.51/1.00  --comb_sup_mult                         2
% 3.51/1.00  --comb_inst_mult                        10
% 3.51/1.00  
% 3.51/1.00  ------ Debug Options
% 3.51/1.00  
% 3.51/1.00  --dbg_backtrace                         false
% 3.51/1.00  --dbg_dump_prop_clauses                 false
% 3.51/1.00  --dbg_dump_prop_clauses_file            -
% 3.51/1.00  --dbg_out_stat                          false
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  ------ Proving...
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  % SZS status Theorem for theBenchmark.p
% 3.51/1.00  
% 3.51/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.51/1.00  
% 3.51/1.00  fof(f20,conjecture,(
% 3.51/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f21,negated_conjecture,(
% 3.51/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 3.51/1.00    inference(negated_conjecture,[],[f20])).
% 3.51/1.00  
% 3.51/1.00  fof(f49,plain,(
% 3.51/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.51/1.00    inference(ennf_transformation,[],[f21])).
% 3.51/1.00  
% 3.51/1.00  fof(f50,plain,(
% 3.51/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.51/1.00    inference(flattening,[],[f49])).
% 3.51/1.00  
% 3.51/1.00  fof(f74,plain,(
% 3.51/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK10) & sK10 = X5 & m1_subset_1(sK10,u1_struct_0(X2)))) )),
% 3.51/1.00    introduced(choice_axiom,[])).
% 3.51/1.00  
% 3.51/1.00  fof(f73,plain,(
% 3.51/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK9) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK9 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK9,u1_struct_0(X3)))) )),
% 3.51/1.00    introduced(choice_axiom,[])).
% 3.51/1.00  
% 3.51/1.00  fof(f72,plain,(
% 3.51/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK8,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK8),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK8,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK8))) )),
% 3.51/1.00    introduced(choice_axiom,[])).
% 3.51/1.00  
% 3.51/1.00  fof(f71,plain,(
% 3.51/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK7,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK7,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK7 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK7,X0) & ~v2_struct_0(sK7))) )),
% 3.51/1.00    introduced(choice_axiom,[])).
% 3.51/1.00  
% 3.51/1.00  fof(f70,plain,(
% 3.51/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK6,X1,k3_tmap_1(X0,X1,X3,sK6,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK6))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK6,X0) & ~v2_struct_0(sK6))) )),
% 3.51/1.00    introduced(choice_axiom,[])).
% 3.51/1.00  
% 3.51/1.00  fof(f69,plain,(
% 3.51/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK5,X4,X5) & r1_tmap_1(X2,sK5,k3_tmap_1(X0,sK5,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))) )),
% 3.51/1.00    introduced(choice_axiom,[])).
% 3.51/1.00  
% 3.51/1.00  fof(f68,plain,(
% 3.51/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 3.51/1.00    introduced(choice_axiom,[])).
% 3.51/1.00  
% 3.51/1.00  fof(f75,plain,(
% 3.51/1.00    ((((((~r1_tmap_1(sK7,sK5,sK8,sK9) & r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) & sK9 = sK10 & m1_subset_1(sK10,u1_struct_0(sK6))) & m1_subset_1(sK9,u1_struct_0(sK7))) & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) & v1_funct_1(sK8)) & m1_pre_topc(sK7,sK4) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 3.51/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f50,f74,f73,f72,f71,f70,f69,f68])).
% 3.51/1.00  
% 3.51/1.00  fof(f122,plain,(
% 3.51/1.00    m1_pre_topc(sK7,sK4)),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f17,axiom,(
% 3.51/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f44,plain,(
% 3.51/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(ennf_transformation,[],[f17])).
% 3.51/1.00  
% 3.51/1.00  fof(f109,plain,(
% 3.51/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f44])).
% 3.51/1.00  
% 3.51/1.00  fof(f126,plain,(
% 3.51/1.00    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f11,axiom,(
% 3.51/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f35,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(ennf_transformation,[],[f11])).
% 3.51/1.00  
% 3.51/1.00  fof(f64,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(nnf_transformation,[],[f35])).
% 3.51/1.00  
% 3.51/1.00  fof(f99,plain,(
% 3.51/1.00    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f64])).
% 3.51/1.00  
% 3.51/1.00  fof(f7,axiom,(
% 3.51/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f30,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(ennf_transformation,[],[f7])).
% 3.51/1.00  
% 3.51/1.00  fof(f94,plain,(
% 3.51/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f30])).
% 3.51/1.00  
% 3.51/1.00  fof(f13,axiom,(
% 3.51/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f38,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/1.00    inference(ennf_transformation,[],[f13])).
% 3.51/1.00  
% 3.51/1.00  fof(f39,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/1.00    inference(flattening,[],[f38])).
% 3.51/1.00  
% 3.51/1.00  fof(f102,plain,(
% 3.51/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f39])).
% 3.51/1.00  
% 3.51/1.00  fof(f124,plain,(
% 3.51/1.00    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f123,plain,(
% 3.51/1.00    v1_funct_1(sK8)),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f19,axiom,(
% 3.51/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f47,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.51/1.00    inference(ennf_transformation,[],[f19])).
% 3.51/1.00  
% 3.51/1.00  fof(f48,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.51/1.00    inference(flattening,[],[f47])).
% 3.51/1.00  
% 3.51/1.00  fof(f112,plain,(
% 3.51/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f48])).
% 3.51/1.00  
% 3.51/1.00  fof(f116,plain,(
% 3.51/1.00    ~v2_struct_0(sK5)),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f117,plain,(
% 3.51/1.00    v2_pre_topc(sK5)),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f118,plain,(
% 3.51/1.00    l1_pre_topc(sK5)),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f125,plain,(
% 3.51/1.00    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f113,plain,(
% 3.51/1.00    ~v2_struct_0(sK4)),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f114,plain,(
% 3.51/1.00    v2_pre_topc(sK4)),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f115,plain,(
% 3.51/1.00    l1_pre_topc(sK4)),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f120,plain,(
% 3.51/1.00    m1_pre_topc(sK6,sK4)),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f12,axiom,(
% 3.51/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f36,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/1.00    inference(ennf_transformation,[],[f12])).
% 3.51/1.00  
% 3.51/1.00  fof(f37,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/1.00    inference(flattening,[],[f36])).
% 3.51/1.00  
% 3.51/1.00  fof(f101,plain,(
% 3.51/1.00    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f37])).
% 3.51/1.00  
% 3.51/1.00  fof(f121,plain,(
% 3.51/1.00    ~v2_struct_0(sK7)),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f4,axiom,(
% 3.51/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f25,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.51/1.00    inference(ennf_transformation,[],[f4])).
% 3.51/1.00  
% 3.51/1.00  fof(f26,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.51/1.00    inference(flattening,[],[f25])).
% 3.51/1.00  
% 3.51/1.00  fof(f79,plain,(
% 3.51/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f26])).
% 3.51/1.00  
% 3.51/1.00  fof(f130,plain,(
% 3.51/1.00    r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f129,plain,(
% 3.51/1.00    sK9 = sK10),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f6,axiom,(
% 3.51/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f29,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(ennf_transformation,[],[f6])).
% 3.51/1.00  
% 3.51/1.00  fof(f63,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(nnf_transformation,[],[f29])).
% 3.51/1.00  
% 3.51/1.00  fof(f93,plain,(
% 3.51/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f63])).
% 3.51/1.00  
% 3.51/1.00  fof(f15,axiom,(
% 3.51/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f41,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.51/1.00    inference(ennf_transformation,[],[f15])).
% 3.51/1.00  
% 3.51/1.00  fof(f42,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.51/1.00    inference(flattening,[],[f41])).
% 3.51/1.00  
% 3.51/1.00  fof(f65,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.51/1.00    inference(nnf_transformation,[],[f42])).
% 3.51/1.00  
% 3.51/1.00  fof(f66,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.51/1.00    inference(flattening,[],[f65])).
% 3.51/1.00  
% 3.51/1.00  fof(f106,plain,(
% 3.51/1.00    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f66])).
% 3.51/1.00  
% 3.51/1.00  fof(f133,plain,(
% 3.51/1.00    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.51/1.00    inference(equality_resolution,[],[f106])).
% 3.51/1.00  
% 3.51/1.00  fof(f16,axiom,(
% 3.51/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f43,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(ennf_transformation,[],[f16])).
% 3.51/1.00  
% 3.51/1.00  fof(f108,plain,(
% 3.51/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f43])).
% 3.51/1.00  
% 3.51/1.00  fof(f18,axiom,(
% 3.51/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f45,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/1.00    inference(ennf_transformation,[],[f18])).
% 3.51/1.00  
% 3.51/1.00  fof(f46,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/1.00    inference(flattening,[],[f45])).
% 3.51/1.00  
% 3.51/1.00  fof(f67,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4))) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/1.00    inference(nnf_transformation,[],[f46])).
% 3.51/1.00  
% 3.51/1.00  fof(f111,plain,(
% 3.51/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X4) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f67])).
% 3.51/1.00  
% 3.51/1.00  fof(f135,plain,(
% 3.51/1.00    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | ~v1_tsep_1(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/1.00    inference(equality_resolution,[],[f111])).
% 3.51/1.00  
% 3.51/1.00  fof(f10,axiom,(
% 3.51/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f33,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/1.00    inference(ennf_transformation,[],[f10])).
% 3.51/1.00  
% 3.51/1.00  fof(f34,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/1.00    inference(flattening,[],[f33])).
% 3.51/1.00  
% 3.51/1.00  fof(f98,plain,(
% 3.51/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f34])).
% 3.51/1.00  
% 3.51/1.00  fof(f3,axiom,(
% 3.51/1.00    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f23,plain,(
% 3.51/1.00    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(ennf_transformation,[],[f3])).
% 3.51/1.00  
% 3.51/1.00  fof(f24,plain,(
% 3.51/1.00    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(flattening,[],[f23])).
% 3.51/1.00  
% 3.51/1.00  fof(f78,plain,(
% 3.51/1.00    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f24])).
% 3.51/1.00  
% 3.51/1.00  fof(f14,axiom,(
% 3.51/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f40,plain,(
% 3.51/1.00    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(ennf_transformation,[],[f14])).
% 3.51/1.00  
% 3.51/1.00  fof(f103,plain,(
% 3.51/1.00    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f40])).
% 3.51/1.00  
% 3.51/1.00  fof(f9,axiom,(
% 3.51/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f32,plain,(
% 3.51/1.00    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.51/1.00    inference(ennf_transformation,[],[f9])).
% 3.51/1.00  
% 3.51/1.00  fof(f96,plain,(
% 3.51/1.00    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f32])).
% 3.51/1.00  
% 3.51/1.00  fof(f8,axiom,(
% 3.51/1.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f31,plain,(
% 3.51/1.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(ennf_transformation,[],[f8])).
% 3.51/1.00  
% 3.51/1.00  fof(f95,plain,(
% 3.51/1.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f31])).
% 3.51/1.00  
% 3.51/1.00  fof(f97,plain,(
% 3.51/1.00    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.51/1.00    inference(cnf_transformation,[],[f32])).
% 3.51/1.00  
% 3.51/1.00  fof(f5,axiom,(
% 3.51/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.51/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/1.00  
% 3.51/1.00  fof(f22,plain,(
% 3.51/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.51/1.00    inference(rectify,[],[f5])).
% 3.51/1.00  
% 3.51/1.00  fof(f27,plain,(
% 3.51/1.00    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(ennf_transformation,[],[f22])).
% 3.51/1.00  
% 3.51/1.00  fof(f28,plain,(
% 3.51/1.00    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(flattening,[],[f27])).
% 3.51/1.00  
% 3.51/1.00  fof(f51,plain,(
% 3.51/1.00    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.51/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.51/1.00  
% 3.51/1.00  fof(f52,plain,(
% 3.51/1.00    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(definition_folding,[],[f28,f51])).
% 3.51/1.00  
% 3.51/1.00  fof(f58,plain,(
% 3.51/1.00    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(nnf_transformation,[],[f52])).
% 3.51/1.00  
% 3.51/1.00  fof(f59,plain,(
% 3.51/1.00    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(flattening,[],[f58])).
% 3.51/1.00  
% 3.51/1.00  fof(f60,plain,(
% 3.51/1.00    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(rectify,[],[f59])).
% 3.51/1.00  
% 3.51/1.00  fof(f61,plain,(
% 3.51/1.00    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.51/1.00    introduced(choice_axiom,[])).
% 3.51/1.00  
% 3.51/1.00  fof(f62,plain,(
% 3.51/1.00    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.51/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f60,f61])).
% 3.51/1.00  
% 3.51/1.00  fof(f86,plain,(
% 3.51/1.00    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.51/1.00    inference(cnf_transformation,[],[f62])).
% 3.51/1.00  
% 3.51/1.00  fof(f131,plain,(
% 3.51/1.00    ~r1_tmap_1(sK7,sK5,sK8,sK9)),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f127,plain,(
% 3.51/1.00    m1_subset_1(sK9,u1_struct_0(sK7))),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  fof(f119,plain,(
% 3.51/1.00    ~v2_struct_0(sK6)),
% 3.51/1.00    inference(cnf_transformation,[],[f75])).
% 3.51/1.00  
% 3.51/1.00  cnf(c_46,negated_conjecture,
% 3.51/1.00      ( m1_pre_topc(sK7,sK4) ),
% 3.51/1.00      inference(cnf_transformation,[],[f122]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3279,plain,
% 3.51/1.00      ( m1_pre_topc(sK7,sK4) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_33,plain,
% 3.51/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3286,plain,
% 3.51/1.00      ( m1_pre_topc(X0,X0) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_42,negated_conjecture,
% 3.51/1.00      ( g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = sK7 ),
% 3.51/1.00      inference(cnf_transformation,[],[f126]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_24,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_18,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_309,plain,
% 3.51/1.00      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.51/1.00      | ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_24,c_18]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_310,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_309]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3269,plain,
% 3.51/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.51/1.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5240,plain,
% 3.51/1.00      ( m1_pre_topc(X0,sK6) != iProver_top
% 3.51/1.00      | m1_pre_topc(X0,sK7) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK6) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_42,c_3269]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5505,plain,
% 3.51/1.00      ( m1_pre_topc(sK6,sK7) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK6) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3286,c_5240]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_26,plain,
% 3.51/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.51/1.00      | ~ m1_pre_topc(X3,X4)
% 3.51/1.00      | ~ m1_pre_topc(X3,X1)
% 3.51/1.00      | ~ m1_pre_topc(X1,X4)
% 3.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.51/1.00      | ~ v1_funct_1(X0)
% 3.51/1.00      | v2_struct_0(X4)
% 3.51/1.00      | v2_struct_0(X2)
% 3.51/1.00      | ~ v2_pre_topc(X4)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X4)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_44,negated_conjecture,
% 3.51/1.00      ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
% 3.51/1.00      inference(cnf_transformation,[],[f124]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_816,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ m1_pre_topc(X0,X2)
% 3.51/1.00      | ~ m1_pre_topc(X1,X2)
% 3.51/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
% 3.51/1.00      | ~ v1_funct_1(X3)
% 3.51/1.00      | v2_struct_0(X4)
% 3.51/1.00      | v2_struct_0(X2)
% 3.51/1.00      | ~ v2_pre_topc(X4)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X4)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X4),X3,u1_struct_0(X0)) = k3_tmap_1(X2,X4,X1,X0,X3)
% 3.51/1.00      | u1_struct_0(X4) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK7)
% 3.51/1.00      | sK8 != X3 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_44]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_817,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ m1_pre_topc(X1,X2)
% 3.51/1.00      | ~ m1_pre_topc(X0,X2)
% 3.51/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.51/1.00      | ~ v1_funct_1(sK8)
% 3.51/1.00      | v2_struct_0(X2)
% 3.51/1.00      | v2_struct_0(X3)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | ~ v2_pre_topc(X3)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X3)
% 3.51/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
% 3.51/1.00      | u1_struct_0(X3) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_816]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_45,negated_conjecture,
% 3.51/1.00      ( v1_funct_1(sK8) ),
% 3.51/1.00      inference(cnf_transformation,[],[f123]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_821,plain,
% 3.51/1.00      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.51/1.00      | ~ m1_pre_topc(X0,X2)
% 3.51/1.00      | ~ m1_pre_topc(X1,X2)
% 3.51/1.00      | ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | v2_struct_0(X2)
% 3.51/1.00      | v2_struct_0(X3)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | ~ v2_pre_topc(X3)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X3)
% 3.51/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
% 3.51/1.00      | u1_struct_0(X3) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_817,c_45]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_822,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ m1_pre_topc(X1,X2)
% 3.51/1.00      | ~ m1_pre_topc(X0,X2)
% 3.51/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.51/1.00      | v2_struct_0(X2)
% 3.51/1.00      | v2_struct_0(X3)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | ~ v2_pre_topc(X3)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X3)
% 3.51/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
% 3.51/1.00      | u1_struct_0(X3) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_821]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_36,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ m1_pre_topc(X2,X0)
% 3.51/1.00      | m1_pre_topc(X2,X1)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_853,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ m1_pre_topc(X1,X2)
% 3.51/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.51/1.00      | v2_struct_0(X2)
% 3.51/1.00      | v2_struct_0(X3)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | ~ v2_pre_topc(X3)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X3)
% 3.51/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),sK8,u1_struct_0(X0)) = k3_tmap_1(X2,X3,X1,X0,sK8)
% 3.51/1.00      | u1_struct_0(X3) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.51/1.00      inference(forward_subsumption_resolution,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_822,c_36]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3268,plain,
% 3.51/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK8,u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,sK8)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.51/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 3.51/1.00      | m1_pre_topc(X0,X3) != iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.51/1.00      | v2_struct_0(X3) = iProver_top
% 3.51/1.00      | v2_struct_0(X1) = iProver_top
% 3.51/1.00      | v2_pre_topc(X3) != iProver_top
% 3.51/1.00      | v2_pre_topc(X1) != iProver_top
% 3.51/1.00      | l1_pre_topc(X3) != iProver_top
% 3.51/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_853]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4563,plain,
% 3.51/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
% 3.51/1.00      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.51/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 3.51/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.51/1.00      | v2_struct_0(X2) = iProver_top
% 3.51/1.00      | v2_struct_0(sK5) = iProver_top
% 3.51/1.00      | v2_pre_topc(X2) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK5) != iProver_top
% 3.51/1.00      | l1_pre_topc(X2) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK5) != iProver_top ),
% 3.51/1.00      inference(equality_resolution,[status(thm)],[c_3268]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_52,negated_conjecture,
% 3.51/1.00      ( ~ v2_struct_0(sK5) ),
% 3.51/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_59,plain,
% 3.51/1.00      ( v2_struct_0(sK5) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_51,negated_conjecture,
% 3.51/1.00      ( v2_pre_topc(sK5) ),
% 3.51/1.00      inference(cnf_transformation,[],[f117]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_60,plain,
% 3.51/1.00      ( v2_pre_topc(sK5) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_50,negated_conjecture,
% 3.51/1.00      ( l1_pre_topc(sK5) ),
% 3.51/1.00      inference(cnf_transformation,[],[f118]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_61,plain,
% 3.51/1.00      ( l1_pre_topc(sK5) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5092,plain,
% 3.51/1.00      ( l1_pre_topc(X2) != iProver_top
% 3.51/1.00      | v2_struct_0(X2) = iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.51/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 3.51/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 3.51/1.00      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.51/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
% 3.51/1.00      | v2_pre_topc(X2) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4563,c_59,c_60,c_61]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5093,plain,
% 3.51/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k3_tmap_1(X2,sK5,X0,X1,sK8)
% 3.51/1.00      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.51/1.00      | m1_pre_topc(X0,X2) != iProver_top
% 3.51/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.51/1.00      | v2_struct_0(X2) = iProver_top
% 3.51/1.00      | v2_pre_topc(X2) != iProver_top
% 3.51/1.00      | l1_pre_topc(X2) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_5092]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5104,plain,
% 3.51/1.00      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
% 3.51/1.00      | m1_pre_topc(X0,sK7) != iProver_top
% 3.51/1.00      | m1_pre_topc(sK7,X1) != iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
% 3.51/1.00      | v2_struct_0(X1) = iProver_top
% 3.51/1.00      | v2_pre_topc(X1) != iProver_top
% 3.51/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.51/1.00      inference(equality_resolution,[status(thm)],[c_5093]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_43,negated_conjecture,
% 3.51/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
% 3.51/1.00      inference(cnf_transformation,[],[f125]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_68,plain,
% 3.51/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5761,plain,
% 3.51/1.00      ( m1_pre_topc(sK7,X1) != iProver_top
% 3.51/1.00      | m1_pre_topc(X0,sK7) != iProver_top
% 3.51/1.00      | k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
% 3.51/1.00      | v2_struct_0(X1) = iProver_top
% 3.51/1.00      | v2_pre_topc(X1) != iProver_top
% 3.51/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_5104,c_68]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5762,plain,
% 3.51/1.00      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k3_tmap_1(X1,sK5,sK7,X0,sK8)
% 3.51/1.00      | m1_pre_topc(X0,sK7) != iProver_top
% 3.51/1.00      | m1_pre_topc(sK7,X1) != iProver_top
% 3.51/1.00      | v2_struct_0(X1) = iProver_top
% 3.51/1.00      | v2_pre_topc(X1) != iProver_top
% 3.51/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_5761]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5774,plain,
% 3.51/1.00      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(X0,sK5,sK7,sK6,sK8)
% 3.51/1.00      | m1_pre_topc(sK7,X0) != iProver_top
% 3.51/1.00      | v2_struct_0(X0) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK6) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_5505,c_5762]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5814,plain,
% 3.51/1.00      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8)
% 3.51/1.00      | v2_struct_0(sK4) = iProver_top
% 3.51/1.00      | v2_pre_topc(sK4) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK4) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK6) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3279,c_5774]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_55,negated_conjecture,
% 3.51/1.00      ( ~ v2_struct_0(sK4) ),
% 3.51/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_54,negated_conjecture,
% 3.51/1.00      ( v2_pre_topc(sK4) ),
% 3.51/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_53,negated_conjecture,
% 3.51/1.00      ( l1_pre_topc(sK4) ),
% 3.51/1.00      inference(cnf_transformation,[],[f115]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_48,negated_conjecture,
% 3.51/1.00      ( m1_pre_topc(sK6,sK4) ),
% 3.51/1.00      inference(cnf_transformation,[],[f120]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5853,plain,
% 3.51/1.00      ( v2_struct_0(sK4)
% 3.51/1.00      | ~ v2_pre_topc(sK4)
% 3.51/1.00      | ~ l1_pre_topc(sK4)
% 3.51/1.00      | ~ l1_pre_topc(sK6)
% 3.51/1.00      | k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8) ),
% 3.51/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5814]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4406,plain,
% 3.51/1.00      ( ~ m1_pre_topc(sK6,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK6) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5908,plain,
% 3.51/1.00      ( ~ m1_pre_topc(sK6,sK4) | ~ l1_pre_topc(sK4) | l1_pre_topc(sK6) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_4406]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7108,plain,
% 3.51/1.00      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK4,sK5,sK7,sK6,sK8) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_5814,c_55,c_54,c_53,c_48,c_5853,c_5908]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_25,plain,
% 3.51/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.51/1.00      | ~ m1_pre_topc(X3,X1)
% 3.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.51/1.00      | ~ v1_funct_1(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X2)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.51/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_867,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
% 3.51/1.00      | ~ v1_funct_1(X2)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X3)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ v2_pre_topc(X3)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X3)
% 3.51/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X3),X2,u1_struct_0(X0)) = k2_tmap_1(X1,X3,X2,X0)
% 3.51/1.00      | u1_struct_0(X3) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK7)
% 3.51/1.00      | sK8 != X2 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_44]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_868,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.51/1.00      | ~ v1_funct_1(sK8)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X2)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
% 3.51/1.00      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_867]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_872,plain,
% 3.51/1.00      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.51/1.00      | ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X2)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
% 3.51/1.00      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_868,c_45]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_873,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X2)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK8,u1_struct_0(X0)) = k2_tmap_1(X1,X2,sK8,X0)
% 3.51/1.00      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK7) ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_872]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3267,plain,
% 3.51/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK8,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK8,X2)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.51/1.00      | m1_pre_topc(X2,X0) != iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 3.51/1.00      | v2_struct_0(X0) = iProver_top
% 3.51/1.00      | v2_struct_0(X1) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0) != iProver_top
% 3.51/1.00      | v2_pre_topc(X1) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top
% 3.51/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_873]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4374,plain,
% 3.51/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
% 3.51/1.00      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.51/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.51/1.00      | v2_struct_0(X0) = iProver_top
% 3.51/1.00      | v2_struct_0(sK5) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK5) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK5) != iProver_top ),
% 3.51/1.00      inference(equality_resolution,[status(thm)],[c_3267]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4825,plain,
% 3.51/1.00      ( l1_pre_topc(X0) != iProver_top
% 3.51/1.00      | v2_struct_0(X0) = iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.51/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 3.51/1.00      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.51/1.00      | k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
% 3.51/1.00      | v2_pre_topc(X0) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4374,c_59,c_60,c_61]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4826,plain,
% 3.51/1.00      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(sK5),sK8,u1_struct_0(X1)) = k2_tmap_1(X0,sK5,sK8,X1)
% 3.51/1.00      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.51/1.00      | m1_pre_topc(X1,X0) != iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK5)))) != iProver_top
% 3.51/1.00      | v2_struct_0(X0) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_4825]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4836,plain,
% 3.51/1.00      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
% 3.51/1.00      | m1_pre_topc(X0,sK7) != iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
% 3.51/1.00      | v2_struct_0(sK7) = iProver_top
% 3.51/1.00      | v2_pre_topc(sK7) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) != iProver_top ),
% 3.51/1.00      inference(equality_resolution,[status(thm)],[c_4826]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_47,negated_conjecture,
% 3.51/1.00      ( ~ v2_struct_0(sK7) ),
% 3.51/1.00      inference(cnf_transformation,[],[f121]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_64,plain,
% 3.51/1.00      ( v2_struct_0(sK7) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4956,plain,
% 3.51/1.00      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(X0)) = k2_tmap_1(sK7,sK5,sK8,X0)
% 3.51/1.00      | m1_pre_topc(X0,sK7) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK7) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4836,c_64,c_68]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5682,plain,
% 3.51/1.00      ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k2_tmap_1(sK7,sK5,sK8,sK6)
% 3.51/1.00      | v2_pre_topc(sK7) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK6) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_5505,c_4956]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7112,plain,
% 3.51/1.00      ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k2_tmap_1(sK7,sK5,sK8,sK6)
% 3.51/1.00      | v2_pre_topc(sK7) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK6) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) != iProver_top ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_7108,c_5682]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_57,plain,
% 3.51/1.00      ( v2_pre_topc(sK4) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_58,plain,
% 3.51/1.00      ( l1_pre_topc(sK4) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_63,plain,
% 3.51/1.00      ( m1_pre_topc(sK6,sK4) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_65,plain,
% 3.51/1.00      ( m1_pre_topc(sK7,sK4) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5909,plain,
% 3.51/1.00      ( m1_pre_topc(sK6,sK4) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK4) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK6) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_5908]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4430,plain,
% 3.51/1.00      ( ~ m1_pre_topc(sK7,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK7) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5925,plain,
% 3.51/1.00      ( ~ m1_pre_topc(sK7,sK4) | ~ l1_pre_topc(sK4) | l1_pre_topc(sK7) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_4430]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5926,plain,
% 3.51/1.00      ( m1_pre_topc(sK7,sK4) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK4) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_5925]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | v2_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4661,plain,
% 3.51/1.00      ( ~ m1_pre_topc(sK7,X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_pre_topc(sK7)
% 3.51/1.00      | ~ l1_pre_topc(X0) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6126,plain,
% 3.51/1.00      ( ~ m1_pre_topc(sK7,sK4)
% 3.51/1.00      | ~ v2_pre_topc(sK4)
% 3.51/1.00      | v2_pre_topc(sK7)
% 3.51/1.00      | ~ l1_pre_topc(sK4) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_4661]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6127,plain,
% 3.51/1.00      ( m1_pre_topc(sK7,sK4) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK4) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK7) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_6126]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11940,plain,
% 3.51/1.00      ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k2_tmap_1(sK7,sK5,sK8,sK6) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_7112,c_57,c_58,c_63,c_65,c_5909,c_5926,c_6127]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_38,negated_conjecture,
% 3.51/1.00      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) ),
% 3.51/1.00      inference(cnf_transformation,[],[f130]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3283,plain,
% 3.51/1.00      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_39,negated_conjecture,
% 3.51/1.00      ( sK9 = sK10 ),
% 3.51/1.00      inference(cnf_transformation,[],[f129]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3353,plain,
% 3.51/1.00      ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) = iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_3283,c_39]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11943,plain,
% 3.51/1.00      ( r1_tmap_1(sK6,sK5,k2_tmap_1(sK7,sK5,sK8,sK6),sK9) = iProver_top ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_11940,c_3353]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_16,plain,
% 3.51/1.00      ( v3_pre_topc(X0,X1)
% 3.51/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_30,plain,
% 3.51/1.00      ( v1_tsep_1(X0,X1)
% 3.51/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.51/1.00      | ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f133]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_32,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_298,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.51/1.00      | v1_tsep_1(X0,X1)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_30,c_32]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_299,plain,
% 3.51/1.00      ( v1_tsep_1(X0,X1)
% 3.51/1.00      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 3.51/1.00      | ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_298]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_639,plain,
% 3.51/1.00      ( v1_tsep_1(X0,X1)
% 3.51/1.00      | ~ r2_hidden(X2,u1_pre_topc(X3))
% 3.51/1.00      | ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X3)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | X1 != X3
% 3.51/1.00      | u1_struct_0(X0) != X2 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_299]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_640,plain,
% 3.51/1.00      ( v1_tsep_1(X0,X1)
% 3.51/1.00      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 3.51/1.00      | ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_639]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_644,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 3.51/1.00      | v1_tsep_1(X0,X1)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_640,c_32]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_645,plain,
% 3.51/1.00      ( v1_tsep_1(X0,X1)
% 3.51/1.00      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
% 3.51/1.00      | ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_644]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_34,plain,
% 3.51/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.51/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.51/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.51/1.00      | ~ v1_tsep_1(X4,X0)
% 3.51/1.00      | ~ m1_pre_topc(X4,X0)
% 3.51/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.51/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.51/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.51/1.00      | ~ v1_funct_1(X2)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | v2_struct_0(X4)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f135]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_760,plain,
% 3.51/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.51/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.51/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.51/1.00      | ~ r2_hidden(u1_struct_0(X5),u1_pre_topc(X6))
% 3.51/1.00      | ~ m1_pre_topc(X5,X6)
% 3.51/1.00      | ~ m1_pre_topc(X4,X0)
% 3.51/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.51/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.51/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.51/1.00      | ~ v1_funct_1(X2)
% 3.51/1.00      | v2_struct_0(X4)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ v2_pre_topc(X6)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(X6)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | X4 != X5
% 3.51/1.00      | X0 != X6 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_645,c_34]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_761,plain,
% 3.51/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.51/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.51/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.51/1.00      | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X0))
% 3.51/1.00      | ~ m1_pre_topc(X4,X0)
% 3.51/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.51/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.51/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.51/1.00      | ~ v1_funct_1(X2)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X4)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X0) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_760]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_22,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.51/1.00      | m1_subset_1(X2,u1_struct_0(X1))
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_797,plain,
% 3.51/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.51/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.51/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.51/1.00      | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X0))
% 3.51/1.00      | ~ m1_pre_topc(X4,X0)
% 3.51/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.51/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.51/1.00      | ~ v1_funct_1(X2)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X4)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(forward_subsumption_resolution,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_761,c_22]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_912,plain,
% 3.51/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.51/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.51/1.00      | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X0))
% 3.51/1.00      | ~ m1_pre_topc(X4,X0)
% 3.51/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.51/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.51/1.00      | ~ v1_funct_1(X2)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X4)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X0) != u1_struct_0(sK7)
% 3.51/1.00      | sK8 != X2 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_797,c_44]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_913,plain,
% 3.51/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
% 3.51/1.00      | r1_tmap_1(X2,X1,sK8,X3)
% 3.51/1.00      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
% 3.51/1.00      | ~ m1_pre_topc(X0,X2)
% 3.51/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.51/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.51/1.00      | ~ v1_funct_1(sK8)
% 3.51/1.00      | v2_struct_0(X2)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X2) != u1_struct_0(sK7) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_912]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_917,plain,
% 3.51/1.00      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.51/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.51/1.00      | ~ m1_pre_topc(X0,X2)
% 3.51/1.00      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
% 3.51/1.00      | r1_tmap_1(X2,X1,sK8,X3)
% 3.51/1.00      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
% 3.51/1.00      | v2_struct_0(X2)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X2) != u1_struct_0(sK7) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_913,c_45]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_918,plain,
% 3.51/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK8,X0),X3)
% 3.51/1.00      | r1_tmap_1(X2,X1,sK8,X3)
% 3.51/1.00      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X2))
% 3.51/1.00      | ~ m1_pre_topc(X0,X2)
% 3.51/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.51/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X2)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X2) != u1_struct_0(sK7) ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_917]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3266,plain,
% 3.51/1.00      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK7)
% 3.51/1.00      | r1_tmap_1(X2,X0,k2_tmap_1(X1,X0,sK8,X2),X3) != iProver_top
% 3.51/1.00      | r1_tmap_1(X1,X0,sK8,X3) = iProver_top
% 3.51/1.00      | r2_hidden(u1_struct_0(X2),u1_pre_topc(X1)) != iProver_top
% 3.51/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 3.51/1.00      | m1_subset_1(X3,u1_struct_0(X2)) != iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 3.51/1.00      | v2_struct_0(X0) = iProver_top
% 3.51/1.00      | v2_struct_0(X2) = iProver_top
% 3.51/1.00      | v2_struct_0(X1) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0) != iProver_top
% 3.51/1.00      | v2_pre_topc(X1) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top
% 3.51/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_918]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4546,plain,
% 3.51/1.00      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.51/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
% 3.51/1.00      | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
% 3.51/1.00      | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
% 3.51/1.00      | m1_pre_topc(X1,sK7) != iProver_top
% 3.51/1.00      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
% 3.51/1.00      | v2_struct_0(X1) = iProver_top
% 3.51/1.00      | v2_struct_0(X0) = iProver_top
% 3.51/1.00      | v2_struct_0(sK7) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK7) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) != iProver_top ),
% 3.51/1.00      inference(equality_resolution,[status(thm)],[c_3266]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2448,plain,( X0 = X0 ),theory(equality) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3745,plain,
% 3.51/1.00      ( u1_struct_0(sK7) = u1_struct_0(sK7) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_2448]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4023,plain,
% 3.51/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK7,X1,sK8,X0),X2)
% 3.51/1.00      | r1_tmap_1(sK7,X1,sK8,X2)
% 3.51/1.00      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7))
% 3.51/1.00      | ~ m1_pre_topc(X0,sK7)
% 3.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.51/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X1))))
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(sK7)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ v2_pre_topc(sK7)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(sK7)
% 3.51/1.00      | u1_struct_0(X1) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(sK7) != u1_struct_0(sK7) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_918]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4024,plain,
% 3.51/1.00      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.51/1.00      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 3.51/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
% 3.51/1.00      | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
% 3.51/1.00      | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
% 3.51/1.00      | m1_pre_topc(X1,sK7) != iProver_top
% 3.51/1.00      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
% 3.51/1.00      | v2_struct_0(X0) = iProver_top
% 3.51/1.00      | v2_struct_0(X1) = iProver_top
% 3.51/1.00      | v2_struct_0(sK7) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK7) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_4023]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4932,plain,
% 3.51/1.00      ( v2_struct_0(X0) = iProver_top
% 3.51/1.00      | v2_struct_0(X1) = iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
% 3.51/1.00      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.51/1.00      | m1_pre_topc(X1,sK7) != iProver_top
% 3.51/1.00      | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
% 3.51/1.00      | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
% 3.51/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
% 3.51/1.00      | u1_struct_0(X0) != u1_struct_0(sK5)
% 3.51/1.00      | v2_pre_topc(X0) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK7) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4546,c_64,c_3745,c_4024]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4933,plain,
% 3.51/1.00      ( u1_struct_0(X0) != u1_struct_0(sK5)
% 3.51/1.00      | r1_tmap_1(X1,X0,k2_tmap_1(sK7,X0,sK8,X1),X2) != iProver_top
% 3.51/1.00      | r1_tmap_1(sK7,X0,sK8,X2) = iProver_top
% 3.51/1.00      | r2_hidden(u1_struct_0(X1),u1_pre_topc(sK7)) != iProver_top
% 3.51/1.00      | m1_pre_topc(X1,sK7) != iProver_top
% 3.51/1.00      | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) != iProver_top
% 3.51/1.00      | v2_struct_0(X1) = iProver_top
% 3.51/1.00      | v2_struct_0(X0) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK7) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_4932]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4951,plain,
% 3.51/1.00      ( r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
% 3.51/1.00      | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
% 3.51/1.00      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 3.51/1.00      | m1_pre_topc(X0,sK7) != iProver_top
% 3.51/1.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.51/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) != iProver_top
% 3.51/1.00      | v2_struct_0(X0) = iProver_top
% 3.51/1.00      | v2_struct_0(sK5) = iProver_top
% 3.51/1.00      | v2_pre_topc(sK5) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK7) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK5) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) != iProver_top ),
% 3.51/1.00      inference(equality_resolution,[status(thm)],[c_4933]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5166,plain,
% 3.51/1.00      ( v2_pre_topc(sK7) != iProver_top
% 3.51/1.00      | v2_struct_0(X0) = iProver_top
% 3.51/1.00      | r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
% 3.51/1.00      | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
% 3.51/1.00      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 3.51/1.00      | m1_pre_topc(X0,sK7) != iProver_top
% 3.51/1.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4951,c_59,c_60,c_61,c_68]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5167,plain,
% 3.51/1.00      ( r1_tmap_1(X0,sK5,k2_tmap_1(sK7,sK5,sK8,X0),X1) != iProver_top
% 3.51/1.00      | r1_tmap_1(sK7,sK5,sK8,X1) = iProver_top
% 3.51/1.00      | r2_hidden(u1_struct_0(X0),u1_pre_topc(sK7)) != iProver_top
% 3.51/1.00      | m1_pre_topc(X0,sK7) != iProver_top
% 3.51/1.00      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 3.51/1.00      | v2_struct_0(X0) = iProver_top
% 3.51/1.00      | v2_pre_topc(sK7) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_5166]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11947,plain,
% 3.51/1.00      ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
% 3.51/1.00      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) != iProver_top
% 3.51/1.00      | m1_pre_topc(sK6,sK7) != iProver_top
% 3.51/1.00      | m1_subset_1(sK9,u1_struct_0(sK6)) != iProver_top
% 3.51/1.00      | v2_struct_0(sK6) = iProver_top
% 3.51/1.00      | v2_pre_topc(sK7) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_11943,c_5167]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3295,plain,
% 3.51/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.51/1.00      | l1_pre_topc(X1) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6019,plain,
% 3.51/1.00      ( l1_pre_topc(sK4) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) = iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3279,c_3295]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6303,plain,
% 3.51/1.00      ( l1_pre_topc(sK7) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_6019,c_58,c_65,c_5926]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2,plain,
% 3.51/1.00      ( ~ l1_pre_topc(X0)
% 3.51/1.00      | ~ v1_pre_topc(X0)
% 3.51/1.00      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.51/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3309,plain,
% 3.51/1.00      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top
% 3.51/1.00      | v1_pre_topc(X0) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6308,plain,
% 3.51/1.00      ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7
% 3.51/1.00      | v1_pre_topc(sK7) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_6303,c_3309]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_28,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.51/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3288,plain,
% 3.51/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.51/1.00      | l1_pre_topc(X1) != iProver_top
% 3.51/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7483,plain,
% 3.51/1.00      ( l1_pre_topc(sK6) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) != iProver_top
% 3.51/1.00      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))) = iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_5505,c_3288]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7487,plain,
% 3.51/1.00      ( l1_pre_topc(sK6) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) != iProver_top
% 3.51/1.00      | v1_pre_topc(sK7) = iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_7483,c_42]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7737,plain,
% 3.51/1.00      ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = sK7 ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_6308,c_58,c_63,c_65,c_5909,c_5926,c_7487]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_21,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.51/1.00      | X2 = X1
% 3.51/1.00      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3292,plain,
% 3.51/1.00      ( X0 = X1
% 3.51/1.00      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 3.51/1.00      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7607,plain,
% 3.51/1.00      ( g1_pre_topc(X0,X1) != sK7
% 3.51/1.00      | u1_struct_0(sK6) = X0
% 3.51/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_42,c_3292]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_19,plain,
% 3.51/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.51/1.00      | ~ l1_pre_topc(X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5478,plain,
% 3.51/1.00      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
% 3.51/1.00      | ~ l1_pre_topc(sK6) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5483,plain,
% 3.51/1.00      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK6) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_5478]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7608,plain,
% 3.51/1.00      ( g1_pre_topc(X0,X1) != sK7
% 3.51/1.00      | u1_struct_0(sK6) = X0
% 3.51/1.00      | m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_42,c_3292]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7629,plain,
% 3.51/1.00      ( u1_struct_0(sK6) = X0 | g1_pre_topc(X0,X1) != sK7 ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_7607,c_58,c_63,c_5483,c_5909,c_7608]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7630,plain,
% 3.51/1.00      ( g1_pre_topc(X0,X1) != sK7 | u1_struct_0(sK6) = X0 ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_7629]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7741,plain,
% 3.51/1.00      ( u1_struct_0(sK7) = u1_struct_0(sK6) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_7737,c_7630]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11948,plain,
% 3.51/1.00      ( r1_tmap_1(sK7,sK5,sK8,sK9) = iProver_top
% 3.51/1.00      | r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top
% 3.51/1.00      | m1_pre_topc(sK6,sK7) != iProver_top
% 3.51/1.00      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top
% 3.51/1.00      | v2_struct_0(sK6) = iProver_top
% 3.51/1.00      | v2_pre_topc(sK7) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK7) != iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_11947,c_7741]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7908,plain,
% 3.51/1.00      ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK6)) = sK7 ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_7741,c_42]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_20,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.51/1.00      | X2 = X0
% 3.51/1.00      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3293,plain,
% 3.51/1.00      ( X0 = X1
% 3.51/1.00      | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
% 3.51/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8470,plain,
% 3.51/1.00      ( g1_pre_topc(X0,X1) != sK7
% 3.51/1.00      | u1_pre_topc(sK6) = X1
% 3.51/1.00      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_7908,c_3293]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3294,plain,
% 3.51/1.00      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7921,plain,
% 3.51/1.00      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK6) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_7741,c_3294]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8472,plain,
% 3.51/1.00      ( g1_pre_topc(X0,X1) != sK7
% 3.51/1.00      | u1_pre_topc(sK6) = X1
% 3.51/1.00      | m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_7908,c_3293]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9010,plain,
% 3.51/1.00      ( u1_pre_topc(sK6) = X1 | g1_pre_topc(X0,X1) != sK7 ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_8470,c_58,c_63,c_5909,c_7921,c_8472]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9011,plain,
% 3.51/1.00      ( g1_pre_topc(X0,X1) != sK7 | u1_pre_topc(sK6) = X1 ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_9010]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9015,plain,
% 3.51/1.00      ( u1_pre_topc(sK7) = u1_pre_topc(sK6) ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_7737,c_9011]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_15,plain,
% 3.51/1.00      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3296,plain,
% 3.51/1.00      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10002,plain,
% 3.51/1.00      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK7)) = iProver_top
% 3.51/1.00      | v2_pre_topc(sK6) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK6) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_9015,c_3296]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10065,plain,
% 3.51/1.00      ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) = iProver_top
% 3.51/1.00      | v2_pre_topc(sK6) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK6) != iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_10002,c_7741]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3277,plain,
% 3.51/1.00      ( m1_pre_topc(sK6,sK4) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3308,plain,
% 3.51/1.00      ( m1_pre_topc(X0,X1) != iProver_top
% 3.51/1.00      | v2_pre_topc(X1) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0) = iProver_top
% 3.51/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8519,plain,
% 3.51/1.00      ( v2_pre_topc(sK4) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK6) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK4) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3277,c_3308]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_37,negated_conjecture,
% 3.51/1.00      ( ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
% 3.51/1.00      inference(cnf_transformation,[],[f131]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_72,plain,
% 3.51/1.00      ( r1_tmap_1(sK7,sK5,sK8,sK9) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_41,negated_conjecture,
% 3.51/1.00      ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 3.51/1.00      inference(cnf_transformation,[],[f127]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_69,plain,
% 3.51/1.00      ( m1_subset_1(sK9,u1_struct_0(sK7)) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_49,negated_conjecture,
% 3.51/1.00      ( ~ v2_struct_0(sK6) ),
% 3.51/1.00      inference(cnf_transformation,[],[f119]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_62,plain,
% 3.51/1.00      ( v2_struct_0(sK6) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(contradiction,plain,
% 3.51/1.00      ( $false ),
% 3.51/1.00      inference(minisat,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_11948,c_10065,c_8519,c_6127,c_5926,c_5909,c_5505,c_72,
% 3.51/1.00                 c_69,c_65,c_63,c_62,c_58,c_57]) ).
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.51/1.00  
% 3.51/1.00  ------                               Statistics
% 3.51/1.00  
% 3.51/1.00  ------ General
% 3.51/1.00  
% 3.51/1.00  abstr_ref_over_cycles:                  0
% 3.51/1.00  abstr_ref_under_cycles:                 0
% 3.51/1.00  gc_basic_clause_elim:                   0
% 3.51/1.00  forced_gc_time:                         0
% 3.51/1.00  parsing_time:                           0.013
% 3.51/1.00  unif_index_cands_time:                  0.
% 3.51/1.00  unif_index_add_time:                    0.
% 3.51/1.00  orderings_time:                         0.
% 3.51/1.00  out_proof_time:                         0.021
% 3.51/1.00  total_time:                             0.352
% 3.51/1.00  num_of_symbols:                         66
% 3.51/1.00  num_of_terms:                           9472
% 3.51/1.00  
% 3.51/1.00  ------ Preprocessing
% 3.51/1.00  
% 3.51/1.00  num_of_splits:                          0
% 3.51/1.00  num_of_split_atoms:                     0
% 3.51/1.00  num_of_reused_defs:                     0
% 3.51/1.00  num_eq_ax_congr_red:                    29
% 3.51/1.00  num_of_sem_filtered_clauses:            1
% 3.51/1.00  num_of_subtypes:                        0
% 3.51/1.00  monotx_restored_types:                  0
% 3.51/1.00  sat_num_of_epr_types:                   0
% 3.51/1.00  sat_num_of_non_cyclic_types:            0
% 3.51/1.00  sat_guarded_non_collapsed_types:        0
% 3.51/1.00  num_pure_diseq_elim:                    0
% 3.51/1.00  simp_replaced_by:                       0
% 3.51/1.00  res_preprocessed:                       245
% 3.51/1.00  prep_upred:                             0
% 3.51/1.00  prep_unflattend:                        28
% 3.51/1.00  smt_new_axioms:                         0
% 3.51/1.00  pred_elim_cands:                        10
% 3.51/1.00  pred_elim:                              4
% 3.51/1.00  pred_elim_cl:                           6
% 3.51/1.00  pred_elim_cycles:                       10
% 3.51/1.00  merged_defs:                            0
% 3.51/1.00  merged_defs_ncl:                        0
% 3.51/1.00  bin_hyper_res:                          0
% 3.51/1.00  prep_cycles:                            4
% 3.51/1.00  pred_elim_time:                         0.039
% 3.51/1.00  splitting_time:                         0.
% 3.51/1.00  sem_filter_time:                        0.
% 3.51/1.00  monotx_time:                            0.001
% 3.51/1.00  subtype_inf_time:                       0.
% 3.51/1.00  
% 3.51/1.00  ------ Problem properties
% 3.51/1.00  
% 3.51/1.00  clauses:                                49
% 3.51/1.00  conjectures:                            17
% 3.51/1.00  epr:                                    17
% 3.51/1.00  horn:                                   38
% 3.51/1.00  ground:                                 17
% 3.51/1.00  unary:                                  19
% 3.51/1.00  binary:                                 7
% 3.51/1.00  lits:                                   161
% 3.51/1.00  lits_eq:                                18
% 3.51/1.00  fd_pure:                                0
% 3.51/1.00  fd_pseudo:                              0
% 3.51/1.00  fd_cond:                                0
% 3.51/1.00  fd_pseudo_cond:                         2
% 3.51/1.00  ac_symbols:                             0
% 3.51/1.00  
% 3.51/1.00  ------ Propositional Solver
% 3.51/1.00  
% 3.51/1.00  prop_solver_calls:                      26
% 3.51/1.00  prop_fast_solver_calls:                 2616
% 3.51/1.00  smt_solver_calls:                       0
% 3.51/1.00  smt_fast_solver_calls:                  0
% 3.51/1.00  prop_num_of_clauses:                    3816
% 3.51/1.00  prop_preprocess_simplified:             11025
% 3.51/1.00  prop_fo_subsumed:                       87
% 3.51/1.00  prop_solver_time:                       0.
% 3.51/1.00  smt_solver_time:                        0.
% 3.51/1.00  smt_fast_solver_time:                   0.
% 3.51/1.00  prop_fast_solver_time:                  0.
% 3.51/1.00  prop_unsat_core_time:                   0.
% 3.51/1.00  
% 3.51/1.00  ------ QBF
% 3.51/1.00  
% 3.51/1.00  qbf_q_res:                              0
% 3.51/1.00  qbf_num_tautologies:                    0
% 3.51/1.00  qbf_prep_cycles:                        0
% 3.51/1.00  
% 3.51/1.00  ------ BMC1
% 3.51/1.00  
% 3.51/1.00  bmc1_current_bound:                     -1
% 3.51/1.00  bmc1_last_solved_bound:                 -1
% 3.51/1.00  bmc1_unsat_core_size:                   -1
% 3.51/1.00  bmc1_unsat_core_parents_size:           -1
% 3.51/1.00  bmc1_merge_next_fun:                    0
% 3.51/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.51/1.00  
% 3.51/1.00  ------ Instantiation
% 3.51/1.00  
% 3.51/1.00  inst_num_of_clauses:                    1060
% 3.51/1.00  inst_num_in_passive:                    64
% 3.51/1.00  inst_num_in_active:                     545
% 3.51/1.00  inst_num_in_unprocessed:                451
% 3.51/1.00  inst_num_of_loops:                      570
% 3.51/1.00  inst_num_of_learning_restarts:          0
% 3.51/1.00  inst_num_moves_active_passive:          22
% 3.51/1.00  inst_lit_activity:                      0
% 3.51/1.00  inst_lit_activity_moves:                0
% 3.51/1.00  inst_num_tautologies:                   0
% 3.51/1.00  inst_num_prop_implied:                  0
% 3.51/1.00  inst_num_existing_simplified:           0
% 3.51/1.00  inst_num_eq_res_simplified:             0
% 3.51/1.00  inst_num_child_elim:                    0
% 3.51/1.00  inst_num_of_dismatching_blockings:      659
% 3.51/1.00  inst_num_of_non_proper_insts:           1558
% 3.51/1.00  inst_num_of_duplicates:                 0
% 3.51/1.00  inst_inst_num_from_inst_to_res:         0
% 3.51/1.00  inst_dismatching_checking_time:         0.
% 3.51/1.00  
% 3.51/1.00  ------ Resolution
% 3.51/1.00  
% 3.51/1.00  res_num_of_clauses:                     0
% 3.51/1.00  res_num_in_passive:                     0
% 3.51/1.00  res_num_in_active:                      0
% 3.51/1.00  res_num_of_loops:                       249
% 3.51/1.00  res_forward_subset_subsumed:            93
% 3.51/1.00  res_backward_subset_subsumed:           2
% 3.51/1.00  res_forward_subsumed:                   0
% 3.51/1.00  res_backward_subsumed:                  0
% 3.51/1.00  res_forward_subsumption_resolution:     3
% 3.51/1.00  res_backward_subsumption_resolution:    0
% 3.51/1.00  res_clause_to_clause_subsumption:       784
% 3.51/1.00  res_orphan_elimination:                 0
% 3.51/1.00  res_tautology_del:                      116
% 3.51/1.00  res_num_eq_res_simplified:              0
% 3.51/1.00  res_num_sel_changes:                    0
% 3.51/1.00  res_moves_from_active_to_pass:          0
% 3.51/1.00  
% 3.51/1.00  ------ Superposition
% 3.51/1.00  
% 3.51/1.00  sup_time_total:                         0.
% 3.51/1.00  sup_time_generating:                    0.
% 3.51/1.00  sup_time_sim_full:                      0.
% 3.51/1.00  sup_time_sim_immed:                     0.
% 3.51/1.00  
% 3.51/1.00  sup_num_of_clauses:                     156
% 3.51/1.00  sup_num_in_active:                      100
% 3.51/1.00  sup_num_in_passive:                     56
% 3.51/1.00  sup_num_of_loops:                       113
% 3.51/1.00  sup_fw_superposition:                   131
% 3.51/1.00  sup_bw_superposition:                   96
% 3.51/1.00  sup_immediate_simplified:               86
% 3.51/1.00  sup_given_eliminated:                   1
% 3.51/1.00  comparisons_done:                       0
% 3.51/1.00  comparisons_avoided:                    0
% 3.51/1.00  
% 3.51/1.00  ------ Simplifications
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  sim_fw_subset_subsumed:                 21
% 3.51/1.00  sim_bw_subset_subsumed:                 20
% 3.51/1.00  sim_fw_subsumed:                        28
% 3.51/1.00  sim_bw_subsumed:                        0
% 3.51/1.00  sim_fw_subsumption_res:                 0
% 3.51/1.00  sim_bw_subsumption_res:                 0
% 3.51/1.00  sim_tautology_del:                      19
% 3.51/1.00  sim_eq_tautology_del:                   6
% 3.51/1.00  sim_eq_res_simp:                        0
% 3.51/1.00  sim_fw_demodulated:                     0
% 3.51/1.00  sim_bw_demodulated:                     12
% 3.51/1.00  sim_light_normalised:                   66
% 3.51/1.00  sim_joinable_taut:                      0
% 3.51/1.00  sim_joinable_simp:                      0
% 3.51/1.00  sim_ac_normalised:                      0
% 3.51/1.00  sim_smt_subsumption:                    0
% 3.51/1.00  
%------------------------------------------------------------------------------
