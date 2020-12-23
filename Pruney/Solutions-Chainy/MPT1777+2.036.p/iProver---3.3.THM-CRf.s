%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:32 EST 2020

% Result     : Theorem 7.83s
% Output     : CNFRefutation 7.83s
% Verified   : 
% Statistics : Number of formulae       :  186 (1028 expanded)
%              Number of clauses        :  107 ( 230 expanded)
%              Number of leaves         :   21 ( 447 expanded)
%              Depth                    :   17
%              Number of atoms          :  862 (13603 expanded)
%              Number of equality atoms :  161 (1931 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f40,f54,f53,f52,f51,f50,f49,f48])).

fof(f88,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f81,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f55])).

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

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f71])).

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

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(nnf_transformation,[],[f38])).

fof(f78,plain,(
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

fof(f103,plain,(
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
    inference(equality_resolution,[],[f78])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f67,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f96,plain,(
    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f95,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f55])).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f94,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f55])).

fof(f97,plain,(
    ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f82,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f79,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_17869,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_17884,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_19686,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_17869,c_17884])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_44,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_7727,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_8,c_32])).

cnf(c_7728,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7727])).

cnf(c_20004,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19686,c_44,c_7728])).

cnf(c_7,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_17885,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_20009,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_20004,c_17885])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_17886,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_20248,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_20009,c_17886])).

cnf(c_34,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_17867,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_19687,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_17867,c_17884])).

cnf(c_7729,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_8,c_34])).

cnf(c_7730,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7729])).

cnf(c_20113,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19687,c_44,c_7730])).

cnf(c_20118,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_20113,c_17885])).

cnf(c_20409,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_20118,c_17886])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_17880,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_22211,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_20409,c_17880])).

cnf(c_28576,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22211,c_44,c_7730])).

cnf(c_28577,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_28576])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_17887,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_28589,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_28577,c_17887])).

cnf(c_29178,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20248,c_28589])).

cnf(c_22149,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_20248,c_17880])).

cnf(c_28368,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22149,c_44,c_7728])).

cnf(c_28369,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_28368])).

cnf(c_28381,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_28369,c_17887])).

cnf(c_28417,plain,
    ( m1_pre_topc(sK2,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_20409,c_28381])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_18710,plain,
    ( ~ r1_tarski(X0,k2_struct_0(X1))
    | ~ r1_tarski(k2_struct_0(X1),X0)
    | X0 = k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_23493,plain,
    ( ~ r1_tarski(k2_struct_0(X0),k2_struct_0(sK3))
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(X0))
    | k2_struct_0(X0) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_18710])).

cnf(c_26756,plain,
    ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3))
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))
    | k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_23493])).

cnf(c_26757,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26756])).

cnf(c_695,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_18375,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | v3_pre_topc(X1,sK3)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_18625,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
    | X0 != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_18375])).

cnf(c_21339,plain,
    ( v3_pre_topc(k2_struct_0(X0),sK3)
    | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
    | k2_struct_0(X0) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_18625])).

cnf(c_21392,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK3)
    | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
    | k2_struct_0(sK2) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_21339])).

cnf(c_18312,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | v3_pre_topc(u1_struct_0(X1),sK3)
    | u1_struct_0(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_19316,plain,
    ( v3_pre_topc(u1_struct_0(X0),sK3)
    | ~ v3_pre_topc(k2_struct_0(X1),sK3)
    | u1_struct_0(X0) != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_18312])).

cnf(c_21100,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v3_pre_topc(k2_struct_0(X0),sK3)
    | u1_struct_0(sK2) != k2_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_19316])).

cnf(c_21154,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ v3_pre_topc(k2_struct_0(sK2),sK3)
    | u1_struct_0(sK2) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_21100])).

cnf(c_19,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_17878,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_28,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_9,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_17883,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_20791,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_17883])).

cnf(c_20833,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20791,c_44,c_7730])).

cnf(c_20834,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_20833])).

cnf(c_20842,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_17878,c_20834])).

cnf(c_15,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_401,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_17])).

cnf(c_402,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_401])).

cnf(c_18295,plain,
    ( v1_tsep_1(X0,sK3)
    | ~ v3_pre_topc(u1_struct_0(X0),sK3)
    | ~ m1_pre_topc(X0,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_402])).

cnf(c_20037,plain,
    ( v1_tsep_1(sK2,sK3)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_18295])).

cnf(c_21,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tsep_1(X4,X0)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_pre_topc(X0,X5)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_18232,plain,
    ( ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2)
    | r1_tmap_1(sK3,sK1,sK4,X2)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_tsep_1(X0,sK3)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_18905,plain,
    ( ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_tsep_1(X0,sK3)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK3)
    | ~ m1_pre_topc(sK3,X1)
    | ~ m1_subset_1(sK5,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_18232])).

cnf(c_19940,plain,
    ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
    | r1_tmap_1(sK3,sK1,sK4,sK5)
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_18905])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_377,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_8])).

cnf(c_378,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_377])).

cnf(c_17859,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_18838,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_17859])).

cnf(c_19187,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18838,c_44,c_7730])).

cnf(c_19188,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_19187])).

cnf(c_19195,plain,
    ( m1_pre_topc(sK2,sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_17878,c_19188])).

cnf(c_19196,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19195])).

cnf(c_11,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_18380,plain,
    ( v3_pre_topc(k2_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_24,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_17874,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_17941,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17874,c_25])).

cnf(c_18082,plain,
    ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17941])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_8942,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_5,c_32])).

cnf(c_7796,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_7747,plain,
    ( ~ l1_struct_0(sK2)
    | u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_6917,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6956,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6917,c_25])).

cnf(c_7216,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6956])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29178,c_28417,c_26757,c_21392,c_21154,c_20842,c_20037,c_19940,c_19196,c_19195,c_18380,c_18082,c_8942,c_7796,c_7747,c_7730,c_7729,c_7728,c_7727,c_7216,c_23,c_27,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_44,c_39,c_40,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:39:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.83/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.83/1.49  
% 7.83/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.83/1.49  
% 7.83/1.49  ------  iProver source info
% 7.83/1.49  
% 7.83/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.83/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.83/1.49  git: non_committed_changes: false
% 7.83/1.49  git: last_make_outside_of_git: false
% 7.83/1.49  
% 7.83/1.49  ------ 
% 7.83/1.49  ------ Parsing...
% 7.83/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.83/1.49  ------ Proving...
% 7.83/1.49  ------ Problem Properties 
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  clauses                                 40
% 7.83/1.49  conjectures                             19
% 7.83/1.49  EPR                                     20
% 7.83/1.49  Horn                                    35
% 7.83/1.49  unary                                   20
% 7.83/1.49  binary                                  5
% 7.83/1.49  lits                                    126
% 7.83/1.49  lits eq                                 5
% 7.83/1.49  fd_pure                                 0
% 7.83/1.49  fd_pseudo                               0
% 7.83/1.49  fd_cond                                 0
% 7.83/1.49  fd_pseudo_cond                          1
% 7.83/1.49  AC symbols                              0
% 7.83/1.49  
% 7.83/1.49  ------ Input Options Time Limit: Unbounded
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing...
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.83/1.49  Current options:
% 7.83/1.49  ------ 
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ Proving...
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.83/1.49  
% 7.83/1.49  ------ Proving...
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.83/1.49  
% 7.83/1.49  ------ Proving...
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 20 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.83/1.49  
% 7.83/1.49  ------ Proving...
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 20 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.83/1.49  
% 7.83/1.49  ------ Proving...
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.83/1.49  
% 7.83/1.49  ------ Proving...
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.83/1.49  
% 7.83/1.49  ------ Proving...
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.83/1.49  
% 7.83/1.49  ------ Proving...
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.83/1.49  
% 7.83/1.49  ------ Proving...
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 20 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.83/1.49  
% 7.83/1.49  ------ Proving...
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 20 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.83/1.49  
% 7.83/1.49  ------ Proving...
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.83/1.49  
% 7.83/1.49  ------ Proving...
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.83/1.49  
% 7.83/1.49  ------ Proving...
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  % SZS status Theorem for theBenchmark.p
% 7.83/1.49  
% 7.83/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.83/1.49  
% 7.83/1.49  fof(f16,conjecture,(
% 7.83/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 7.83/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f17,negated_conjecture,(
% 7.83/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 7.83/1.49    inference(negated_conjecture,[],[f16])).
% 7.83/1.49  
% 7.83/1.49  fof(f39,plain,(
% 7.83/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.83/1.49    inference(ennf_transformation,[],[f17])).
% 7.83/1.49  
% 7.83/1.49  fof(f40,plain,(
% 7.83/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.83/1.49    inference(flattening,[],[f39])).
% 7.83/1.49  
% 7.83/1.49  fof(f54,plain,(
% 7.83/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) => (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),sK6) & sK6 = X5 & m1_subset_1(sK6,u1_struct_0(X2)))) )),
% 7.83/1.49    introduced(choice_axiom,[])).
% 7.83/1.49  
% 7.83/1.49  fof(f53,plain,(
% 7.83/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) => (? [X6] : (~r1_tmap_1(X3,X1,X4,sK5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 7.83/1.49    introduced(choice_axiom,[])).
% 7.83/1.49  
% 7.83/1.49  fof(f52,plain,(
% 7.83/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,sK4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,sK4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 7.83/1.49    introduced(choice_axiom,[])).
% 7.83/1.49  
% 7.83/1.49  fof(f51,plain,(
% 7.83/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,sK3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.83/1.49    introduced(choice_axiom,[])).
% 7.83/1.49  
% 7.83/1.49  fof(f50,plain,(
% 7.83/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(sK2,X1,k3_tmap_1(X0,X1,X3,sK2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.83/1.49    introduced(choice_axiom,[])).
% 7.83/1.49  
% 7.83/1.49  fof(f49,plain,(
% 7.83/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK1,X4,X5) & r1_tmap_1(X2,sK1,k3_tmap_1(X0,sK1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.83/1.49    introduced(choice_axiom,[])).
% 7.83/1.49  
% 7.83/1.49  fof(f48,plain,(
% 7.83/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.83/1.49    introduced(choice_axiom,[])).
% 7.83/1.49  
% 7.83/1.49  fof(f55,plain,(
% 7.83/1.49    ((((((~r1_tmap_1(sK3,sK1,sK4,sK5) & r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.83/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f40,f54,f53,f52,f51,f50,f49,f48])).
% 7.83/1.49  
% 7.83/1.49  fof(f88,plain,(
% 7.83/1.49    m1_pre_topc(sK3,sK0)),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f6,axiom,(
% 7.83/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.83/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f23,plain,(
% 7.83/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.83/1.49    inference(ennf_transformation,[],[f6])).
% 7.83/1.49  
% 7.83/1.49  fof(f64,plain,(
% 7.83/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f23])).
% 7.83/1.49  
% 7.83/1.49  fof(f81,plain,(
% 7.83/1.49    l1_pre_topc(sK0)),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f5,axiom,(
% 7.83/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.83/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f22,plain,(
% 7.83/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.83/1.49    inference(ennf_transformation,[],[f5])).
% 7.83/1.49  
% 7.83/1.49  fof(f63,plain,(
% 7.83/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f22])).
% 7.83/1.49  
% 7.83/1.49  fof(f4,axiom,(
% 7.83/1.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.83/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f21,plain,(
% 7.83/1.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.83/1.49    inference(ennf_transformation,[],[f4])).
% 7.83/1.49  
% 7.83/1.49  fof(f62,plain,(
% 7.83/1.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f21])).
% 7.83/1.49  
% 7.83/1.49  fof(f86,plain,(
% 7.83/1.49    m1_pre_topc(sK2,sK0)),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f11,axiom,(
% 7.83/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.83/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f31,plain,(
% 7.83/1.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.83/1.49    inference(ennf_transformation,[],[f11])).
% 7.83/1.49  
% 7.83/1.49  fof(f73,plain,(
% 7.83/1.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f31])).
% 7.83/1.49  
% 7.83/1.49  fof(f2,axiom,(
% 7.83/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.83/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f43,plain,(
% 7.83/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.83/1.49    inference(nnf_transformation,[],[f2])).
% 7.83/1.49  
% 7.83/1.49  fof(f59,plain,(
% 7.83/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.83/1.49    inference(cnf_transformation,[],[f43])).
% 7.83/1.49  
% 7.83/1.49  fof(f1,axiom,(
% 7.83/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.83/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f41,plain,(
% 7.83/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.83/1.49    inference(nnf_transformation,[],[f1])).
% 7.83/1.49  
% 7.83/1.49  fof(f42,plain,(
% 7.83/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.83/1.49    inference(flattening,[],[f41])).
% 7.83/1.49  
% 7.83/1.49  fof(f58,plain,(
% 7.83/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f42])).
% 7.83/1.49  
% 7.83/1.49  fof(f13,axiom,(
% 7.83/1.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.83/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f34,plain,(
% 7.83/1.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.83/1.49    inference(ennf_transformation,[],[f13])).
% 7.83/1.49  
% 7.83/1.49  fof(f75,plain,(
% 7.83/1.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f34])).
% 7.83/1.49  
% 7.83/1.49  fof(f92,plain,(
% 7.83/1.49    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f7,axiom,(
% 7.83/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.83/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f24,plain,(
% 7.83/1.49    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.83/1.49    inference(ennf_transformation,[],[f7])).
% 7.83/1.49  
% 7.83/1.49  fof(f44,plain,(
% 7.83/1.49    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.83/1.49    inference(nnf_transformation,[],[f24])).
% 7.83/1.49  
% 7.83/1.49  fof(f66,plain,(
% 7.83/1.49    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f44])).
% 7.83/1.49  
% 7.83/1.49  fof(f10,axiom,(
% 7.83/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 7.83/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f29,plain,(
% 7.83/1.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.83/1.49    inference(ennf_transformation,[],[f10])).
% 7.83/1.49  
% 7.83/1.49  fof(f30,plain,(
% 7.83/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.83/1.49    inference(flattening,[],[f29])).
% 7.83/1.49  
% 7.83/1.49  fof(f45,plain,(
% 7.83/1.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.83/1.49    inference(nnf_transformation,[],[f30])).
% 7.83/1.49  
% 7.83/1.49  fof(f46,plain,(
% 7.83/1.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.83/1.49    inference(flattening,[],[f45])).
% 7.83/1.49  
% 7.83/1.49  fof(f71,plain,(
% 7.83/1.49    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f46])).
% 7.83/1.49  
% 7.83/1.49  fof(f101,plain,(
% 7.83/1.49    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.83/1.49    inference(equality_resolution,[],[f71])).
% 7.83/1.49  
% 7.83/1.49  fof(f15,axiom,(
% 7.83/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 7.83/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f37,plain,(
% 7.83/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.83/1.49    inference(ennf_transformation,[],[f15])).
% 7.83/1.49  
% 7.83/1.49  fof(f38,plain,(
% 7.83/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.83/1.49    inference(flattening,[],[f37])).
% 7.83/1.49  
% 7.83/1.49  fof(f47,plain,(
% 7.83/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.83/1.49    inference(nnf_transformation,[],[f38])).
% 7.83/1.49  
% 7.83/1.49  fof(f78,plain,(
% 7.83/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f47])).
% 7.83/1.49  
% 7.83/1.49  fof(f103,plain,(
% 7.83/1.49    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.83/1.49    inference(equality_resolution,[],[f78])).
% 7.83/1.49  
% 7.83/1.49  fof(f65,plain,(
% 7.83/1.49    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f44])).
% 7.83/1.49  
% 7.83/1.49  fof(f8,axiom,(
% 7.83/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 7.83/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f25,plain,(
% 7.83/1.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.83/1.49    inference(ennf_transformation,[],[f8])).
% 7.83/1.49  
% 7.83/1.49  fof(f26,plain,(
% 7.83/1.49    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.83/1.49    inference(flattening,[],[f25])).
% 7.83/1.49  
% 7.83/1.49  fof(f67,plain,(
% 7.83/1.49    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f26])).
% 7.83/1.49  
% 7.83/1.49  fof(f96,plain,(
% 7.83/1.49    r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6)),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f95,plain,(
% 7.83/1.49    sK5 = sK6),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f3,axiom,(
% 7.83/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.83/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f19,plain,(
% 7.83/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.83/1.49    inference(ennf_transformation,[],[f3])).
% 7.83/1.49  
% 7.83/1.49  fof(f20,plain,(
% 7.83/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.83/1.49    inference(flattening,[],[f19])).
% 7.83/1.49  
% 7.83/1.49  fof(f61,plain,(
% 7.83/1.49    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f20])).
% 7.83/1.49  
% 7.83/1.49  fof(f94,plain,(
% 7.83/1.49    m1_subset_1(sK6,u1_struct_0(sK2))),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f97,plain,(
% 7.83/1.49    ~r1_tmap_1(sK3,sK1,sK4,sK5)),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f93,plain,(
% 7.83/1.49    m1_subset_1(sK5,u1_struct_0(sK3))),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f91,plain,(
% 7.83/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f90,plain,(
% 7.83/1.49    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f89,plain,(
% 7.83/1.49    v1_funct_1(sK4)),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f87,plain,(
% 7.83/1.49    ~v2_struct_0(sK3)),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f85,plain,(
% 7.83/1.49    ~v2_struct_0(sK2)),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f84,plain,(
% 7.83/1.49    l1_pre_topc(sK1)),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f83,plain,(
% 7.83/1.49    v2_pre_topc(sK1)),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f82,plain,(
% 7.83/1.49    ~v2_struct_0(sK1)),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f80,plain,(
% 7.83/1.49    v2_pre_topc(sK0)),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f79,plain,(
% 7.83/1.49    ~v2_struct_0(sK0)),
% 7.83/1.49    inference(cnf_transformation,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  cnf(c_32,negated_conjecture,
% 7.83/1.49      ( m1_pre_topc(sK3,sK0) ),
% 7.83/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_17869,plain,
% 7.83/1.49      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_8,plain,
% 7.83/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.83/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_17884,plain,
% 7.83/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.83/1.49      | l1_pre_topc(X1) != iProver_top
% 7.83/1.49      | l1_pre_topc(X0) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_19686,plain,
% 7.83/1.49      ( l1_pre_topc(sK0) != iProver_top
% 7.83/1.49      | l1_pre_topc(sK3) = iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_17869,c_17884]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_39,negated_conjecture,
% 7.83/1.49      ( l1_pre_topc(sK0) ),
% 7.83/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_44,plain,
% 7.83/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_7727,plain,
% 7.83/1.49      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK3) ),
% 7.83/1.49      inference(resolution,[status(thm)],[c_8,c_32]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_7728,plain,
% 7.83/1.49      ( l1_pre_topc(sK0) != iProver_top
% 7.83/1.49      | l1_pre_topc(sK3) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_7727]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_20004,plain,
% 7.83/1.49      ( l1_pre_topc(sK3) = iProver_top ),
% 7.83/1.49      inference(global_propositional_subsumption,
% 7.83/1.49                [status(thm)],
% 7.83/1.49                [c_19686,c_44,c_7728]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_7,plain,
% 7.83/1.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.83/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_17885,plain,
% 7.83/1.49      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_20009,plain,
% 7.83/1.49      ( l1_struct_0(sK3) = iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_20004,c_17885]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_6,plain,
% 7.83/1.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.83/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_17886,plain,
% 7.83/1.49      ( u1_struct_0(X0) = k2_struct_0(X0)
% 7.83/1.49      | l1_struct_0(X0) != iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_20248,plain,
% 7.83/1.49      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_20009,c_17886]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_34,negated_conjecture,
% 7.83/1.49      ( m1_pre_topc(sK2,sK0) ),
% 7.83/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_17867,plain,
% 7.83/1.49      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_19687,plain,
% 7.83/1.49      ( l1_pre_topc(sK0) != iProver_top
% 7.83/1.49      | l1_pre_topc(sK2) = iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_17867,c_17884]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_7729,plain,
% 7.83/1.49      ( ~ l1_pre_topc(sK0) | l1_pre_topc(sK2) ),
% 7.83/1.49      inference(resolution,[status(thm)],[c_8,c_34]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_7730,plain,
% 7.83/1.49      ( l1_pre_topc(sK0) != iProver_top
% 7.83/1.49      | l1_pre_topc(sK2) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_7729]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_20113,plain,
% 7.83/1.49      ( l1_pre_topc(sK2) = iProver_top ),
% 7.83/1.49      inference(global_propositional_subsumption,
% 7.83/1.49                [status(thm)],
% 7.83/1.49                [c_19687,c_44,c_7730]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_20118,plain,
% 7.83/1.49      ( l1_struct_0(sK2) = iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_20113,c_17885]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_20409,plain,
% 7.83/1.49      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_20118,c_17886]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_17,plain,
% 7.83/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.83/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.83/1.49      | ~ l1_pre_topc(X1) ),
% 7.83/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_17880,plain,
% 7.83/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.83/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.83/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_22211,plain,
% 7.83/1.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.83/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
% 7.83/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_20409,c_17880]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_28576,plain,
% 7.83/1.49      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top
% 7.83/1.49      | m1_pre_topc(X0,sK2) != iProver_top ),
% 7.83/1.49      inference(global_propositional_subsumption,
% 7.83/1.49                [status(thm)],
% 7.83/1.49                [c_22211,c_44,c_7730]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_28577,plain,
% 7.83/1.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.83/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 7.83/1.49      inference(renaming,[status(thm)],[c_28576]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_4,plain,
% 7.83/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.83/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_17887,plain,
% 7.83/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.83/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_28589,plain,
% 7.83/1.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.83/1.49      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_28577,c_17887]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_29178,plain,
% 7.83/1.49      ( m1_pre_topc(sK3,sK2) != iProver_top
% 7.83/1.49      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_20248,c_28589]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_22149,plain,
% 7.83/1.49      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.83/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 7.83/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_20248,c_17880]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_28368,plain,
% 7.83/1.49      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top
% 7.83/1.49      | m1_pre_topc(X0,sK3) != iProver_top ),
% 7.83/1.49      inference(global_propositional_subsumption,
% 7.83/1.49                [status(thm)],
% 7.83/1.49                [c_22149,c_44,c_7728]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_28369,plain,
% 7.83/1.49      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.83/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 7.83/1.49      inference(renaming,[status(thm)],[c_28368]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_28381,plain,
% 7.83/1.49      ( m1_pre_topc(X0,sK3) != iProver_top
% 7.83/1.49      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_28369,c_17887]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_28417,plain,
% 7.83/1.49      ( m1_pre_topc(sK2,sK3) != iProver_top
% 7.83/1.49      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_20409,c_28381]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_0,plain,
% 7.83/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.83/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_18710,plain,
% 7.83/1.49      ( ~ r1_tarski(X0,k2_struct_0(X1))
% 7.83/1.49      | ~ r1_tarski(k2_struct_0(X1),X0)
% 7.83/1.49      | X0 = k2_struct_0(X1) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_23493,plain,
% 7.83/1.49      ( ~ r1_tarski(k2_struct_0(X0),k2_struct_0(sK3))
% 7.83/1.49      | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(X0))
% 7.83/1.49      | k2_struct_0(X0) = k2_struct_0(sK3) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_18710]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_26756,plain,
% 7.83/1.49      ( ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3))
% 7.83/1.49      | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2))
% 7.83/1.49      | k2_struct_0(sK2) = k2_struct_0(sK3) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_23493]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_26757,plain,
% 7.83/1.49      ( k2_struct_0(sK2) = k2_struct_0(sK3)
% 7.83/1.49      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
% 7.83/1.49      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_26756]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_695,plain,
% 7.83/1.49      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X1) | X2 != X0 ),
% 7.83/1.49      theory(equality) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_18375,plain,
% 7.83/1.49      ( ~ v3_pre_topc(X0,sK3) | v3_pre_topc(X1,sK3) | X1 != X0 ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_695]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_18625,plain,
% 7.83/1.49      ( v3_pre_topc(X0,sK3)
% 7.83/1.49      | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
% 7.83/1.49      | X0 != k2_struct_0(sK3) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_18375]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_21339,plain,
% 7.83/1.49      ( v3_pre_topc(k2_struct_0(X0),sK3)
% 7.83/1.49      | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
% 7.83/1.49      | k2_struct_0(X0) != k2_struct_0(sK3) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_18625]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_21392,plain,
% 7.83/1.49      ( v3_pre_topc(k2_struct_0(sK2),sK3)
% 7.83/1.49      | ~ v3_pre_topc(k2_struct_0(sK3),sK3)
% 7.83/1.49      | k2_struct_0(sK2) != k2_struct_0(sK3) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_21339]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_18312,plain,
% 7.83/1.49      ( ~ v3_pre_topc(X0,sK3)
% 7.83/1.49      | v3_pre_topc(u1_struct_0(X1),sK3)
% 7.83/1.49      | u1_struct_0(X1) != X0 ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_695]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_19316,plain,
% 7.83/1.49      ( v3_pre_topc(u1_struct_0(X0),sK3)
% 7.83/1.49      | ~ v3_pre_topc(k2_struct_0(X1),sK3)
% 7.83/1.49      | u1_struct_0(X0) != k2_struct_0(X1) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_18312]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_21100,plain,
% 7.83/1.49      ( v3_pre_topc(u1_struct_0(sK2),sK3)
% 7.83/1.49      | ~ v3_pre_topc(k2_struct_0(X0),sK3)
% 7.83/1.49      | u1_struct_0(sK2) != k2_struct_0(X0) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_19316]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_21154,plain,
% 7.83/1.49      ( v3_pre_topc(u1_struct_0(sK2),sK3)
% 7.83/1.49      | ~ v3_pre_topc(k2_struct_0(sK2),sK3)
% 7.83/1.49      | u1_struct_0(sK2) != k2_struct_0(sK2) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_21100]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_19,plain,
% 7.83/1.49      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.83/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_17878,plain,
% 7.83/1.49      ( m1_pre_topc(X0,X0) = iProver_top
% 7.83/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_28,negated_conjecture,
% 7.83/1.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK3 ),
% 7.83/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_9,plain,
% 7.83/1.49      ( m1_pre_topc(X0,X1)
% 7.83/1.49      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.83/1.49      | ~ l1_pre_topc(X0)
% 7.83/1.49      | ~ l1_pre_topc(X1) ),
% 7.83/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_17883,plain,
% 7.83/1.49      ( m1_pre_topc(X0,X1) = iProver_top
% 7.83/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 7.83/1.49      | l1_pre_topc(X1) != iProver_top
% 7.83/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_20791,plain,
% 7.83/1.49      ( m1_pre_topc(X0,sK2) = iProver_top
% 7.83/1.49      | m1_pre_topc(X0,sK3) != iProver_top
% 7.83/1.49      | l1_pre_topc(X0) != iProver_top
% 7.83/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_28,c_17883]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_20833,plain,
% 7.83/1.49      ( l1_pre_topc(X0) != iProver_top
% 7.83/1.49      | m1_pre_topc(X0,sK3) != iProver_top
% 7.83/1.49      | m1_pre_topc(X0,sK2) = iProver_top ),
% 7.83/1.49      inference(global_propositional_subsumption,
% 7.83/1.49                [status(thm)],
% 7.83/1.49                [c_20791,c_44,c_7730]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_20834,plain,
% 7.83/1.49      ( m1_pre_topc(X0,sK2) = iProver_top
% 7.83/1.49      | m1_pre_topc(X0,sK3) != iProver_top
% 7.83/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.83/1.49      inference(renaming,[status(thm)],[c_20833]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_20842,plain,
% 7.83/1.49      ( m1_pre_topc(sK3,sK2) = iProver_top
% 7.83/1.49      | l1_pre_topc(sK3) != iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_17878,c_20834]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_15,plain,
% 7.83/1.49      ( v1_tsep_1(X0,X1)
% 7.83/1.49      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.83/1.49      | ~ m1_pre_topc(X0,X1)
% 7.83/1.49      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.83/1.49      | ~ l1_pre_topc(X1)
% 7.83/1.49      | ~ v2_pre_topc(X1) ),
% 7.83/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_401,plain,
% 7.83/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.83/1.49      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.83/1.49      | v1_tsep_1(X0,X1)
% 7.83/1.49      | ~ l1_pre_topc(X1)
% 7.83/1.49      | ~ v2_pre_topc(X1) ),
% 7.83/1.49      inference(global_propositional_subsumption,
% 7.83/1.49                [status(thm)],
% 7.83/1.49                [c_15,c_17]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_402,plain,
% 7.83/1.49      ( v1_tsep_1(X0,X1)
% 7.83/1.49      | ~ v3_pre_topc(u1_struct_0(X0),X1)
% 7.83/1.49      | ~ m1_pre_topc(X0,X1)
% 7.83/1.49      | ~ l1_pre_topc(X1)
% 7.83/1.49      | ~ v2_pre_topc(X1) ),
% 7.83/1.49      inference(renaming,[status(thm)],[c_401]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_18295,plain,
% 7.83/1.49      ( v1_tsep_1(X0,sK3)
% 7.83/1.49      | ~ v3_pre_topc(u1_struct_0(X0),sK3)
% 7.83/1.49      | ~ m1_pre_topc(X0,sK3)
% 7.83/1.49      | ~ l1_pre_topc(sK3)
% 7.83/1.49      | ~ v2_pre_topc(sK3) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_402]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_20037,plain,
% 7.83/1.49      ( v1_tsep_1(sK2,sK3)
% 7.83/1.49      | ~ v3_pre_topc(u1_struct_0(sK2),sK3)
% 7.83/1.49      | ~ m1_pre_topc(sK2,sK3)
% 7.83/1.49      | ~ l1_pre_topc(sK3)
% 7.83/1.49      | ~ v2_pre_topc(sK3) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_18295]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_21,plain,
% 7.83/1.49      ( r1_tmap_1(X0,X1,X2,X3)
% 7.83/1.49      | ~ r1_tmap_1(X4,X1,k3_tmap_1(X5,X1,X0,X4,X2),X3)
% 7.83/1.49      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.83/1.49      | ~ v1_tsep_1(X4,X0)
% 7.83/1.49      | ~ m1_pre_topc(X4,X5)
% 7.83/1.49      | ~ m1_pre_topc(X4,X0)
% 7.83/1.49      | ~ m1_pre_topc(X0,X5)
% 7.83/1.49      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 7.83/1.49      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 7.83/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.83/1.49      | ~ v1_funct_1(X2)
% 7.83/1.49      | v2_struct_0(X5)
% 7.83/1.49      | v2_struct_0(X1)
% 7.83/1.49      | v2_struct_0(X4)
% 7.83/1.49      | v2_struct_0(X0)
% 7.83/1.49      | ~ l1_pre_topc(X5)
% 7.83/1.49      | ~ l1_pre_topc(X1)
% 7.83/1.49      | ~ v2_pre_topc(X5)
% 7.83/1.49      | ~ v2_pre_topc(X1) ),
% 7.83/1.49      inference(cnf_transformation,[],[f103]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_18232,plain,
% 7.83/1.49      ( ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),X2)
% 7.83/1.49      | r1_tmap_1(sK3,sK1,sK4,X2)
% 7.83/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 7.83/1.49      | ~ v1_tsep_1(X0,sK3)
% 7.83/1.49      | ~ m1_pre_topc(X0,X1)
% 7.83/1.49      | ~ m1_pre_topc(X0,sK3)
% 7.83/1.49      | ~ m1_pre_topc(sK3,X1)
% 7.83/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.83/1.49      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 7.83/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 7.83/1.49      | ~ v1_funct_1(sK4)
% 7.83/1.49      | v2_struct_0(X0)
% 7.83/1.49      | v2_struct_0(X1)
% 7.83/1.49      | v2_struct_0(sK1)
% 7.83/1.49      | v2_struct_0(sK3)
% 7.83/1.49      | ~ l1_pre_topc(X1)
% 7.83/1.49      | ~ l1_pre_topc(sK1)
% 7.83/1.49      | ~ v2_pre_topc(X1)
% 7.83/1.49      | ~ v2_pre_topc(sK1) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_21]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_18905,plain,
% 7.83/1.49      ( ~ r1_tmap_1(X0,sK1,k3_tmap_1(X1,sK1,sK3,X0,sK4),sK5)
% 7.83/1.49      | r1_tmap_1(sK3,sK1,sK4,sK5)
% 7.83/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 7.83/1.49      | ~ v1_tsep_1(X0,sK3)
% 7.83/1.49      | ~ m1_pre_topc(X0,X1)
% 7.83/1.49      | ~ m1_pre_topc(X0,sK3)
% 7.83/1.49      | ~ m1_pre_topc(sK3,X1)
% 7.83/1.49      | ~ m1_subset_1(sK5,u1_struct_0(X0))
% 7.83/1.49      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 7.83/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 7.83/1.49      | ~ v1_funct_1(sK4)
% 7.83/1.49      | v2_struct_0(X0)
% 7.83/1.49      | v2_struct_0(X1)
% 7.83/1.49      | v2_struct_0(sK1)
% 7.83/1.49      | v2_struct_0(sK3)
% 7.83/1.49      | ~ l1_pre_topc(X1)
% 7.83/1.49      | ~ l1_pre_topc(sK1)
% 7.83/1.49      | ~ v2_pre_topc(X1)
% 7.83/1.49      | ~ v2_pre_topc(sK1) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_18232]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_19940,plain,
% 7.83/1.49      ( ~ r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5)
% 7.83/1.49      | r1_tmap_1(sK3,sK1,sK4,sK5)
% 7.83/1.49      | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1))
% 7.83/1.49      | ~ v1_tsep_1(sK2,sK3)
% 7.83/1.49      | ~ m1_pre_topc(sK2,sK0)
% 7.83/1.49      | ~ m1_pre_topc(sK2,sK3)
% 7.83/1.49      | ~ m1_pre_topc(sK3,sK0)
% 7.83/1.49      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 7.83/1.49      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 7.83/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 7.83/1.49      | ~ v1_funct_1(sK4)
% 7.83/1.49      | v2_struct_0(sK0)
% 7.83/1.49      | v2_struct_0(sK2)
% 7.83/1.49      | v2_struct_0(sK1)
% 7.83/1.49      | v2_struct_0(sK3)
% 7.83/1.49      | ~ l1_pre_topc(sK0)
% 7.83/1.49      | ~ l1_pre_topc(sK1)
% 7.83/1.49      | ~ v2_pre_topc(sK0)
% 7.83/1.49      | ~ v2_pre_topc(sK1) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_18905]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_10,plain,
% 7.83/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.83/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.83/1.49      | ~ l1_pre_topc(X0)
% 7.83/1.49      | ~ l1_pre_topc(X1) ),
% 7.83/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_377,plain,
% 7.83/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.83/1.49      | ~ m1_pre_topc(X0,X1)
% 7.83/1.49      | ~ l1_pre_topc(X1) ),
% 7.83/1.49      inference(global_propositional_subsumption,
% 7.83/1.49                [status(thm)],
% 7.83/1.49                [c_10,c_8]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_378,plain,
% 7.83/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.83/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.83/1.49      | ~ l1_pre_topc(X1) ),
% 7.83/1.49      inference(renaming,[status(thm)],[c_377]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_17859,plain,
% 7.83/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.83/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 7.83/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_18838,plain,
% 7.83/1.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.83/1.49      | m1_pre_topc(X0,sK3) = iProver_top
% 7.83/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_28,c_17859]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_19187,plain,
% 7.83/1.49      ( m1_pre_topc(X0,sK3) = iProver_top
% 7.83/1.49      | m1_pre_topc(X0,sK2) != iProver_top ),
% 7.83/1.49      inference(global_propositional_subsumption,
% 7.83/1.49                [status(thm)],
% 7.83/1.49                [c_18838,c_44,c_7730]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_19188,plain,
% 7.83/1.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.83/1.49      | m1_pre_topc(X0,sK3) = iProver_top ),
% 7.83/1.49      inference(renaming,[status(thm)],[c_19187]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_19195,plain,
% 7.83/1.49      ( m1_pre_topc(sK2,sK3) = iProver_top
% 7.83/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_17878,c_19188]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_19196,plain,
% 7.83/1.49      ( m1_pre_topc(sK2,sK3) | ~ l1_pre_topc(sK2) ),
% 7.83/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_19195]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_11,plain,
% 7.83/1.49      ( v3_pre_topc(k2_struct_0(X0),X0)
% 7.83/1.49      | ~ l1_pre_topc(X0)
% 7.83/1.49      | ~ v2_pre_topc(X0) ),
% 7.83/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_18380,plain,
% 7.83/1.49      ( v3_pre_topc(k2_struct_0(sK3),sK3)
% 7.83/1.49      | ~ l1_pre_topc(sK3)
% 7.83/1.49      | ~ v2_pre_topc(sK3) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_24,negated_conjecture,
% 7.83/1.49      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) ),
% 7.83/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_17874,plain,
% 7.83/1.49      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK6) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_25,negated_conjecture,
% 7.83/1.49      ( sK5 = sK6 ),
% 7.83/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_17941,plain,
% 7.83/1.49      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) = iProver_top ),
% 7.83/1.49      inference(light_normalisation,[status(thm)],[c_17874,c_25]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_18082,plain,
% 7.83/1.49      ( r1_tmap_1(sK2,sK1,k3_tmap_1(sK0,sK1,sK3,sK2,sK4),sK5) ),
% 7.83/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_17941]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_5,plain,
% 7.83/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.83/1.49      | ~ l1_pre_topc(X1)
% 7.83/1.49      | ~ v2_pre_topc(X1)
% 7.83/1.49      | v2_pre_topc(X0) ),
% 7.83/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_8942,plain,
% 7.83/1.49      ( ~ l1_pre_topc(sK0) | ~ v2_pre_topc(sK0) | v2_pre_topc(sK3) ),
% 7.83/1.49      inference(resolution,[status(thm)],[c_5,c_32]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_7796,plain,
% 7.83/1.49      ( l1_struct_0(sK2) | ~ l1_pre_topc(sK2) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_7747,plain,
% 7.83/1.49      ( ~ l1_struct_0(sK2) | u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_26,negated_conjecture,
% 7.83/1.49      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 7.83/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_6917,plain,
% 7.83/1.49      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_6956,plain,
% 7.83/1.49      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 7.83/1.49      inference(light_normalisation,[status(thm)],[c_6917,c_25]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_7216,plain,
% 7.83/1.49      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 7.83/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_6956]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_23,negated_conjecture,
% 7.83/1.49      ( ~ r1_tmap_1(sK3,sK1,sK4,sK5) ),
% 7.83/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_27,negated_conjecture,
% 7.83/1.49      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 7.83/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_29,negated_conjecture,
% 7.83/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 7.83/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_30,negated_conjecture,
% 7.83/1.49      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 7.83/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_31,negated_conjecture,
% 7.83/1.49      ( v1_funct_1(sK4) ),
% 7.83/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_33,negated_conjecture,
% 7.83/1.49      ( ~ v2_struct_0(sK3) ),
% 7.83/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_35,negated_conjecture,
% 7.83/1.49      ( ~ v2_struct_0(sK2) ),
% 7.83/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_36,negated_conjecture,
% 7.83/1.49      ( l1_pre_topc(sK1) ),
% 7.83/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_37,negated_conjecture,
% 7.83/1.49      ( v2_pre_topc(sK1) ),
% 7.83/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_38,negated_conjecture,
% 7.83/1.49      ( ~ v2_struct_0(sK1) ),
% 7.83/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_40,negated_conjecture,
% 7.83/1.49      ( v2_pre_topc(sK0) ),
% 7.83/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_41,negated_conjecture,
% 7.83/1.49      ( ~ v2_struct_0(sK0) ),
% 7.83/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(contradiction,plain,
% 7.83/1.49      ( $false ),
% 7.83/1.49      inference(minisat,
% 7.83/1.49                [status(thm)],
% 7.83/1.49                [c_29178,c_28417,c_26757,c_21392,c_21154,c_20842,c_20037,
% 7.83/1.49                 c_19940,c_19196,c_19195,c_18380,c_18082,c_8942,c_7796,
% 7.83/1.49                 c_7747,c_7730,c_7729,c_7728,c_7727,c_7216,c_23,c_27,
% 7.83/1.49                 c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_44,
% 7.83/1.49                 c_39,c_40,c_41]) ).
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.83/1.49  
% 7.83/1.49  ------                               Statistics
% 7.83/1.49  
% 7.83/1.49  ------ Selected
% 7.83/1.49  
% 7.83/1.49  total_time:                             0.817
% 7.83/1.49  
%------------------------------------------------------------------------------
