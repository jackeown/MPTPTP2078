%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:00 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  234 (4536 expanded)
%              Number of clauses        :  162 (1093 expanded)
%              Number of leaves         :   19 (1893 expanded)
%              Depth                    :   30
%              Number of atoms          : 1249 (62697 expanded)
%              Number of equality atoms :  518 (1876 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X3,X2) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X4,X3)
                            & m1_pre_topc(X3,X2) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
    inference(flattening,[],[f34])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,sK5)),k3_tmap_1(X0,X1,X2,X4,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_pre_topc(X4,X3)
          & m1_pre_topc(X3,X2)
          & m1_pre_topc(X4,X0)
          & ~ v2_struct_0(X4) )
     => ( ? [X5] :
            ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,sK4,X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_pre_topc(sK4,X3)
        & m1_pre_topc(X3,X2)
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_pre_topc(X4,X3)
              & m1_pre_topc(X3,X2)
              & m1_pre_topc(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X4,k3_tmap_1(X0,X1,X2,sK3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_pre_topc(X4,sK3)
            & m1_pre_topc(sK3,X2)
            & m1_pre_topc(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_pre_topc(X4,X3)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,sK2,X3,X5)),k3_tmap_1(X0,X1,sK2,X4,X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                    & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_pre_topc(X4,X3)
                & m1_pre_topc(X3,sK2)
                & m1_pre_topc(X4,X0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
                        ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X4,k3_tmap_1(X0,sK1,X2,X3,X5)),k3_tmap_1(X0,sK1,X2,X4,X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1))
                        & v1_funct_1(X5) )
                    & m1_pre_topc(X4,X3)
                    & m1_pre_topc(X3,X2)
                    & m1_pre_topc(X4,X0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_pre_topc(X4,X3)
                        & m1_pre_topc(X3,X2)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
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
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X4,k3_tmap_1(sK0,X1,X2,X3,X5)),k3_tmap_1(sK0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
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

fof(f42,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK3)
    & m1_pre_topc(sK3,sK2)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f35,f41,f40,f39,f38,f37,f36])).

fof(f74,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f42])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
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
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f30])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_962,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1543,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_962])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_961,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1544,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_961])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_965,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1540,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_965])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_969,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | v2_struct_0(X1_54)
    | v2_struct_0(X0_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X0_54)
    | ~ v1_funct_1(X0_52)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_52,X2_54) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1536,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_52,X2_54)
    | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_969])).

cnf(c_2991,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK1,sK5,X0_54)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1540,c_1536])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_37,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_38,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_39,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_40,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_41,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_42,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_43,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_50,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_51,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_970,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2110,plain,
    ( ~ m1_pre_topc(sK2,X0_54)
    | ~ l1_pre_topc(X0_54)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_2111,plain,
    ( m1_pre_topc(sK2,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2110])).

cnf(c_2113,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2111])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_971,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v2_pre_topc(X1_54)
    | v2_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2441,plain,
    ( ~ m1_pre_topc(sK2,X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X0_54)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_2442,plain,
    ( m1_pre_topc(sK2,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2441])).

cnf(c_2444,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2442])).

cnf(c_3758,plain,
    ( m1_pre_topc(X0_54,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK1,sK5,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2991,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_50,c_51,c_2113,c_2444])).

cnf(c_3759,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK1,sK5,X0_54)
    | m1_pre_topc(X0_54,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3758])).

cnf(c_3766,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_1544,c_3759])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_975,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ r1_tarski(X2_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | m1_subset_1(k2_partfun1(X0_53,X1_53,X0_52,X2_53),k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | k1_xboole_0 = X1_53 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1530,plain,
    ( k1_xboole_0 = X0_53
    | v1_funct_2(X0_52,X1_53,X0_53) != iProver_top
    | r1_tarski(X2_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) != iProver_top
    | m1_subset_1(k2_partfun1(X1_53,X0_53,X0_52,X2_53),k1_zfmisc_1(k2_zfmisc_1(X2_53,X0_53))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_975])).

cnf(c_3776,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3766,c_1530])).

cnf(c_48,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_52,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_967,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | r1_tarski(u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ l1_pre_topc(X1_54) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1845,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_1846,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1845])).

cnf(c_4634,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3776,c_38,c_43,c_48,c_50,c_51,c_52,c_1846,c_2113])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_968,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | v2_struct_0(X1_54)
    | v2_struct_0(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X3_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X3_54)
    | ~ v1_funct_1(X0_52)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1537,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)
    | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_968])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_966,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ m1_pre_topc(X1_54,X2_54)
    | m1_pre_topc(X0_54,X2_54)
    | ~ l1_pre_topc(X2_54)
    | ~ v2_pre_topc(X2_54) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1539,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X1_54,X2_54) != iProver_top
    | m1_pre_topc(X0_54,X2_54) = iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_966])).

cnf(c_1720,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)
    | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1537,c_1539])).

cnf(c_4640,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3))
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4634,c_1720])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_977,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k2_partfun1(X0_53,X1_53,X0_52,X2_53)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1528,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_partfun1(X0_53,X1_53,X0_52,X2_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_977])).

cnf(c_2415,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,X0_53)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1540,c_1528])).

cnf(c_1878,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,X0_53))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_1879,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,X0_53)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1878])).

cnf(c_2836,plain,
    ( v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,X0_53)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2415,c_50,c_52,c_1879])).

cnf(c_3778,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3766,c_2836])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_partfun1(X1,X2,X0,X3),X3,X2)
    | ~ r1_tarski(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_973,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | v1_funct_2(k2_partfun1(X0_53,X1_53,X0_52,X2_53),X2_53,X1_53)
    | ~ r1_tarski(X2_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | k1_xboole_0 = X1_53 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1532,plain,
    ( k1_xboole_0 = X0_53
    | v1_funct_2(X0_52,X1_53,X0_53) != iProver_top
    | v1_funct_2(k2_partfun1(X1_53,X0_53,X0_52,X2_53),X2_53,X0_53) = iProver_top
    | r1_tarski(X2_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_973])).

cnf(c_3777,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3766,c_1532])).

cnf(c_4594,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3777,c_38,c_43,c_48,c_50,c_51,c_52,c_1846,c_2113])).

cnf(c_10,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_371,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_389,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_371])).

cnf(c_948,plain,
    ( v2_struct_0(X0_54)
    | ~ l1_pre_topc(X0_54)
    | u1_struct_0(X0_54) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_389])).

cnf(c_6389,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_6966,plain,
    ( l1_pre_topc(X1_54) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4640,c_38,c_32,c_39,c_40,c_30,c_41,c_43,c_48,c_50,c_51,c_52,c_1846,c_2113,c_3777,c_3778,c_6389])).

cnf(c_6967,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_6966])).

cnf(c_6978,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(sK2,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1544,c_6967])).

cnf(c_7033,plain,
    ( m1_pre_topc(X0_54,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(sK2,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6978,c_37,c_38,c_42,c_43,c_2113,c_2444])).

cnf(c_7034,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(sK2,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(X0_54,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_7033])).

cnf(c_7041,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
    inference(superposition,[status(thm)],[c_1543,c_7034])).

cnf(c_1538,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | r1_tarski(u1_struct_0(X0_54),u1_struct_0(X1_54)) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_967])).

cnf(c_2994,plain,
    ( u1_struct_0(X0_54) = k1_xboole_0
    | k2_partfun1(u1_struct_0(X1_54),u1_struct_0(X0_54),k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),u1_struct_0(X2_54)) = k2_tmap_1(X1_54,X0_54,k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),X2_54)
    | v1_funct_2(X0_52,X0_53,u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | r1_tarski(u1_struct_0(X1_54),X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_1536])).

cnf(c_1053,plain,
    ( u1_struct_0(X0_54) != k1_xboole_0
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_5514,plain,
    ( k2_partfun1(u1_struct_0(X1_54),u1_struct_0(X0_54),k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),u1_struct_0(X2_54)) = k2_tmap_1(X1_54,X0_54,k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),X2_54)
    | v1_funct_2(X0_52,X0_53,u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | r1_tarski(u1_struct_0(X1_54),X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2994,c_1053])).

cnf(c_5515,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),X2_54)
    | v1_funct_2(X0_52,X0_53,u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | r1_tarski(u1_struct_0(X0_54),X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(X1_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5514])).

cnf(c_5532,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),X2_54)
    | v1_funct_2(X0_52,X0_53,u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | r1_tarski(u1_struct_0(X0_54),X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(X1_54)))) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5515,c_1528])).

cnf(c_5537,plain,
    ( u1_struct_0(X0_54) = k1_xboole_0
    | k2_partfun1(u1_struct_0(X1_54),u1_struct_0(X0_54),k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),u1_struct_0(X2_54)) = k2_tmap_1(X1_54,X0_54,k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),X2_54)
    | v1_funct_2(X0_52,X0_53,u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | r1_tarski(u1_struct_0(X1_54),X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1532,c_5532])).

cnf(c_5825,plain,
    ( k2_partfun1(u1_struct_0(X1_54),u1_struct_0(X0_54),k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),u1_struct_0(X2_54)) = k2_tmap_1(X1_54,X0_54,k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),X2_54)
    | v1_funct_2(X0_52,X0_53,u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(X2_54,X1_54) != iProver_top
    | r1_tarski(u1_struct_0(X1_54),X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5537,c_1053])).

cnf(c_5826,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),X2_54)
    | v1_funct_2(X0_52,X0_53,u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | r1_tarski(u1_struct_0(X0_54),X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(X1_54)))) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5825])).

cnf(c_5841,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),X1_54)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | r1_tarski(u1_struct_0(X0_54),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1540,c_5826])).

cnf(c_6172,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),X1_54)
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | r1_tarski(u1_struct_0(X0_54),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5841,c_39,c_40,c_41,c_50,c_51])).

cnf(c_6173,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),X1_54)
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | r1_tarski(u1_struct_0(X0_54),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_6172])).

cnf(c_6184,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),X1_54)
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1538,c_6173])).

cnf(c_6189,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),X1_54)
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6184,c_38,c_43,c_2113])).

cnf(c_6190,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),X1_54)
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_6189])).

cnf(c_6201,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)),u1_struct_0(X0_54)) = k2_tmap_1(sK3,sK1,k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)),X0_54)
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1544,c_6190])).

cnf(c_6219,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_54)
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6201,c_3766])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_44,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_45,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2105,plain,
    ( ~ m1_pre_topc(sK3,X0_54)
    | ~ l1_pre_topc(X0_54)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_2106,plain,
    ( m1_pre_topc(sK3,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2105])).

cnf(c_2108,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2106])).

cnf(c_2436,plain,
    ( ~ m1_pre_topc(sK3,X0_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X0_54)
    | v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_2437,plain,
    ( m1_pre_topc(sK3,X0_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2436])).

cnf(c_2439,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2437])).

cnf(c_6291,plain,
    ( m1_pre_topc(X0_54,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6219,c_37,c_38,c_44,c_45,c_2108,c_2439])).

cnf(c_6292,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_54)
    | m1_pre_topc(X0_54,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6291])).

cnf(c_6299,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
    inference(superposition,[status(thm)],[c_1543,c_6292])).

cnf(c_7042,plain,
    ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
    inference(light_normalisation,[status(thm)],[c_7041,c_6299])).

cnf(c_956,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1549,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_956])).

cnf(c_3556,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK2,X0_54,sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1540,c_1720])).

cnf(c_3869,plain,
    ( l1_pre_topc(X1_54) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK2,X0_54,sK5)
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3556,c_39,c_40,c_41,c_50,c_51])).

cnf(c_3870,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK2,X0_54,sK5)
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3869])).

cnf(c_3881,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK2,X0_54,sK5)
    | m1_pre_topc(X0_54,sK2) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1549,c_3870])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_36,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3886,plain,
    ( m1_pre_topc(X0_54,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK2,X0_54,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3881,c_36,c_37,c_38])).

cnf(c_3887,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK2,X0_54,sK5)
    | m1_pre_topc(X0_54,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3886])).

cnf(c_3894,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1544,c_3887])).

cnf(c_3899,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
    inference(light_normalisation,[status(thm)],[c_3894,c_3766])).

cnf(c_16,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k2_tmap_1(X2,X1,X4,X3)),k2_tmap_1(X2,X1,X4,X0))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_18,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_407,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k3_tmap_1(sK0,sK1,sK2,sK4,sK5) != k2_tmap_1(X1,X2,X0,X4)
    | k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) != k3_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X0,X3))
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X4) != u1_struct_0(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_447,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k3_tmap_1(sK0,sK1,sK2,sK4,sK5) != k2_tmap_1(X1,X2,X0,X4)
    | k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) != k3_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X0,X3))
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X4) != u1_struct_0(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_407,c_17])).

cnf(c_947,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_pre_topc(X3_54,X2_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X0_54)
    | ~ l1_pre_topc(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X1_54)
    | ~ v2_pre_topc(X0_54)
    | ~ v1_funct_1(X0_52)
    | u1_struct_0(X1_54) != u1_struct_0(sK1)
    | u1_struct_0(X3_54) != u1_struct_0(sK4)
    | k3_tmap_1(sK0,sK1,sK2,sK4,sK5) != k2_tmap_1(X0_54,X1_54,X0_52,X3_54)
    | k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) != k3_tmap_1(X0_54,X1_54,X2_54,X3_54,k2_tmap_1(X0_54,X1_54,X0_52,X2_54)) ),
    inference(subtyping,[status(esa)],[c_447])).

cnf(c_1558,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(X1_54) != u1_struct_0(sK4)
    | k3_tmap_1(sK0,sK1,sK2,sK4,sK5) != k2_tmap_1(X2_54,X0_54,X0_52,X1_54)
    | k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) != k3_tmap_1(X2_54,X0_54,X3_54,X1_54,k2_tmap_1(X2_54,X0_54,X0_52,X3_54))
    | v1_funct_2(X0_52,u1_struct_0(X2_54),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_3946,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(X1_54) != u1_struct_0(sK4)
    | k3_tmap_1(X2_54,X0_54,X3_54,X1_54,k2_tmap_1(X2_54,X0_54,X0_52,X3_54)) != k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
    | k3_tmap_1(sK0,sK1,sK2,sK4,sK5) != k2_tmap_1(X2_54,X0_54,X0_52,X1_54)
    | v1_funct_2(X0_52,u1_struct_0(X2_54),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3899,c_1558])).

cnf(c_2582,plain,
    ( m1_pre_topc(sK3,X0_54) != iProver_top
    | m1_pre_topc(sK4,X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_1539])).

cnf(c_3194,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1544,c_2582])).

cnf(c_49,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1857,plain,
    ( ~ m1_pre_topc(sK3,X0_54)
    | m1_pre_topc(sK4,X0_54)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(X0_54)
    | ~ v2_pre_topc(X0_54) ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_2849,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1857])).

cnf(c_2852,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) = iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2849])).

cnf(c_3264,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3194,c_37,c_38,c_43,c_48,c_49,c_2113,c_2444,c_2852])).

cnf(c_3895,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK2,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_3264,c_3887])).

cnf(c_3767,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_3264,c_3759])).

cnf(c_4583,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
    inference(light_normalisation,[status(thm)],[c_3895,c_3767])).

cnf(c_958,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1547,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_958])).

cnf(c_6979,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(X0_54,sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_6967])).

cnf(c_7044,plain,
    ( m1_pre_topc(X0_54,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6979,c_36,c_37,c_38])).

cnf(c_7045,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(X0_54,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_7044])).

cnf(c_7052,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
    inference(superposition,[status(thm)],[c_1543,c_7045])).

cnf(c_7053,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
    inference(light_normalisation,[status(thm)],[c_7052,c_6299])).

cnf(c_9076,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK1)
    | u1_struct_0(X1_54) != u1_struct_0(sK4)
    | k3_tmap_1(X2_54,X0_54,X3_54,X1_54,k2_tmap_1(X2_54,X0_54,X0_52,X3_54)) != k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
    | k2_tmap_1(X2_54,X0_54,X0_52,X1_54) != k2_tmap_1(sK2,sK1,sK5,sK4)
    | v1_funct_2(X0_52,u1_struct_0(X2_54),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(X3_54,X2_54) != iProver_top
    | m1_pre_topc(X1_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) != iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | l1_pre_topc(X2_54) != iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X2_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3946,c_4583,c_7053])).

cnf(c_9097,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | k2_tmap_1(sK2,sK1,sK5,sK4) != k2_tmap_1(sK2,sK1,sK5,sK4)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7042,c_9076])).

cnf(c_10158,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9097])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_46,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10158,c_2444,c_2113,c_52,c_51,c_50,c_49,c_48,c_46,c_44,c_43,c_42,c_41,c_40,c_39,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:47:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.29/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/0.98  
% 3.29/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.29/0.98  
% 3.29/0.98  ------  iProver source info
% 3.29/0.98  
% 3.29/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.29/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.29/0.98  git: non_committed_changes: false
% 3.29/0.98  git: last_make_outside_of_git: false
% 3.29/0.98  
% 3.29/0.98  ------ 
% 3.29/0.98  
% 3.29/0.98  ------ Input Options
% 3.29/0.98  
% 3.29/0.98  --out_options                           all
% 3.29/0.98  --tptp_safe_out                         true
% 3.29/0.98  --problem_path                          ""
% 3.29/0.98  --include_path                          ""
% 3.29/0.98  --clausifier                            res/vclausify_rel
% 3.29/0.98  --clausifier_options                    --mode clausify
% 3.29/0.98  --stdin                                 false
% 3.29/0.98  --stats_out                             all
% 3.29/0.98  
% 3.29/0.98  ------ General Options
% 3.29/0.98  
% 3.29/0.98  --fof                                   false
% 3.29/0.98  --time_out_real                         305.
% 3.29/0.98  --time_out_virtual                      -1.
% 3.29/0.98  --symbol_type_check                     false
% 3.29/0.98  --clausify_out                          false
% 3.29/0.98  --sig_cnt_out                           false
% 3.29/0.98  --trig_cnt_out                          false
% 3.29/0.98  --trig_cnt_out_tolerance                1.
% 3.29/0.98  --trig_cnt_out_sk_spl                   false
% 3.29/0.98  --abstr_cl_out                          false
% 3.29/0.98  
% 3.29/0.98  ------ Global Options
% 3.29/0.98  
% 3.29/0.98  --schedule                              default
% 3.29/0.98  --add_important_lit                     false
% 3.29/0.98  --prop_solver_per_cl                    1000
% 3.29/0.98  --min_unsat_core                        false
% 3.29/0.98  --soft_assumptions                      false
% 3.29/0.98  --soft_lemma_size                       3
% 3.29/0.98  --prop_impl_unit_size                   0
% 3.29/0.98  --prop_impl_unit                        []
% 3.29/0.98  --share_sel_clauses                     true
% 3.29/0.98  --reset_solvers                         false
% 3.29/0.98  --bc_imp_inh                            [conj_cone]
% 3.29/0.98  --conj_cone_tolerance                   3.
% 3.29/0.98  --extra_neg_conj                        none
% 3.29/0.98  --large_theory_mode                     true
% 3.29/0.98  --prolific_symb_bound                   200
% 3.29/0.98  --lt_threshold                          2000
% 3.29/0.98  --clause_weak_htbl                      true
% 3.29/0.98  --gc_record_bc_elim                     false
% 3.29/0.98  
% 3.29/0.98  ------ Preprocessing Options
% 3.29/0.98  
% 3.29/0.98  --preprocessing_flag                    true
% 3.29/0.98  --time_out_prep_mult                    0.1
% 3.29/0.98  --splitting_mode                        input
% 3.29/0.98  --splitting_grd                         true
% 3.29/0.98  --splitting_cvd                         false
% 3.29/0.98  --splitting_cvd_svl                     false
% 3.29/0.98  --splitting_nvd                         32
% 3.29/0.98  --sub_typing                            true
% 3.29/0.98  --prep_gs_sim                           true
% 3.29/0.98  --prep_unflatten                        true
% 3.29/0.98  --prep_res_sim                          true
% 3.29/0.98  --prep_upred                            true
% 3.29/0.98  --prep_sem_filter                       exhaustive
% 3.29/0.98  --prep_sem_filter_out                   false
% 3.29/0.98  --pred_elim                             true
% 3.29/0.98  --res_sim_input                         true
% 3.29/0.98  --eq_ax_congr_red                       true
% 3.29/0.98  --pure_diseq_elim                       true
% 3.29/0.98  --brand_transform                       false
% 3.29/0.98  --non_eq_to_eq                          false
% 3.29/0.98  --prep_def_merge                        true
% 3.29/0.98  --prep_def_merge_prop_impl              false
% 3.29/0.98  --prep_def_merge_mbd                    true
% 3.29/0.98  --prep_def_merge_tr_red                 false
% 3.29/0.98  --prep_def_merge_tr_cl                  false
% 3.29/0.98  --smt_preprocessing                     true
% 3.29/0.98  --smt_ac_axioms                         fast
% 3.29/0.98  --preprocessed_out                      false
% 3.29/0.98  --preprocessed_stats                    false
% 3.29/0.98  
% 3.29/0.98  ------ Abstraction refinement Options
% 3.29/0.98  
% 3.29/0.98  --abstr_ref                             []
% 3.29/0.98  --abstr_ref_prep                        false
% 3.29/0.98  --abstr_ref_until_sat                   false
% 3.29/0.98  --abstr_ref_sig_restrict                funpre
% 3.29/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/0.98  --abstr_ref_under                       []
% 3.29/0.98  
% 3.29/0.98  ------ SAT Options
% 3.29/0.98  
% 3.29/0.98  --sat_mode                              false
% 3.29/0.98  --sat_fm_restart_options                ""
% 3.29/0.98  --sat_gr_def                            false
% 3.29/0.98  --sat_epr_types                         true
% 3.29/0.98  --sat_non_cyclic_types                  false
% 3.29/0.98  --sat_finite_models                     false
% 3.29/0.98  --sat_fm_lemmas                         false
% 3.29/0.98  --sat_fm_prep                           false
% 3.29/0.98  --sat_fm_uc_incr                        true
% 3.29/0.98  --sat_out_model                         small
% 3.29/0.98  --sat_out_clauses                       false
% 3.29/0.98  
% 3.29/0.98  ------ QBF Options
% 3.29/0.98  
% 3.29/0.98  --qbf_mode                              false
% 3.29/0.98  --qbf_elim_univ                         false
% 3.29/0.98  --qbf_dom_inst                          none
% 3.29/0.98  --qbf_dom_pre_inst                      false
% 3.29/0.98  --qbf_sk_in                             false
% 3.29/0.98  --qbf_pred_elim                         true
% 3.29/0.98  --qbf_split                             512
% 3.29/0.98  
% 3.29/0.98  ------ BMC1 Options
% 3.29/0.98  
% 3.29/0.98  --bmc1_incremental                      false
% 3.29/0.98  --bmc1_axioms                           reachable_all
% 3.29/0.98  --bmc1_min_bound                        0
% 3.29/0.98  --bmc1_max_bound                        -1
% 3.29/0.98  --bmc1_max_bound_default                -1
% 3.29/0.98  --bmc1_symbol_reachability              true
% 3.29/0.98  --bmc1_property_lemmas                  false
% 3.29/0.98  --bmc1_k_induction                      false
% 3.29/0.98  --bmc1_non_equiv_states                 false
% 3.29/0.98  --bmc1_deadlock                         false
% 3.29/0.98  --bmc1_ucm                              false
% 3.29/0.98  --bmc1_add_unsat_core                   none
% 3.29/0.98  --bmc1_unsat_core_children              false
% 3.29/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/0.98  --bmc1_out_stat                         full
% 3.29/0.98  --bmc1_ground_init                      false
% 3.29/0.98  --bmc1_pre_inst_next_state              false
% 3.29/0.98  --bmc1_pre_inst_state                   false
% 3.29/0.98  --bmc1_pre_inst_reach_state             false
% 3.29/0.98  --bmc1_out_unsat_core                   false
% 3.29/0.98  --bmc1_aig_witness_out                  false
% 3.29/0.98  --bmc1_verbose                          false
% 3.29/0.98  --bmc1_dump_clauses_tptp                false
% 3.29/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.29/0.98  --bmc1_dump_file                        -
% 3.29/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.29/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.29/0.98  --bmc1_ucm_extend_mode                  1
% 3.29/0.98  --bmc1_ucm_init_mode                    2
% 3.29/0.98  --bmc1_ucm_cone_mode                    none
% 3.29/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.29/0.98  --bmc1_ucm_relax_model                  4
% 3.29/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.29/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/0.98  --bmc1_ucm_layered_model                none
% 3.29/0.98  --bmc1_ucm_max_lemma_size               10
% 3.29/0.98  
% 3.29/0.98  ------ AIG Options
% 3.29/0.98  
% 3.29/0.98  --aig_mode                              false
% 3.29/0.98  
% 3.29/0.98  ------ Instantiation Options
% 3.29/0.98  
% 3.29/0.98  --instantiation_flag                    true
% 3.29/0.98  --inst_sos_flag                         false
% 3.29/0.98  --inst_sos_phase                        true
% 3.29/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/0.98  --inst_lit_sel_side                     num_symb
% 3.29/0.98  --inst_solver_per_active                1400
% 3.29/0.98  --inst_solver_calls_frac                1.
% 3.29/0.98  --inst_passive_queue_type               priority_queues
% 3.29/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/0.98  --inst_passive_queues_freq              [25;2]
% 3.29/0.98  --inst_dismatching                      true
% 3.29/0.98  --inst_eager_unprocessed_to_passive     true
% 3.29/0.98  --inst_prop_sim_given                   true
% 3.29/0.98  --inst_prop_sim_new                     false
% 3.29/0.98  --inst_subs_new                         false
% 3.29/0.98  --inst_eq_res_simp                      false
% 3.29/0.98  --inst_subs_given                       false
% 3.29/0.98  --inst_orphan_elimination               true
% 3.29/0.98  --inst_learning_loop_flag               true
% 3.29/0.98  --inst_learning_start                   3000
% 3.29/0.98  --inst_learning_factor                  2
% 3.29/0.98  --inst_start_prop_sim_after_learn       3
% 3.29/0.98  --inst_sel_renew                        solver
% 3.29/0.98  --inst_lit_activity_flag                true
% 3.29/0.98  --inst_restr_to_given                   false
% 3.29/0.98  --inst_activity_threshold               500
% 3.29/0.98  --inst_out_proof                        true
% 3.29/0.98  
% 3.29/0.98  ------ Resolution Options
% 3.29/0.98  
% 3.29/0.98  --resolution_flag                       true
% 3.29/0.98  --res_lit_sel                           adaptive
% 3.29/0.98  --res_lit_sel_side                      none
% 3.29/0.98  --res_ordering                          kbo
% 3.29/0.98  --res_to_prop_solver                    active
% 3.29/0.98  --res_prop_simpl_new                    false
% 3.29/0.98  --res_prop_simpl_given                  true
% 3.29/0.98  --res_passive_queue_type                priority_queues
% 3.29/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/0.98  --res_passive_queues_freq               [15;5]
% 3.29/0.98  --res_forward_subs                      full
% 3.29/0.98  --res_backward_subs                     full
% 3.29/0.98  --res_forward_subs_resolution           true
% 3.29/0.98  --res_backward_subs_resolution          true
% 3.29/0.98  --res_orphan_elimination                true
% 3.29/0.98  --res_time_limit                        2.
% 3.29/0.98  --res_out_proof                         true
% 3.29/0.98  
% 3.29/0.98  ------ Superposition Options
% 3.29/0.98  
% 3.29/0.98  --superposition_flag                    true
% 3.29/0.98  --sup_passive_queue_type                priority_queues
% 3.29/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.29/0.98  --demod_completeness_check              fast
% 3.29/0.98  --demod_use_ground                      true
% 3.29/0.98  --sup_to_prop_solver                    passive
% 3.29/0.98  --sup_prop_simpl_new                    true
% 3.29/0.98  --sup_prop_simpl_given                  true
% 3.29/0.98  --sup_fun_splitting                     false
% 3.29/0.98  --sup_smt_interval                      50000
% 3.29/0.98  
% 3.29/0.98  ------ Superposition Simplification Setup
% 3.29/0.98  
% 3.29/0.98  --sup_indices_passive                   []
% 3.29/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.98  --sup_full_bw                           [BwDemod]
% 3.29/0.98  --sup_immed_triv                        [TrivRules]
% 3.29/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.98  --sup_immed_bw_main                     []
% 3.29/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.98  
% 3.29/0.98  ------ Combination Options
% 3.29/0.98  
% 3.29/0.98  --comb_res_mult                         3
% 3.29/0.98  --comb_sup_mult                         2
% 3.29/0.98  --comb_inst_mult                        10
% 3.29/0.98  
% 3.29/0.98  ------ Debug Options
% 3.29/0.98  
% 3.29/0.98  --dbg_backtrace                         false
% 3.29/0.98  --dbg_dump_prop_clauses                 false
% 3.29/0.98  --dbg_dump_prop_clauses_file            -
% 3.29/0.98  --dbg_out_stat                          false
% 3.29/0.98  ------ Parsing...
% 3.29/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.29/0.98  
% 3.29/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.29/0.98  
% 3.29/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.29/0.98  
% 3.29/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.29/0.98  ------ Proving...
% 3.29/0.98  ------ Problem Properties 
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  clauses                                 32
% 3.29/0.98  conjectures                             17
% 3.29/0.98  EPR                                     18
% 3.29/0.98  Horn                                    27
% 3.29/0.98  unary                                   17
% 3.29/0.98  binary                                  0
% 3.29/0.98  lits                                    109
% 3.29/0.98  lits eq                                 9
% 3.29/0.98  fd_pure                                 0
% 3.29/0.98  fd_pseudo                               0
% 3.29/0.98  fd_cond                                 2
% 3.29/0.98  fd_pseudo_cond                          0
% 3.29/0.98  AC symbols                              0
% 3.29/0.98  
% 3.29/0.98  ------ Schedule dynamic 5 is on 
% 3.29/0.98  
% 3.29/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  ------ 
% 3.29/0.98  Current options:
% 3.29/0.98  ------ 
% 3.29/0.98  
% 3.29/0.98  ------ Input Options
% 3.29/0.98  
% 3.29/0.98  --out_options                           all
% 3.29/0.98  --tptp_safe_out                         true
% 3.29/0.98  --problem_path                          ""
% 3.29/0.98  --include_path                          ""
% 3.29/0.98  --clausifier                            res/vclausify_rel
% 3.29/0.98  --clausifier_options                    --mode clausify
% 3.29/0.98  --stdin                                 false
% 3.29/0.98  --stats_out                             all
% 3.29/0.98  
% 3.29/0.98  ------ General Options
% 3.29/0.98  
% 3.29/0.98  --fof                                   false
% 3.29/0.98  --time_out_real                         305.
% 3.29/0.98  --time_out_virtual                      -1.
% 3.29/0.98  --symbol_type_check                     false
% 3.29/0.98  --clausify_out                          false
% 3.29/0.98  --sig_cnt_out                           false
% 3.29/0.98  --trig_cnt_out                          false
% 3.29/0.98  --trig_cnt_out_tolerance                1.
% 3.29/0.98  --trig_cnt_out_sk_spl                   false
% 3.29/0.98  --abstr_cl_out                          false
% 3.29/0.98  
% 3.29/0.98  ------ Global Options
% 3.29/0.98  
% 3.29/0.98  --schedule                              default
% 3.29/0.98  --add_important_lit                     false
% 3.29/0.98  --prop_solver_per_cl                    1000
% 3.29/0.98  --min_unsat_core                        false
% 3.29/0.98  --soft_assumptions                      false
% 3.29/0.98  --soft_lemma_size                       3
% 3.29/0.98  --prop_impl_unit_size                   0
% 3.29/0.98  --prop_impl_unit                        []
% 3.29/0.98  --share_sel_clauses                     true
% 3.29/0.98  --reset_solvers                         false
% 3.29/0.98  --bc_imp_inh                            [conj_cone]
% 3.29/0.98  --conj_cone_tolerance                   3.
% 3.29/0.98  --extra_neg_conj                        none
% 3.29/0.98  --large_theory_mode                     true
% 3.29/0.98  --prolific_symb_bound                   200
% 3.29/0.98  --lt_threshold                          2000
% 3.29/0.98  --clause_weak_htbl                      true
% 3.29/0.98  --gc_record_bc_elim                     false
% 3.29/0.98  
% 3.29/0.98  ------ Preprocessing Options
% 3.29/0.98  
% 3.29/0.98  --preprocessing_flag                    true
% 3.29/0.98  --time_out_prep_mult                    0.1
% 3.29/0.98  --splitting_mode                        input
% 3.29/0.98  --splitting_grd                         true
% 3.29/0.98  --splitting_cvd                         false
% 3.29/0.98  --splitting_cvd_svl                     false
% 3.29/0.98  --splitting_nvd                         32
% 3.29/0.98  --sub_typing                            true
% 3.29/0.98  --prep_gs_sim                           true
% 3.29/0.98  --prep_unflatten                        true
% 3.29/0.98  --prep_res_sim                          true
% 3.29/0.98  --prep_upred                            true
% 3.29/0.98  --prep_sem_filter                       exhaustive
% 3.29/0.98  --prep_sem_filter_out                   false
% 3.29/0.98  --pred_elim                             true
% 3.29/0.98  --res_sim_input                         true
% 3.29/0.98  --eq_ax_congr_red                       true
% 3.29/0.98  --pure_diseq_elim                       true
% 3.29/0.98  --brand_transform                       false
% 3.29/0.98  --non_eq_to_eq                          false
% 3.29/0.98  --prep_def_merge                        true
% 3.29/0.98  --prep_def_merge_prop_impl              false
% 3.29/0.98  --prep_def_merge_mbd                    true
% 3.29/0.98  --prep_def_merge_tr_red                 false
% 3.29/0.98  --prep_def_merge_tr_cl                  false
% 3.29/0.98  --smt_preprocessing                     true
% 3.29/0.98  --smt_ac_axioms                         fast
% 3.29/0.98  --preprocessed_out                      false
% 3.29/0.98  --preprocessed_stats                    false
% 3.29/0.98  
% 3.29/0.98  ------ Abstraction refinement Options
% 3.29/0.98  
% 3.29/0.98  --abstr_ref                             []
% 3.29/0.98  --abstr_ref_prep                        false
% 3.29/0.98  --abstr_ref_until_sat                   false
% 3.29/0.98  --abstr_ref_sig_restrict                funpre
% 3.29/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/0.98  --abstr_ref_under                       []
% 3.29/0.98  
% 3.29/0.98  ------ SAT Options
% 3.29/0.98  
% 3.29/0.98  --sat_mode                              false
% 3.29/0.98  --sat_fm_restart_options                ""
% 3.29/0.98  --sat_gr_def                            false
% 3.29/0.98  --sat_epr_types                         true
% 3.29/0.98  --sat_non_cyclic_types                  false
% 3.29/0.98  --sat_finite_models                     false
% 3.29/0.98  --sat_fm_lemmas                         false
% 3.29/0.98  --sat_fm_prep                           false
% 3.29/0.98  --sat_fm_uc_incr                        true
% 3.29/0.98  --sat_out_model                         small
% 3.29/0.98  --sat_out_clauses                       false
% 3.29/0.98  
% 3.29/0.98  ------ QBF Options
% 3.29/0.98  
% 3.29/0.98  --qbf_mode                              false
% 3.29/0.98  --qbf_elim_univ                         false
% 3.29/0.98  --qbf_dom_inst                          none
% 3.29/0.98  --qbf_dom_pre_inst                      false
% 3.29/0.98  --qbf_sk_in                             false
% 3.29/0.98  --qbf_pred_elim                         true
% 3.29/0.98  --qbf_split                             512
% 3.29/0.98  
% 3.29/0.98  ------ BMC1 Options
% 3.29/0.98  
% 3.29/0.98  --bmc1_incremental                      false
% 3.29/0.98  --bmc1_axioms                           reachable_all
% 3.29/0.98  --bmc1_min_bound                        0
% 3.29/0.98  --bmc1_max_bound                        -1
% 3.29/0.98  --bmc1_max_bound_default                -1
% 3.29/0.98  --bmc1_symbol_reachability              true
% 3.29/0.98  --bmc1_property_lemmas                  false
% 3.29/0.98  --bmc1_k_induction                      false
% 3.29/0.98  --bmc1_non_equiv_states                 false
% 3.29/0.98  --bmc1_deadlock                         false
% 3.29/0.98  --bmc1_ucm                              false
% 3.29/0.98  --bmc1_add_unsat_core                   none
% 3.29/0.98  --bmc1_unsat_core_children              false
% 3.29/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/0.98  --bmc1_out_stat                         full
% 3.29/0.98  --bmc1_ground_init                      false
% 3.29/0.98  --bmc1_pre_inst_next_state              false
% 3.29/0.98  --bmc1_pre_inst_state                   false
% 3.29/0.98  --bmc1_pre_inst_reach_state             false
% 3.29/0.98  --bmc1_out_unsat_core                   false
% 3.29/0.98  --bmc1_aig_witness_out                  false
% 3.29/0.98  --bmc1_verbose                          false
% 3.29/0.98  --bmc1_dump_clauses_tptp                false
% 3.29/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.29/0.98  --bmc1_dump_file                        -
% 3.29/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.29/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.29/0.98  --bmc1_ucm_extend_mode                  1
% 3.29/0.98  --bmc1_ucm_init_mode                    2
% 3.29/0.98  --bmc1_ucm_cone_mode                    none
% 3.29/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.29/0.98  --bmc1_ucm_relax_model                  4
% 3.29/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.29/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/0.98  --bmc1_ucm_layered_model                none
% 3.29/0.98  --bmc1_ucm_max_lemma_size               10
% 3.29/0.98  
% 3.29/0.98  ------ AIG Options
% 3.29/0.98  
% 3.29/0.98  --aig_mode                              false
% 3.29/0.98  
% 3.29/0.98  ------ Instantiation Options
% 3.29/0.98  
% 3.29/0.98  --instantiation_flag                    true
% 3.29/0.98  --inst_sos_flag                         false
% 3.29/0.98  --inst_sos_phase                        true
% 3.29/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/0.98  --inst_lit_sel_side                     none
% 3.29/0.98  --inst_solver_per_active                1400
% 3.29/0.98  --inst_solver_calls_frac                1.
% 3.29/0.98  --inst_passive_queue_type               priority_queues
% 3.29/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/0.98  --inst_passive_queues_freq              [25;2]
% 3.29/0.98  --inst_dismatching                      true
% 3.29/0.98  --inst_eager_unprocessed_to_passive     true
% 3.29/0.98  --inst_prop_sim_given                   true
% 3.29/0.98  --inst_prop_sim_new                     false
% 3.29/0.98  --inst_subs_new                         false
% 3.29/0.98  --inst_eq_res_simp                      false
% 3.29/0.98  --inst_subs_given                       false
% 3.29/0.98  --inst_orphan_elimination               true
% 3.29/0.98  --inst_learning_loop_flag               true
% 3.29/0.98  --inst_learning_start                   3000
% 3.29/0.98  --inst_learning_factor                  2
% 3.29/0.98  --inst_start_prop_sim_after_learn       3
% 3.29/0.98  --inst_sel_renew                        solver
% 3.29/0.98  --inst_lit_activity_flag                true
% 3.29/0.98  --inst_restr_to_given                   false
% 3.29/0.98  --inst_activity_threshold               500
% 3.29/0.98  --inst_out_proof                        true
% 3.29/0.98  
% 3.29/0.98  ------ Resolution Options
% 3.29/0.98  
% 3.29/0.98  --resolution_flag                       false
% 3.29/0.98  --res_lit_sel                           adaptive
% 3.29/0.98  --res_lit_sel_side                      none
% 3.29/0.98  --res_ordering                          kbo
% 3.29/0.98  --res_to_prop_solver                    active
% 3.29/0.98  --res_prop_simpl_new                    false
% 3.29/0.98  --res_prop_simpl_given                  true
% 3.29/0.98  --res_passive_queue_type                priority_queues
% 3.29/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/0.98  --res_passive_queues_freq               [15;5]
% 3.29/0.98  --res_forward_subs                      full
% 3.29/0.98  --res_backward_subs                     full
% 3.29/0.98  --res_forward_subs_resolution           true
% 3.29/0.98  --res_backward_subs_resolution          true
% 3.29/0.98  --res_orphan_elimination                true
% 3.29/0.98  --res_time_limit                        2.
% 3.29/0.98  --res_out_proof                         true
% 3.29/0.98  
% 3.29/0.98  ------ Superposition Options
% 3.29/0.98  
% 3.29/0.98  --superposition_flag                    true
% 3.29/0.98  --sup_passive_queue_type                priority_queues
% 3.29/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.29/0.98  --demod_completeness_check              fast
% 3.29/0.98  --demod_use_ground                      true
% 3.29/0.98  --sup_to_prop_solver                    passive
% 3.29/0.98  --sup_prop_simpl_new                    true
% 3.29/0.98  --sup_prop_simpl_given                  true
% 3.29/0.98  --sup_fun_splitting                     false
% 3.29/0.98  --sup_smt_interval                      50000
% 3.29/0.98  
% 3.29/0.98  ------ Superposition Simplification Setup
% 3.29/0.98  
% 3.29/0.98  --sup_indices_passive                   []
% 3.29/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.98  --sup_full_bw                           [BwDemod]
% 3.29/0.98  --sup_immed_triv                        [TrivRules]
% 3.29/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.98  --sup_immed_bw_main                     []
% 3.29/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/0.98  
% 3.29/0.98  ------ Combination Options
% 3.29/0.98  
% 3.29/0.98  --comb_res_mult                         3
% 3.29/0.98  --comb_sup_mult                         2
% 3.29/0.98  --comb_inst_mult                        10
% 3.29/0.98  
% 3.29/0.98  ------ Debug Options
% 3.29/0.98  
% 3.29/0.98  --dbg_backtrace                         false
% 3.29/0.98  --dbg_dump_prop_clauses                 false
% 3.29/0.98  --dbg_dump_prop_clauses_file            -
% 3.29/0.98  --dbg_out_stat                          false
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  ------ Proving...
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  % SZS status Theorem for theBenchmark.p
% 3.29/0.98  
% 3.29/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.29/0.98  
% 3.29/0.98  fof(f13,conjecture,(
% 3.29/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f14,negated_conjecture,(
% 3.29/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 3.29/0.98    inference(negated_conjecture,[],[f13])).
% 3.29/0.98  
% 3.29/0.98  fof(f34,plain,(
% 3.29/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.29/0.98    inference(ennf_transformation,[],[f14])).
% 3.29/0.98  
% 3.29/0.98  fof(f35,plain,(
% 3.29/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.29/0.98    inference(flattening,[],[f34])).
% 3.29/0.98  
% 3.29/0.98  fof(f41,plain,(
% 3.29/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,sK5)),k3_tmap_1(X0,X1,X2,X4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 3.29/0.98    introduced(choice_axiom,[])).
% 3.29/0.98  
% 3.29/0.98  fof(f40,plain,(
% 3.29/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (? [X5] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,sK4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(sK4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.29/0.98    introduced(choice_axiom,[])).
% 3.29/0.98  
% 3.29/0.98  fof(f39,plain,(
% 3.29/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X4,k3_tmap_1(X0,X1,X2,sK3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK3) & m1_pre_topc(sK3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.29/0.98    introduced(choice_axiom,[])).
% 3.29/0.98  
% 3.29/0.98  fof(f38,plain,(
% 3.29/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,sK2,X3,X5)),k3_tmap_1(X0,X1,sK2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,sK2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.29/0.98    introduced(choice_axiom,[])).
% 3.29/0.98  
% 3.29/0.98  fof(f37,plain,(
% 3.29/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X4,k3_tmap_1(X0,sK1,X2,X3,X5)),k3_tmap_1(X0,sK1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.29/0.98    introduced(choice_axiom,[])).
% 3.29/0.98  
% 3.29/0.98  fof(f36,plain,(
% 3.29/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X4,k3_tmap_1(sK0,X1,X2,X3,X5)),k3_tmap_1(sK0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.29/0.98    introduced(choice_axiom,[])).
% 3.29/0.98  
% 3.29/0.98  fof(f42,plain,(
% 3.29/0.98    (((((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK3) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.29/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f35,f41,f40,f39,f38,f37,f36])).
% 3.29/0.98  
% 3.29/0.98  fof(f74,plain,(
% 3.29/0.98    m1_pre_topc(sK4,sK3)),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f73,plain,(
% 3.29/0.98    m1_pre_topc(sK3,sK2)),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f77,plain,(
% 3.29/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f8,axiom,(
% 3.29/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f25,plain,(
% 3.29/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.29/0.98    inference(ennf_transformation,[],[f8])).
% 3.29/0.98  
% 3.29/0.98  fof(f26,plain,(
% 3.29/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.29/0.98    inference(flattening,[],[f25])).
% 3.29/0.98  
% 3.29/0.98  fof(f56,plain,(
% 3.29/0.98    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f26])).
% 3.29/0.98  
% 3.29/0.98  fof(f62,plain,(
% 3.29/0.98    v2_pre_topc(sK0)),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f63,plain,(
% 3.29/0.98    l1_pre_topc(sK0)),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f64,plain,(
% 3.29/0.98    ~v2_struct_0(sK1)),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f65,plain,(
% 3.29/0.98    v2_pre_topc(sK1)),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f66,plain,(
% 3.29/0.98    l1_pre_topc(sK1)),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f67,plain,(
% 3.29/0.98    ~v2_struct_0(sK2)),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f68,plain,(
% 3.29/0.98    m1_pre_topc(sK2,sK0)),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f75,plain,(
% 3.29/0.98    v1_funct_1(sK5)),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f76,plain,(
% 3.29/0.98    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f6,axiom,(
% 3.29/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f22,plain,(
% 3.29/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.29/0.98    inference(ennf_transformation,[],[f6])).
% 3.29/0.98  
% 3.29/0.98  fof(f54,plain,(
% 3.29/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f22])).
% 3.29/0.98  
% 3.29/0.98  fof(f4,axiom,(
% 3.29/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f19,plain,(
% 3.29/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.29/0.98    inference(ennf_transformation,[],[f4])).
% 3.29/0.98  
% 3.29/0.98  fof(f20,plain,(
% 3.29/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.29/0.98    inference(flattening,[],[f19])).
% 3.29/0.98  
% 3.29/0.98  fof(f52,plain,(
% 3.29/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f20])).
% 3.29/0.98  
% 3.29/0.98  fof(f3,axiom,(
% 3.29/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f17,plain,(
% 3.29/0.98    ! [X0,X1,X2,X3] : ((((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.29/0.98    inference(ennf_transformation,[],[f3])).
% 3.29/0.98  
% 3.29/0.98  fof(f18,plain,(
% 3.29/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.29/0.98    inference(flattening,[],[f17])).
% 3.29/0.98  
% 3.29/0.98  fof(f50,plain,(
% 3.29/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | k1_xboole_0 = X1 | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f18])).
% 3.29/0.98  
% 3.29/0.98  fof(f10,axiom,(
% 3.29/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f29,plain,(
% 3.29/0.98    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.29/0.98    inference(ennf_transformation,[],[f10])).
% 3.29/0.98  
% 3.29/0.98  fof(f58,plain,(
% 3.29/0.98    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f29])).
% 3.29/0.98  
% 3.29/0.98  fof(f9,axiom,(
% 3.29/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f27,plain,(
% 3.29/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.29/0.98    inference(ennf_transformation,[],[f9])).
% 3.29/0.98  
% 3.29/0.98  fof(f28,plain,(
% 3.29/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.29/0.98    inference(flattening,[],[f27])).
% 3.29/0.98  
% 3.29/0.98  fof(f57,plain,(
% 3.29/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f28])).
% 3.29/0.98  
% 3.29/0.98  fof(f12,axiom,(
% 3.29/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f32,plain,(
% 3.29/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.29/0.98    inference(ennf_transformation,[],[f12])).
% 3.29/0.98  
% 3.29/0.98  fof(f33,plain,(
% 3.29/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.29/0.98    inference(flattening,[],[f32])).
% 3.29/0.98  
% 3.29/0.98  fof(f60,plain,(
% 3.29/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f33])).
% 3.29/0.98  
% 3.29/0.98  fof(f2,axiom,(
% 3.29/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f15,plain,(
% 3.29/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.29/0.98    inference(ennf_transformation,[],[f2])).
% 3.29/0.98  
% 3.29/0.98  fof(f16,plain,(
% 3.29/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.29/0.98    inference(flattening,[],[f15])).
% 3.29/0.98  
% 3.29/0.98  fof(f44,plain,(
% 3.29/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f16])).
% 3.29/0.98  
% 3.29/0.98  fof(f48,plain,(
% 3.29/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | k1_xboole_0 = X1 | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f18])).
% 3.29/0.98  
% 3.29/0.98  fof(f5,axiom,(
% 3.29/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f21,plain,(
% 3.29/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.29/0.98    inference(ennf_transformation,[],[f5])).
% 3.29/0.98  
% 3.29/0.98  fof(f53,plain,(
% 3.29/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f21])).
% 3.29/0.98  
% 3.29/0.98  fof(f1,axiom,(
% 3.29/0.98    v1_xboole_0(k1_xboole_0)),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f43,plain,(
% 3.29/0.98    v1_xboole_0(k1_xboole_0)),
% 3.29/0.98    inference(cnf_transformation,[],[f1])).
% 3.29/0.98  
% 3.29/0.98  fof(f7,axiom,(
% 3.29/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f23,plain,(
% 3.29/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.29/0.98    inference(ennf_transformation,[],[f7])).
% 3.29/0.98  
% 3.29/0.98  fof(f24,plain,(
% 3.29/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.29/0.98    inference(flattening,[],[f23])).
% 3.29/0.98  
% 3.29/0.98  fof(f55,plain,(
% 3.29/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f24])).
% 3.29/0.98  
% 3.29/0.98  fof(f69,plain,(
% 3.29/0.98    ~v2_struct_0(sK3)),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f70,plain,(
% 3.29/0.98    m1_pre_topc(sK3,sK0)),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f61,plain,(
% 3.29/0.98    ~v2_struct_0(sK0)),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f11,axiom,(
% 3.29/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 3.29/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f30,plain,(
% 3.29/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.29/0.98    inference(ennf_transformation,[],[f11])).
% 3.29/0.98  
% 3.29/0.98  fof(f31,plain,(
% 3.29/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.29/0.98    inference(flattening,[],[f30])).
% 3.29/0.98  
% 3.29/0.98  fof(f59,plain,(
% 3.29/0.98    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f31])).
% 3.29/0.98  
% 3.29/0.98  fof(f78,plain,(
% 3.29/0.98    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  fof(f71,plain,(
% 3.29/0.98    ~v2_struct_0(sK4)),
% 3.29/0.98    inference(cnf_transformation,[],[f42])).
% 3.29/0.98  
% 3.29/0.98  cnf(c_22,negated_conjecture,
% 3.29/0.98      ( m1_pre_topc(sK4,sK3) ),
% 3.29/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_962,negated_conjecture,
% 3.29/0.98      ( m1_pre_topc(sK4,sK3) ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_22]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1543,plain,
% 3.29/0.98      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_962]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_23,negated_conjecture,
% 3.29/0.98      ( m1_pre_topc(sK3,sK2) ),
% 3.29/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_961,negated_conjecture,
% 3.29/0.98      ( m1_pre_topc(sK3,sK2) ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_23]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1544,plain,
% 3.29/0.98      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_961]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_19,negated_conjecture,
% 3.29/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 3.29/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_965,negated_conjecture,
% 3.29/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1540,plain,
% 3.29/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_965]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_13,plain,
% 3.29/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.29/0.98      | ~ m1_pre_topc(X3,X1)
% 3.29/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.29/0.98      | v2_struct_0(X1)
% 3.29/0.98      | v2_struct_0(X2)
% 3.29/0.98      | ~ l1_pre_topc(X1)
% 3.29/0.98      | ~ l1_pre_topc(X2)
% 3.29/0.98      | ~ v2_pre_topc(X1)
% 3.29/0.98      | ~ v2_pre_topc(X2)
% 3.29/0.98      | ~ v1_funct_1(X0)
% 3.29/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.29/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_969,plain,
% 3.29/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.29/0.98      | ~ m1_pre_topc(X2_54,X0_54)
% 3.29/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.29/0.98      | v2_struct_0(X1_54)
% 3.29/0.98      | v2_struct_0(X0_54)
% 3.29/0.98      | ~ l1_pre_topc(X1_54)
% 3.29/0.98      | ~ l1_pre_topc(X0_54)
% 3.29/0.98      | ~ v2_pre_topc(X1_54)
% 3.29/0.98      | ~ v2_pre_topc(X0_54)
% 3.29/0.98      | ~ v1_funct_1(X0_52)
% 3.29/0.98      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_52,X2_54) ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1536,plain,
% 3.29/0.98      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_52,X2_54)
% 3.29/0.98      | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.29/0.98      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 3.29/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 3.29/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.29/0.98      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.98      | v2_pre_topc(X1_54) != iProver_top
% 3.29/0.98      | v2_pre_topc(X0_54) != iProver_top
% 3.29/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_969]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2991,plain,
% 3.29/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK1,sK5,X0_54)
% 3.29/0.98      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.29/0.98      | m1_pre_topc(X0_54,sK2) != iProver_top
% 3.29/0.98      | v2_struct_0(sK2) = iProver_top
% 3.29/0.98      | v2_struct_0(sK1) = iProver_top
% 3.29/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.29/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.29/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.29/0.98      | v2_pre_topc(sK1) != iProver_top
% 3.29/0.98      | v1_funct_1(sK5) != iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_1540,c_1536]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_34,negated_conjecture,
% 3.29/0.98      ( v2_pre_topc(sK0) ),
% 3.29/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_37,plain,
% 3.29/0.98      ( v2_pre_topc(sK0) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_33,negated_conjecture,
% 3.29/0.98      ( l1_pre_topc(sK0) ),
% 3.29/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_38,plain,
% 3.29/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_32,negated_conjecture,
% 3.29/0.98      ( ~ v2_struct_0(sK1) ),
% 3.29/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_39,plain,
% 3.29/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_31,negated_conjecture,
% 3.29/0.98      ( v2_pre_topc(sK1) ),
% 3.29/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_40,plain,
% 3.29/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_30,negated_conjecture,
% 3.29/0.98      ( l1_pre_topc(sK1) ),
% 3.29/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_41,plain,
% 3.29/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_29,negated_conjecture,
% 3.29/0.98      ( ~ v2_struct_0(sK2) ),
% 3.29/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_42,plain,
% 3.29/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_28,negated_conjecture,
% 3.29/0.98      ( m1_pre_topc(sK2,sK0) ),
% 3.29/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_43,plain,
% 3.29/0.98      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_21,negated_conjecture,
% 3.29/0.98      ( v1_funct_1(sK5) ),
% 3.29/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_50,plain,
% 3.29/0.98      ( v1_funct_1(sK5) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_20,negated_conjecture,
% 3.29/0.98      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 3.29/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_51,plain,
% 3.29/0.98      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_11,plain,
% 3.29/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.29/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_970,plain,
% 3.29/0.98      ( ~ m1_pre_topc(X0_54,X1_54)
% 3.29/0.98      | ~ l1_pre_topc(X1_54)
% 3.29/0.98      | l1_pre_topc(X0_54) ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2110,plain,
% 3.29/0.98      ( ~ m1_pre_topc(sK2,X0_54)
% 3.29/0.98      | ~ l1_pre_topc(X0_54)
% 3.29/0.98      | l1_pre_topc(sK2) ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_970]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2111,plain,
% 3.29/0.98      ( m1_pre_topc(sK2,X0_54) != iProver_top
% 3.29/0.98      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.98      | l1_pre_topc(sK2) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_2110]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2113,plain,
% 3.29/0.98      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.29/0.98      | l1_pre_topc(sK2) = iProver_top
% 3.29/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_2111]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_9,plain,
% 3.29/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.29/0.98      | ~ l1_pre_topc(X1)
% 3.29/0.98      | ~ v2_pre_topc(X1)
% 3.29/0.98      | v2_pre_topc(X0) ),
% 3.29/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_971,plain,
% 3.29/0.98      ( ~ m1_pre_topc(X0_54,X1_54)
% 3.29/0.98      | ~ l1_pre_topc(X1_54)
% 3.29/0.98      | ~ v2_pre_topc(X1_54)
% 3.29/0.98      | v2_pre_topc(X0_54) ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2441,plain,
% 3.29/0.98      ( ~ m1_pre_topc(sK2,X0_54)
% 3.29/0.98      | ~ l1_pre_topc(X0_54)
% 3.29/0.98      | ~ v2_pre_topc(X0_54)
% 3.29/0.98      | v2_pre_topc(sK2) ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_971]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2442,plain,
% 3.29/0.98      ( m1_pre_topc(sK2,X0_54) != iProver_top
% 3.29/0.98      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.98      | v2_pre_topc(X0_54) != iProver_top
% 3.29/0.98      | v2_pre_topc(sK2) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_2441]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2444,plain,
% 3.29/0.98      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.29/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.29/0.98      | v2_pre_topc(sK2) = iProver_top
% 3.29/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_2442]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_3758,plain,
% 3.29/0.98      ( m1_pre_topc(X0_54,sK2) != iProver_top
% 3.29/0.98      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK1,sK5,X0_54) ),
% 3.29/0.98      inference(global_propositional_subsumption,
% 3.29/0.98                [status(thm)],
% 3.29/0.98                [c_2991,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_50,c_51,
% 3.29/0.98                 c_2113,c_2444]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_3759,plain,
% 3.29/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k2_tmap_1(sK2,sK1,sK5,X0_54)
% 3.29/0.98      | m1_pre_topc(X0_54,sK2) != iProver_top ),
% 3.29/0.98      inference(renaming,[status(thm)],[c_3758]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_3766,plain,
% 3.29/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_1544,c_3759]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_4,plain,
% 3.29/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.29/0.98      | ~ r1_tarski(X3,X1)
% 3.29/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.98      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.29/0.98      | ~ v1_funct_1(X0)
% 3.29/0.98      | k1_xboole_0 = X2 ),
% 3.29/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_975,plain,
% 3.29/0.98      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 3.29/0.98      | ~ r1_tarski(X2_53,X0_53)
% 3.29/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.29/0.98      | m1_subset_1(k2_partfun1(X0_53,X1_53,X0_52,X2_53),k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53)))
% 3.29/0.98      | ~ v1_funct_1(X0_52)
% 3.29/0.98      | k1_xboole_0 = X1_53 ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1530,plain,
% 3.29/0.98      ( k1_xboole_0 = X0_53
% 3.29/0.98      | v1_funct_2(X0_52,X1_53,X0_53) != iProver_top
% 3.29/0.98      | r1_tarski(X2_53,X1_53) != iProver_top
% 3.29/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) != iProver_top
% 3.29/0.98      | m1_subset_1(k2_partfun1(X1_53,X0_53,X0_52,X2_53),k1_zfmisc_1(k2_zfmisc_1(X2_53,X0_53))) = iProver_top
% 3.29/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_975]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_3776,plain,
% 3.29/0.98      ( u1_struct_0(sK1) = k1_xboole_0
% 3.29/0.98      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.29/0.98      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 3.29/0.98      | m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 3.29/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.29/0.98      | v1_funct_1(sK5) != iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_3766,c_1530]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_48,plain,
% 3.29/0.98      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_52,plain,
% 3.29/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_15,plain,
% 3.29/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.29/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 3.29/0.98      | ~ l1_pre_topc(X1) ),
% 3.29/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_967,plain,
% 3.29/0.98      ( ~ m1_pre_topc(X0_54,X1_54)
% 3.29/0.98      | r1_tarski(u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.29/0.98      | ~ l1_pre_topc(X1_54) ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1845,plain,
% 3.29/0.98      ( ~ m1_pre_topc(sK3,sK2)
% 3.29/0.98      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
% 3.29/0.98      | ~ l1_pre_topc(sK2) ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_967]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1846,plain,
% 3.29/0.98      ( m1_pre_topc(sK3,sK2) != iProver_top
% 3.29/0.98      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
% 3.29/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_1845]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_4634,plain,
% 3.29/0.98      ( u1_struct_0(sK1) = k1_xboole_0
% 3.29/0.98      | m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.29/0.98      inference(global_propositional_subsumption,
% 3.29/0.98                [status(thm)],
% 3.29/0.98                [c_3776,c_38,c_43,c_48,c_50,c_51,c_52,c_1846,c_2113]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_14,plain,
% 3.29/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.29/0.98      | ~ m1_pre_topc(X3,X4)
% 3.29/0.98      | ~ m1_pre_topc(X3,X1)
% 3.29/0.98      | ~ m1_pre_topc(X1,X4)
% 3.29/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.29/0.98      | v2_struct_0(X4)
% 3.29/0.98      | v2_struct_0(X2)
% 3.29/0.98      | ~ l1_pre_topc(X4)
% 3.29/0.98      | ~ l1_pre_topc(X2)
% 3.29/0.98      | ~ v2_pre_topc(X4)
% 3.29/0.98      | ~ v2_pre_topc(X2)
% 3.29/0.98      | ~ v1_funct_1(X0)
% 3.29/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.29/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_968,plain,
% 3.29/0.98      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.29/0.98      | ~ m1_pre_topc(X2_54,X0_54)
% 3.29/0.98      | ~ m1_pre_topc(X2_54,X3_54)
% 3.29/0.98      | ~ m1_pre_topc(X0_54,X3_54)
% 3.29/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.29/0.98      | v2_struct_0(X1_54)
% 3.29/0.98      | v2_struct_0(X3_54)
% 3.29/0.98      | ~ l1_pre_topc(X1_54)
% 3.29/0.98      | ~ l1_pre_topc(X3_54)
% 3.29/0.98      | ~ v2_pre_topc(X1_54)
% 3.29/0.98      | ~ v2_pre_topc(X3_54)
% 3.29/0.98      | ~ v1_funct_1(X0_52)
% 3.29/0.98      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52) ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1537,plain,
% 3.29/0.98      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)
% 3.29/0.98      | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.29/0.98      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 3.29/0.98      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 3.29/0.98      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 3.29/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 3.29/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.98      | v2_struct_0(X3_54) = iProver_top
% 3.29/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.29/0.98      | l1_pre_topc(X3_54) != iProver_top
% 3.29/0.98      | v2_pre_topc(X1_54) != iProver_top
% 3.29/0.98      | v2_pre_topc(X3_54) != iProver_top
% 3.29/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_968]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_17,plain,
% 3.29/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.29/0.98      | ~ m1_pre_topc(X2,X0)
% 3.29/0.98      | m1_pre_topc(X2,X1)
% 3.29/0.98      | ~ l1_pre_topc(X1)
% 3.29/0.98      | ~ v2_pre_topc(X1) ),
% 3.29/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_966,plain,
% 3.29/0.98      ( ~ m1_pre_topc(X0_54,X1_54)
% 3.29/0.98      | ~ m1_pre_topc(X1_54,X2_54)
% 3.29/0.98      | m1_pre_topc(X0_54,X2_54)
% 3.29/0.98      | ~ l1_pre_topc(X2_54)
% 3.29/0.98      | ~ v2_pre_topc(X2_54) ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1539,plain,
% 3.29/0.98      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.29/0.98      | m1_pre_topc(X1_54,X2_54) != iProver_top
% 3.29/0.98      | m1_pre_topc(X0_54,X2_54) = iProver_top
% 3.29/0.98      | l1_pre_topc(X2_54) != iProver_top
% 3.29/0.98      | v2_pre_topc(X2_54) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_966]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1720,plain,
% 3.29/0.98      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)
% 3.29/0.98      | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.29/0.98      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 3.29/0.98      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 3.29/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 3.29/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.98      | v2_struct_0(X3_54) = iProver_top
% 3.29/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.29/0.98      | l1_pre_topc(X3_54) != iProver_top
% 3.29/0.98      | v2_pre_topc(X1_54) != iProver_top
% 3.29/0.98      | v2_pre_topc(X3_54) != iProver_top
% 3.29/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 3.29/0.98      inference(forward_subsumption_resolution,
% 3.29/0.98                [status(thm)],
% 3.29/0.98                [c_1537,c_1539]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_4640,plain,
% 3.29/0.98      ( u1_struct_0(sK1) = k1_xboole_0
% 3.29/0.98      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3))
% 3.29/0.98      | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.29/0.98      | m1_pre_topc(X0_54,sK3) != iProver_top
% 3.29/0.98      | m1_pre_topc(sK3,X1_54) != iProver_top
% 3.29/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.98      | v2_struct_0(sK1) = iProver_top
% 3.29/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.29/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.29/0.98      | v2_pre_topc(X1_54) != iProver_top
% 3.29/0.98      | v2_pre_topc(sK1) != iProver_top
% 3.29/0.98      | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_4634,c_1720]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2,plain,
% 3.29/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.98      | ~ v1_funct_1(X0)
% 3.29/0.98      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.29/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_977,plain,
% 3.29/0.98      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.29/0.98      | ~ v1_funct_1(X0_52)
% 3.29/0.98      | v1_funct_1(k2_partfun1(X0_53,X1_53,X0_52,X2_53)) ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1528,plain,
% 3.29/0.98      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.29/0.98      | v1_funct_1(X0_52) != iProver_top
% 3.29/0.98      | v1_funct_1(k2_partfun1(X0_53,X1_53,X0_52,X2_53)) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_977]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2415,plain,
% 3.29/0.98      ( v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,X0_53)) = iProver_top
% 3.29/0.98      | v1_funct_1(sK5) != iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_1540,c_1528]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1878,plain,
% 3.29/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.29/0.98      | v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,X0_53))
% 3.29/0.98      | ~ v1_funct_1(sK5) ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_977]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1879,plain,
% 3.29/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.29/0.98      | v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,X0_53)) = iProver_top
% 3.29/0.98      | v1_funct_1(sK5) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_1878]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2836,plain,
% 3.29/0.98      ( v1_funct_1(k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,X0_53)) = iProver_top ),
% 3.29/0.98      inference(global_propositional_subsumption,
% 3.29/0.98                [status(thm)],
% 3.29/0.98                [c_2415,c_50,c_52,c_1879]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_3778,plain,
% 3.29/0.98      ( v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) = iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_3766,c_2836]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_6,plain,
% 3.29/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.29/0.98      | v1_funct_2(k2_partfun1(X1,X2,X0,X3),X3,X2)
% 3.29/0.98      | ~ r1_tarski(X3,X1)
% 3.29/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/0.98      | ~ v1_funct_1(X0)
% 3.29/0.98      | k1_xboole_0 = X2 ),
% 3.29/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_973,plain,
% 3.29/0.98      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 3.29/0.98      | v1_funct_2(k2_partfun1(X0_53,X1_53,X0_52,X2_53),X2_53,X1_53)
% 3.29/0.98      | ~ r1_tarski(X2_53,X0_53)
% 3.29/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.29/0.98      | ~ v1_funct_1(X0_52)
% 3.29/0.98      | k1_xboole_0 = X1_53 ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1532,plain,
% 3.29/0.98      ( k1_xboole_0 = X0_53
% 3.29/0.98      | v1_funct_2(X0_52,X1_53,X0_53) != iProver_top
% 3.29/0.98      | v1_funct_2(k2_partfun1(X1_53,X0_53,X0_52,X2_53),X2_53,X0_53) = iProver_top
% 3.29/0.98      | r1_tarski(X2_53,X1_53) != iProver_top
% 3.29/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) != iProver_top
% 3.29/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_973]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_3777,plain,
% 3.29/0.98      ( u1_struct_0(sK1) = k1_xboole_0
% 3.29/0.98      | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 3.29/0.98      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.29/0.98      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
% 3.29/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.29/0.98      | v1_funct_1(sK5) != iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_3766,c_1532]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_4594,plain,
% 3.29/0.98      ( u1_struct_0(sK1) = k1_xboole_0
% 3.29/0.98      | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 3.29/0.98      inference(global_propositional_subsumption,
% 3.29/0.98                [status(thm)],
% 3.29/0.98                [c_3777,c_38,c_43,c_48,c_50,c_51,c_52,c_1846,c_2113]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_10,plain,
% 3.29/0.98      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.29/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_0,plain,
% 3.29/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.29/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_12,plain,
% 3.29/0.98      ( v2_struct_0(X0)
% 3.29/0.98      | ~ l1_struct_0(X0)
% 3.29/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.29/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_371,plain,
% 3.29/0.98      ( v2_struct_0(X0)
% 3.29/0.98      | ~ l1_struct_0(X0)
% 3.29/0.98      | u1_struct_0(X0) != k1_xboole_0 ),
% 3.29/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_12]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_389,plain,
% 3.29/0.98      ( v2_struct_0(X0)
% 3.29/0.98      | ~ l1_pre_topc(X0)
% 3.29/0.98      | u1_struct_0(X0) != k1_xboole_0 ),
% 3.29/0.98      inference(resolution,[status(thm)],[c_10,c_371]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_948,plain,
% 3.29/0.98      ( v2_struct_0(X0_54)
% 3.29/0.98      | ~ l1_pre_topc(X0_54)
% 3.29/0.98      | u1_struct_0(X0_54) != k1_xboole_0 ),
% 3.29/0.98      inference(subtyping,[status(esa)],[c_389]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_6389,plain,
% 3.29/0.98      ( v2_struct_0(sK1)
% 3.29/0.98      | ~ l1_pre_topc(sK1)
% 3.29/0.98      | u1_struct_0(sK1) != k1_xboole_0 ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_948]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_6966,plain,
% 3.29/0.98      ( l1_pre_topc(X1_54) != iProver_top
% 3.29/0.98      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3))
% 3.29/0.98      | m1_pre_topc(X0_54,sK3) != iProver_top
% 3.29/0.98      | m1_pre_topc(sK3,X1_54) != iProver_top
% 3.29/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.98      | v2_pre_topc(X1_54) != iProver_top ),
% 3.29/0.98      inference(global_propositional_subsumption,
% 3.29/0.98                [status(thm)],
% 3.29/0.98                [c_4640,c_38,c_32,c_39,c_40,c_30,c_41,c_43,c_48,c_50,
% 3.29/0.98                 c_51,c_52,c_1846,c_2113,c_3777,c_3778,c_6389]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_6967,plain,
% 3.29/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3))
% 3.29/0.98      | m1_pre_topc(X0_54,sK3) != iProver_top
% 3.29/0.98      | m1_pre_topc(sK3,X1_54) != iProver_top
% 3.29/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.29/0.98      | v2_pre_topc(X1_54) != iProver_top ),
% 3.29/0.98      inference(renaming,[status(thm)],[c_6966]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_6978,plain,
% 3.29/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(sK2,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3))
% 3.29/0.98      | m1_pre_topc(X0_54,sK3) != iProver_top
% 3.29/0.98      | v2_struct_0(sK2) = iProver_top
% 3.29/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.29/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_1544,c_6967]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_7033,plain,
% 3.29/0.98      ( m1_pre_topc(X0_54,sK3) != iProver_top
% 3.29/0.98      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(sK2,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
% 3.29/0.98      inference(global_propositional_subsumption,
% 3.29/0.98                [status(thm)],
% 3.29/0.98                [c_6978,c_37,c_38,c_42,c_43,c_2113,c_2444]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_7034,plain,
% 3.29/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(sK2,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3))
% 3.29/0.98      | m1_pre_topc(X0_54,sK3) != iProver_top ),
% 3.29/0.98      inference(renaming,[status(thm)],[c_7033]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_7041,plain,
% 3.29/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_1543,c_7034]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1538,plain,
% 3.29/0.98      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.29/0.98      | r1_tarski(u1_struct_0(X0_54),u1_struct_0(X1_54)) = iProver_top
% 3.29/0.98      | l1_pre_topc(X1_54) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_967]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2994,plain,
% 3.29/0.98      ( u1_struct_0(X0_54) = k1_xboole_0
% 3.29/0.98      | k2_partfun1(u1_struct_0(X1_54),u1_struct_0(X0_54),k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),u1_struct_0(X2_54)) = k2_tmap_1(X1_54,X0_54,k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),X2_54)
% 3.29/0.98      | v1_funct_2(X0_52,X0_53,u1_struct_0(X0_54)) != iProver_top
% 3.29/0.98      | v1_funct_2(k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
% 3.29/0.98      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 3.29/0.98      | r1_tarski(u1_struct_0(X1_54),X0_53) != iProver_top
% 3.29/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(X0_54)))) != iProver_top
% 3.29/0.98      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.98      | l1_pre_topc(X1_54) != iProver_top
% 3.29/0.98      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.98      | v2_pre_topc(X1_54) != iProver_top
% 3.29/0.98      | v2_pre_topc(X0_54) != iProver_top
% 3.29/0.98      | v1_funct_1(X0_52) != iProver_top
% 3.29/0.98      | v1_funct_1(k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54))) != iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_1530,c_1536]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1053,plain,
% 3.29/0.98      ( u1_struct_0(X0_54) != k1_xboole_0
% 3.29/0.98      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.98      | l1_pre_topc(X0_54) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_5514,plain,
% 3.29/0.98      ( k2_partfun1(u1_struct_0(X1_54),u1_struct_0(X0_54),k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),u1_struct_0(X2_54)) = k2_tmap_1(X1_54,X0_54,k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),X2_54)
% 3.29/0.98      | v1_funct_2(X0_52,X0_53,u1_struct_0(X0_54)) != iProver_top
% 3.29/0.98      | v1_funct_2(k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),u1_struct_0(X1_54),u1_struct_0(X0_54)) != iProver_top
% 3.29/0.98      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 3.29/0.98      | r1_tarski(u1_struct_0(X1_54),X0_53) != iProver_top
% 3.29/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(X0_54)))) != iProver_top
% 3.29/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v1_funct_1(X0_52) != iProver_top
% 3.29/0.99      | v1_funct_1(k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54))) != iProver_top ),
% 3.29/0.99      inference(global_propositional_subsumption,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_2994,c_1053]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_5515,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),X2_54)
% 3.29/0.99      | v1_funct_2(X0_52,X0_53,u1_struct_0(X1_54)) != iProver_top
% 3.29/0.99      | v1_funct_2(k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.29/0.99      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 3.29/0.99      | r1_tarski(u1_struct_0(X0_54),X0_53) != iProver_top
% 3.29/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(X1_54)))) != iProver_top
% 3.29/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | v1_funct_1(X0_52) != iProver_top
% 3.29/0.99      | v1_funct_1(k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54))) != iProver_top ),
% 3.29/0.99      inference(renaming,[status(thm)],[c_5514]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_5532,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),X2_54)
% 3.29/0.99      | v1_funct_2(X0_52,X0_53,u1_struct_0(X1_54)) != iProver_top
% 3.29/0.99      | v1_funct_2(k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.29/0.99      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 3.29/0.99      | r1_tarski(u1_struct_0(X0_54),X0_53) != iProver_top
% 3.29/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(X1_54)))) != iProver_top
% 3.29/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.29/0.99      inference(forward_subsumption_resolution,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_5515,c_1528]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_5537,plain,
% 3.29/0.99      ( u1_struct_0(X0_54) = k1_xboole_0
% 3.29/0.99      | k2_partfun1(u1_struct_0(X1_54),u1_struct_0(X0_54),k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),u1_struct_0(X2_54)) = k2_tmap_1(X1_54,X0_54,k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),X2_54)
% 3.29/0.99      | v1_funct_2(X0_52,X0_53,u1_struct_0(X0_54)) != iProver_top
% 3.29/0.99      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 3.29/0.99      | r1_tarski(u1_struct_0(X1_54),X0_53) != iProver_top
% 3.29/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(X0_54)))) != iProver_top
% 3.29/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1532,c_5532]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_5825,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(X1_54),u1_struct_0(X0_54),k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),u1_struct_0(X2_54)) = k2_tmap_1(X1_54,X0_54,k2_partfun1(X0_53,u1_struct_0(X0_54),X0_52,u1_struct_0(X1_54)),X2_54)
% 3.29/0.99      | v1_funct_2(X0_52,X0_53,u1_struct_0(X0_54)) != iProver_top
% 3.29/0.99      | m1_pre_topc(X2_54,X1_54) != iProver_top
% 3.29/0.99      | r1_tarski(u1_struct_0(X1_54),X0_53) != iProver_top
% 3.29/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(X0_54)))) != iProver_top
% 3.29/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.29/0.99      inference(global_propositional_subsumption,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_5537,c_1053]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_5826,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,k2_partfun1(X0_53,u1_struct_0(X1_54),X0_52,u1_struct_0(X0_54)),X2_54)
% 3.29/0.99      | v1_funct_2(X0_52,X0_53,u1_struct_0(X1_54)) != iProver_top
% 3.29/0.99      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 3.29/0.99      | r1_tarski(u1_struct_0(X0_54),X0_53) != iProver_top
% 3.29/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(X1_54)))) != iProver_top
% 3.29/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.29/0.99      inference(renaming,[status(thm)],[c_5825]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_5841,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),X1_54)
% 3.29/0.99      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.29/0.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 3.29/0.99      | r1_tarski(u1_struct_0(X0_54),u1_struct_0(sK2)) != iProver_top
% 3.29/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.99      | v2_struct_0(sK1) = iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.29/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1540,c_5826]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6172,plain,
% 3.29/0.99      ( l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),X1_54)
% 3.29/0.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 3.29/0.99      | r1_tarski(u1_struct_0(X0_54),u1_struct_0(sK2)) != iProver_top
% 3.29/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top ),
% 3.29/0.99      inference(global_propositional_subsumption,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_5841,c_39,c_40,c_41,c_50,c_51]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6173,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),X1_54)
% 3.29/0.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 3.29/0.99      | r1_tarski(u1_struct_0(X0_54),u1_struct_0(sK2)) != iProver_top
% 3.29/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top ),
% 3.29/0.99      inference(renaming,[status(thm)],[c_6172]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6184,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),X1_54)
% 3.29/0.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 3.29/0.99      | m1_pre_topc(X0_54,sK2) != iProver_top
% 3.29/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1538,c_6173]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6189,plain,
% 3.29/0.99      ( l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.99      | m1_pre_topc(X0_54,sK2) != iProver_top
% 3.29/0.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 3.29/0.99      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),X1_54)
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top ),
% 3.29/0.99      inference(global_propositional_subsumption,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_6184,c_38,c_43,c_2113]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6190,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),u1_struct_0(X1_54)) = k2_tmap_1(X0_54,sK1,k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)),X1_54)
% 3.29/0.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 3.29/0.99      | m1_pre_topc(X0_54,sK2) != iProver_top
% 3.29/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top ),
% 3.29/0.99      inference(renaming,[status(thm)],[c_6189]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6201,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)),u1_struct_0(X0_54)) = k2_tmap_1(sK3,sK1,k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)),X0_54)
% 3.29/0.99      | m1_pre_topc(X0_54,sK3) != iProver_top
% 3.29/0.99      | v2_struct_0(sK3) = iProver_top
% 3.29/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.29/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1544,c_6190]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6219,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_54)
% 3.29/0.99      | m1_pre_topc(X0_54,sK3) != iProver_top
% 3.29/0.99      | v2_struct_0(sK3) = iProver_top
% 3.29/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.29/0.99      | v2_pre_topc(sK3) != iProver_top ),
% 3.29/0.99      inference(light_normalisation,[status(thm)],[c_6201,c_3766]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_27,negated_conjecture,
% 3.29/0.99      ( ~ v2_struct_0(sK3) ),
% 3.29/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_44,plain,
% 3.29/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_26,negated_conjecture,
% 3.29/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.29/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_45,plain,
% 3.29/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2105,plain,
% 3.29/0.99      ( ~ m1_pre_topc(sK3,X0_54)
% 3.29/0.99      | ~ l1_pre_topc(X0_54)
% 3.29/0.99      | l1_pre_topc(sK3) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_970]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2106,plain,
% 3.29/0.99      ( m1_pre_topc(sK3,X0_54) != iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | l1_pre_topc(sK3) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_2105]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2108,plain,
% 3.29/0.99      ( m1_pre_topc(sK3,sK0) != iProver_top
% 3.29/0.99      | l1_pre_topc(sK3) = iProver_top
% 3.29/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_2106]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2436,plain,
% 3.29/0.99      ( ~ m1_pre_topc(sK3,X0_54)
% 3.29/0.99      | ~ l1_pre_topc(X0_54)
% 3.29/0.99      | ~ v2_pre_topc(X0_54)
% 3.29/0.99      | v2_pre_topc(sK3) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_971]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2437,plain,
% 3.29/0.99      ( m1_pre_topc(sK3,X0_54) != iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(sK3) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_2436]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2439,plain,
% 3.29/0.99      ( m1_pre_topc(sK3,sK0) != iProver_top
% 3.29/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.29/0.99      | v2_pre_topc(sK3) = iProver_top
% 3.29/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_2437]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6291,plain,
% 3.29/0.99      ( m1_pre_topc(X0_54,sK3) != iProver_top
% 3.29/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_54) ),
% 3.29/0.99      inference(global_propositional_subsumption,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_6219,c_37,c_38,c_44,c_45,c_2108,c_2439]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6292,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_54)
% 3.29/0.99      | m1_pre_topc(X0_54,sK3) != iProver_top ),
% 3.29/0.99      inference(renaming,[status(thm)],[c_6291]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6299,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1543,c_6292]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_7042,plain,
% 3.29/0.99      ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
% 3.29/0.99      inference(light_normalisation,[status(thm)],[c_7041,c_6299]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_956,negated_conjecture,
% 3.29/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.29/0.99      inference(subtyping,[status(esa)],[c_28]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1549,plain,
% 3.29/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_956]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3556,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK2,X0_54,sK5)
% 3.29/0.99      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.29/0.99      | m1_pre_topc(X0_54,sK2) != iProver_top
% 3.29/0.99      | m1_pre_topc(sK2,X1_54) != iProver_top
% 3.29/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.99      | v2_struct_0(sK1) = iProver_top
% 3.29/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.29/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.29/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1540,c_1720]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3869,plain,
% 3.29/0.99      ( l1_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK2,X0_54,sK5)
% 3.29/0.99      | m1_pre_topc(X0_54,sK2) != iProver_top
% 3.29/0.99      | m1_pre_topc(sK2,X1_54) != iProver_top
% 3.29/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.99      | v2_pre_topc(X1_54) != iProver_top ),
% 3.29/0.99      inference(global_propositional_subsumption,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_3556,c_39,c_40,c_41,c_50,c_51]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3870,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK2,X0_54,sK5)
% 3.29/0.99      | m1_pre_topc(X0_54,sK2) != iProver_top
% 3.29/0.99      | m1_pre_topc(sK2,X1_54) != iProver_top
% 3.29/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X1_54) != iProver_top ),
% 3.29/0.99      inference(renaming,[status(thm)],[c_3869]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3881,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK2,X0_54,sK5)
% 3.29/0.99      | m1_pre_topc(X0_54,sK2) != iProver_top
% 3.29/0.99      | v2_struct_0(sK0) = iProver_top
% 3.29/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.29/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1549,c_3870]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_35,negated_conjecture,
% 3.29/0.99      ( ~ v2_struct_0(sK0) ),
% 3.29/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_36,plain,
% 3.29/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3886,plain,
% 3.29/0.99      ( m1_pre_topc(X0_54,sK2) != iProver_top
% 3.29/0.99      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK2,X0_54,sK5) ),
% 3.29/0.99      inference(global_propositional_subsumption,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_3881,c_36,c_37,c_38]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3887,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK2,X0_54,sK5)
% 3.29/0.99      | m1_pre_topc(X0_54,sK2) != iProver_top ),
% 3.29/0.99      inference(renaming,[status(thm)],[c_3886]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3894,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK2,sK3,sK5) ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1544,c_3887]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3899,plain,
% 3.29/0.99      ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
% 3.29/0.99      inference(light_normalisation,[status(thm)],[c_3894,c_3766]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_16,plain,
% 3.29/0.99      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k2_tmap_1(X2,X1,X4,X3)),k2_tmap_1(X2,X1,X4,X0))
% 3.29/0.99      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
% 3.29/0.99      | ~ m1_pre_topc(X3,X2)
% 3.29/0.99      | ~ m1_pre_topc(X0,X2)
% 3.29/0.99      | ~ m1_pre_topc(X0,X3)
% 3.29/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.29/0.99      | v2_struct_0(X2)
% 3.29/0.99      | v2_struct_0(X1)
% 3.29/0.99      | v2_struct_0(X0)
% 3.29/0.99      | v2_struct_0(X3)
% 3.29/0.99      | ~ l1_pre_topc(X2)
% 3.29/0.99      | ~ l1_pre_topc(X1)
% 3.29/0.99      | ~ v2_pre_topc(X2)
% 3.29/0.99      | ~ v2_pre_topc(X1)
% 3.29/0.99      | ~ v1_funct_1(X4) ),
% 3.29/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_18,negated_conjecture,
% 3.29/0.99      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
% 3.29/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_407,plain,
% 3.29/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.29/0.99      | ~ m1_pre_topc(X3,X1)
% 3.29/0.99      | ~ m1_pre_topc(X4,X1)
% 3.29/0.99      | ~ m1_pre_topc(X4,X3)
% 3.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.29/0.99      | v2_struct_0(X4)
% 3.29/0.99      | v2_struct_0(X2)
% 3.29/0.99      | v2_struct_0(X1)
% 3.29/0.99      | v2_struct_0(X3)
% 3.29/0.99      | ~ l1_pre_topc(X2)
% 3.29/0.99      | ~ l1_pre_topc(X1)
% 3.29/0.99      | ~ v2_pre_topc(X2)
% 3.29/0.99      | ~ v2_pre_topc(X1)
% 3.29/0.99      | ~ v1_funct_1(X0)
% 3.29/0.99      | k3_tmap_1(sK0,sK1,sK2,sK4,sK5) != k2_tmap_1(X1,X2,X0,X4)
% 3.29/0.99      | k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) != k3_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X0,X3))
% 3.29/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 3.29/0.99      | u1_struct_0(X4) != u1_struct_0(sK4) ),
% 3.29/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_447,plain,
% 3.29/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.29/0.99      | ~ m1_pre_topc(X3,X1)
% 3.29/0.99      | ~ m1_pre_topc(X4,X3)
% 3.29/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.29/0.99      | v2_struct_0(X1)
% 3.29/0.99      | v2_struct_0(X2)
% 3.29/0.99      | v2_struct_0(X4)
% 3.29/0.99      | v2_struct_0(X3)
% 3.29/0.99      | ~ l1_pre_topc(X1)
% 3.29/0.99      | ~ l1_pre_topc(X2)
% 3.29/0.99      | ~ v2_pre_topc(X1)
% 3.29/0.99      | ~ v2_pre_topc(X2)
% 3.29/0.99      | ~ v1_funct_1(X0)
% 3.29/0.99      | k3_tmap_1(sK0,sK1,sK2,sK4,sK5) != k2_tmap_1(X1,X2,X0,X4)
% 3.29/0.99      | k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) != k3_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X0,X3))
% 3.29/0.99      | u1_struct_0(X2) != u1_struct_0(sK1)
% 3.29/0.99      | u1_struct_0(X4) != u1_struct_0(sK4) ),
% 3.29/0.99      inference(forward_subsumption_resolution,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_407,c_17]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_947,plain,
% 3.29/0.99      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.29/0.99      | ~ m1_pre_topc(X2_54,X0_54)
% 3.29/0.99      | ~ m1_pre_topc(X3_54,X2_54)
% 3.29/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.29/0.99      | v2_struct_0(X1_54)
% 3.29/0.99      | v2_struct_0(X2_54)
% 3.29/0.99      | v2_struct_0(X3_54)
% 3.29/0.99      | v2_struct_0(X0_54)
% 3.29/0.99      | ~ l1_pre_topc(X1_54)
% 3.29/0.99      | ~ l1_pre_topc(X0_54)
% 3.29/0.99      | ~ v2_pre_topc(X1_54)
% 3.29/0.99      | ~ v2_pre_topc(X0_54)
% 3.29/0.99      | ~ v1_funct_1(X0_52)
% 3.29/0.99      | u1_struct_0(X1_54) != u1_struct_0(sK1)
% 3.29/0.99      | u1_struct_0(X3_54) != u1_struct_0(sK4)
% 3.29/0.99      | k3_tmap_1(sK0,sK1,sK2,sK4,sK5) != k2_tmap_1(X0_54,X1_54,X0_52,X3_54)
% 3.29/0.99      | k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) != k3_tmap_1(X0_54,X1_54,X2_54,X3_54,k2_tmap_1(X0_54,X1_54,X0_52,X2_54)) ),
% 3.29/0.99      inference(subtyping,[status(esa)],[c_447]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1558,plain,
% 3.29/0.99      ( u1_struct_0(X0_54) != u1_struct_0(sK1)
% 3.29/0.99      | u1_struct_0(X1_54) != u1_struct_0(sK4)
% 3.29/0.99      | k3_tmap_1(sK0,sK1,sK2,sK4,sK5) != k2_tmap_1(X2_54,X0_54,X0_52,X1_54)
% 3.29/0.99      | k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) != k3_tmap_1(X2_54,X0_54,X3_54,X1_54,k2_tmap_1(X2_54,X0_54,X0_52,X3_54))
% 3.29/0.99      | v1_funct_2(X0_52,u1_struct_0(X2_54),u1_struct_0(X0_54)) != iProver_top
% 3.29/0.99      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 3.29/0.99      | m1_pre_topc(X1_54,X3_54) != iProver_top
% 3.29/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) != iProver_top
% 3.29/0.99      | v2_struct_0(X3_54) = iProver_top
% 3.29/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.99      | v2_struct_0(X2_54) = iProver_top
% 3.29/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | l1_pre_topc(X2_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X2_54) != iProver_top
% 3.29/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3946,plain,
% 3.29/0.99      ( u1_struct_0(X0_54) != u1_struct_0(sK1)
% 3.29/0.99      | u1_struct_0(X1_54) != u1_struct_0(sK4)
% 3.29/0.99      | k3_tmap_1(X2_54,X0_54,X3_54,X1_54,k2_tmap_1(X2_54,X0_54,X0_52,X3_54)) != k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
% 3.29/0.99      | k3_tmap_1(sK0,sK1,sK2,sK4,sK5) != k2_tmap_1(X2_54,X0_54,X0_52,X1_54)
% 3.29/0.99      | v1_funct_2(X0_52,u1_struct_0(X2_54),u1_struct_0(X0_54)) != iProver_top
% 3.29/0.99      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 3.29/0.99      | m1_pre_topc(X1_54,X3_54) != iProver_top
% 3.29/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) != iProver_top
% 3.29/0.99      | v2_struct_0(X2_54) = iProver_top
% 3.29/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.99      | v2_struct_0(X3_54) = iProver_top
% 3.29/0.99      | l1_pre_topc(X2_54) != iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X2_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.29/0.99      inference(demodulation,[status(thm)],[c_3899,c_1558]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2582,plain,
% 3.29/0.99      ( m1_pre_topc(sK3,X0_54) != iProver_top
% 3.29/0.99      | m1_pre_topc(sK4,X0_54) = iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1543,c_1539]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3194,plain,
% 3.29/0.99      ( m1_pre_topc(sK4,sK2) = iProver_top
% 3.29/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.29/0.99      | v2_pre_topc(sK2) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1544,c_2582]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_49,plain,
% 3.29/0.99      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1857,plain,
% 3.29/0.99      ( ~ m1_pre_topc(sK3,X0_54)
% 3.29/0.99      | m1_pre_topc(sK4,X0_54)
% 3.29/0.99      | ~ m1_pre_topc(sK4,sK3)
% 3.29/0.99      | ~ l1_pre_topc(X0_54)
% 3.29/0.99      | ~ v2_pre_topc(X0_54) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_966]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2849,plain,
% 3.29/0.99      ( ~ m1_pre_topc(sK3,sK2)
% 3.29/0.99      | m1_pre_topc(sK4,sK2)
% 3.29/0.99      | ~ m1_pre_topc(sK4,sK3)
% 3.29/0.99      | ~ l1_pre_topc(sK2)
% 3.29/0.99      | ~ v2_pre_topc(sK2) ),
% 3.29/0.99      inference(instantiation,[status(thm)],[c_1857]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_2852,plain,
% 3.29/0.99      ( m1_pre_topc(sK3,sK2) != iProver_top
% 3.29/0.99      | m1_pre_topc(sK4,sK2) = iProver_top
% 3.29/0.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 3.29/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.29/0.99      | v2_pre_topc(sK2) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_2849]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3264,plain,
% 3.29/0.99      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.29/0.99      inference(global_propositional_subsumption,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_3194,c_37,c_38,c_43,c_48,c_49,c_2113,c_2444,c_2852]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3895,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK2,sK4,sK5) ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_3264,c_3887]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_3767,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_3264,c_3759]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_4583,plain,
% 3.29/0.99      ( k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
% 3.29/0.99      inference(light_normalisation,[status(thm)],[c_3895,c_3767]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_958,negated_conjecture,
% 3.29/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.29/0.99      inference(subtyping,[status(esa)],[c_26]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_1547,plain,
% 3.29/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_958]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_6979,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3))
% 3.29/0.99      | m1_pre_topc(X0_54,sK3) != iProver_top
% 3.29/0.99      | v2_struct_0(sK0) = iProver_top
% 3.29/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.29/0.99      | v2_pre_topc(sK0) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1547,c_6967]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_7044,plain,
% 3.29/0.99      ( m1_pre_topc(X0_54,sK3) != iProver_top
% 3.29/0.99      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
% 3.29/0.99      inference(global_propositional_subsumption,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_6979,c_36,c_37,c_38]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_7045,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_54)) = k3_tmap_1(sK0,sK1,sK3,X0_54,k2_tmap_1(sK2,sK1,sK5,sK3))
% 3.29/0.99      | m1_pre_topc(X0_54,sK3) != iProver_top ),
% 3.29/0.99      inference(renaming,[status(thm)],[c_7044]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_7052,plain,
% 3.29/0.99      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_1543,c_7045]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_7053,plain,
% 3.29/0.99      ( k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
% 3.29/0.99      inference(light_normalisation,[status(thm)],[c_7052,c_6299]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_9076,plain,
% 3.29/0.99      ( u1_struct_0(X0_54) != u1_struct_0(sK1)
% 3.29/0.99      | u1_struct_0(X1_54) != u1_struct_0(sK4)
% 3.29/0.99      | k3_tmap_1(X2_54,X0_54,X3_54,X1_54,k2_tmap_1(X2_54,X0_54,X0_52,X3_54)) != k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4)
% 3.29/0.99      | k2_tmap_1(X2_54,X0_54,X0_52,X1_54) != k2_tmap_1(sK2,sK1,sK5,sK4)
% 3.29/0.99      | v1_funct_2(X0_52,u1_struct_0(X2_54),u1_struct_0(X0_54)) != iProver_top
% 3.29/0.99      | m1_pre_topc(X3_54,X2_54) != iProver_top
% 3.29/0.99      | m1_pre_topc(X1_54,X3_54) != iProver_top
% 3.29/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X0_54)))) != iProver_top
% 3.29/0.99      | v2_struct_0(X2_54) = iProver_top
% 3.29/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.29/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.29/0.99      | v2_struct_0(X3_54) = iProver_top
% 3.29/0.99      | l1_pre_topc(X2_54) != iProver_top
% 3.29/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X2_54) != iProver_top
% 3.29/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.29/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.29/0.99      inference(light_normalisation,[status(thm)],[c_3946,c_4583,c_7053]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_9097,plain,
% 3.29/0.99      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.29/0.99      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.29/0.99      | k2_tmap_1(sK2,sK1,sK5,sK4) != k2_tmap_1(sK2,sK1,sK5,sK4)
% 3.29/0.99      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.29/0.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.29/0.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 3.29/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.29/0.99      | v2_struct_0(sK2) = iProver_top
% 3.29/0.99      | v2_struct_0(sK3) = iProver_top
% 3.29/0.99      | v2_struct_0(sK1) = iProver_top
% 3.29/0.99      | v2_struct_0(sK4) = iProver_top
% 3.29/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.29/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.29/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.29/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.29/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.29/0.99      inference(superposition,[status(thm)],[c_7042,c_9076]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_10158,plain,
% 3.29/0.99      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.29/0.99      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.29/0.99      | m1_pre_topc(sK4,sK3) != iProver_top
% 3.29/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.29/0.99      | v2_struct_0(sK2) = iProver_top
% 3.29/0.99      | v2_struct_0(sK3) = iProver_top
% 3.29/0.99      | v2_struct_0(sK1) = iProver_top
% 3.29/0.99      | v2_struct_0(sK4) = iProver_top
% 3.29/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.29/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.29/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.29/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.29/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.29/0.99      inference(equality_resolution_simp,[status(thm)],[c_9097]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_25,negated_conjecture,
% 3.29/0.99      ( ~ v2_struct_0(sK4) ),
% 3.29/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(c_46,plain,
% 3.29/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 3.29/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.29/0.99  
% 3.29/0.99  cnf(contradiction,plain,
% 3.29/0.99      ( $false ),
% 3.29/0.99      inference(minisat,
% 3.29/0.99                [status(thm)],
% 3.29/0.99                [c_10158,c_2444,c_2113,c_52,c_51,c_50,c_49,c_48,c_46,
% 3.29/0.99                 c_44,c_43,c_42,c_41,c_40,c_39,c_38,c_37]) ).
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.29/0.99  
% 3.29/0.99  ------                               Statistics
% 3.29/0.99  
% 3.29/0.99  ------ General
% 3.29/0.99  
% 3.29/0.99  abstr_ref_over_cycles:                  0
% 3.29/0.99  abstr_ref_under_cycles:                 0
% 3.29/0.99  gc_basic_clause_elim:                   0
% 3.29/0.99  forced_gc_time:                         0
% 3.29/0.99  parsing_time:                           0.011
% 3.29/0.99  unif_index_cands_time:                  0.
% 3.29/0.99  unif_index_add_time:                    0.
% 3.29/0.99  orderings_time:                         0.
% 3.29/0.99  out_proof_time:                         0.016
% 3.29/0.99  total_time:                             0.36
% 3.29/0.99  num_of_symbols:                         57
% 3.29/0.99  num_of_terms:                           6513
% 3.29/0.99  
% 3.29/0.99  ------ Preprocessing
% 3.29/0.99  
% 3.29/0.99  num_of_splits:                          0
% 3.29/0.99  num_of_split_atoms:                     0
% 3.29/0.99  num_of_reused_defs:                     0
% 3.29/0.99  num_eq_ax_congr_red:                    26
% 3.29/0.99  num_of_sem_filtered_clauses:            1
% 3.29/0.99  num_of_subtypes:                        5
% 3.29/0.99  monotx_restored_types:                  1
% 3.29/0.99  sat_num_of_epr_types:                   0
% 3.29/0.99  sat_num_of_non_cyclic_types:            0
% 3.29/0.99  sat_guarded_non_collapsed_types:        0
% 3.29/0.99  num_pure_diseq_elim:                    0
% 3.29/0.99  simp_replaced_by:                       0
% 3.29/0.99  res_preprocessed:                       160
% 3.29/0.99  prep_upred:                             0
% 3.29/0.99  prep_unflattend:                        14
% 3.29/0.99  smt_new_axioms:                         0
% 3.29/0.99  pred_elim_cands:                        8
% 3.29/0.99  pred_elim:                              3
% 3.29/0.99  pred_elim_cl:                           3
% 3.29/0.99  pred_elim_cycles:                       5
% 3.29/0.99  merged_defs:                            0
% 3.29/0.99  merged_defs_ncl:                        0
% 3.29/0.99  bin_hyper_res:                          0
% 3.29/0.99  prep_cycles:                            4
% 3.29/0.99  pred_elim_time:                         0.011
% 3.29/0.99  splitting_time:                         0.
% 3.29/0.99  sem_filter_time:                        0.
% 3.29/0.99  monotx_time:                            0.001
% 3.29/0.99  subtype_inf_time:                       0.002
% 3.29/0.99  
% 3.29/0.99  ------ Problem properties
% 3.29/0.99  
% 3.29/0.99  clauses:                                32
% 3.29/0.99  conjectures:                            17
% 3.29/0.99  epr:                                    18
% 3.29/0.99  horn:                                   27
% 3.29/0.99  ground:                                 17
% 3.29/0.99  unary:                                  17
% 3.29/0.99  binary:                                 0
% 3.29/0.99  lits:                                   109
% 3.29/0.99  lits_eq:                                9
% 3.29/0.99  fd_pure:                                0
% 3.29/0.99  fd_pseudo:                              0
% 3.29/0.99  fd_cond:                                2
% 3.29/0.99  fd_pseudo_cond:                         0
% 3.29/0.99  ac_symbols:                             0
% 3.29/0.99  
% 3.29/0.99  ------ Propositional Solver
% 3.29/0.99  
% 3.29/0.99  prop_solver_calls:                      31
% 3.29/0.99  prop_fast_solver_calls:                 2529
% 3.29/0.99  smt_solver_calls:                       0
% 3.29/0.99  smt_fast_solver_calls:                  0
% 3.29/0.99  prop_num_of_clauses:                    2610
% 3.29/0.99  prop_preprocess_simplified:             6811
% 3.29/0.99  prop_fo_subsumed:                       312
% 3.29/0.99  prop_solver_time:                       0.
% 3.29/0.99  smt_solver_time:                        0.
% 3.29/0.99  smt_fast_solver_time:                   0.
% 3.29/0.99  prop_fast_solver_time:                  0.
% 3.29/0.99  prop_unsat_core_time:                   0.001
% 3.29/0.99  
% 3.29/0.99  ------ QBF
% 3.29/0.99  
% 3.29/0.99  qbf_q_res:                              0
% 3.29/0.99  qbf_num_tautologies:                    0
% 3.29/0.99  qbf_prep_cycles:                        0
% 3.29/0.99  
% 3.29/0.99  ------ BMC1
% 3.29/0.99  
% 3.29/0.99  bmc1_current_bound:                     -1
% 3.29/0.99  bmc1_last_solved_bound:                 -1
% 3.29/0.99  bmc1_unsat_core_size:                   -1
% 3.29/0.99  bmc1_unsat_core_parents_size:           -1
% 3.29/0.99  bmc1_merge_next_fun:                    0
% 3.29/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.29/0.99  
% 3.29/0.99  ------ Instantiation
% 3.29/0.99  
% 3.29/0.99  inst_num_of_clauses:                    643
% 3.29/0.99  inst_num_in_passive:                    10
% 3.29/0.99  inst_num_in_active:                     554
% 3.29/0.99  inst_num_in_unprocessed:                79
% 3.29/0.99  inst_num_of_loops:                      660
% 3.29/0.99  inst_num_of_learning_restarts:          0
% 3.29/0.99  inst_num_moves_active_passive:          98
% 3.29/0.99  inst_lit_activity:                      0
% 3.29/0.99  inst_lit_activity_moves:                0
% 3.29/0.99  inst_num_tautologies:                   0
% 3.29/0.99  inst_num_prop_implied:                  0
% 3.29/0.99  inst_num_existing_simplified:           0
% 3.29/0.99  inst_num_eq_res_simplified:             0
% 3.29/0.99  inst_num_child_elim:                    0
% 3.29/0.99  inst_num_of_dismatching_blockings:      197
% 3.29/0.99  inst_num_of_non_proper_insts:           850
% 3.29/0.99  inst_num_of_duplicates:                 0
% 3.29/0.99  inst_inst_num_from_inst_to_res:         0
% 3.29/0.99  inst_dismatching_checking_time:         0.
% 3.29/0.99  
% 3.29/0.99  ------ Resolution
% 3.29/0.99  
% 3.29/0.99  res_num_of_clauses:                     0
% 3.29/0.99  res_num_in_passive:                     0
% 3.29/0.99  res_num_in_active:                      0
% 3.29/0.99  res_num_of_loops:                       164
% 3.29/0.99  res_forward_subset_subsumed:            56
% 3.29/0.99  res_backward_subset_subsumed:           2
% 3.29/0.99  res_forward_subsumed:                   2
% 3.29/0.99  res_backward_subsumed:                  0
% 3.29/0.99  res_forward_subsumption_resolution:     1
% 3.29/0.99  res_backward_subsumption_resolution:    0
% 3.29/0.99  res_clause_to_clause_subsumption:       745
% 3.29/0.99  res_orphan_elimination:                 0
% 3.29/0.99  res_tautology_del:                      129
% 3.29/0.99  res_num_eq_res_simplified:              0
% 3.29/0.99  res_num_sel_changes:                    0
% 3.29/0.99  res_moves_from_active_to_pass:          0
% 3.29/0.99  
% 3.29/0.99  ------ Superposition
% 3.29/0.99  
% 3.29/0.99  sup_time_total:                         0.
% 3.29/0.99  sup_time_generating:                    0.
% 3.29/0.99  sup_time_sim_full:                      0.
% 3.29/0.99  sup_time_sim_immed:                     0.
% 3.29/0.99  
% 3.29/0.99  sup_num_of_clauses:                     172
% 3.29/0.99  sup_num_in_active:                      129
% 3.29/0.99  sup_num_in_passive:                     43
% 3.29/0.99  sup_num_of_loops:                       130
% 3.29/0.99  sup_fw_superposition:                   140
% 3.29/0.99  sup_bw_superposition:                   54
% 3.29/0.99  sup_immediate_simplified:               50
% 3.29/0.99  sup_given_eliminated:                   0
% 3.29/0.99  comparisons_done:                       0
% 3.29/0.99  comparisons_avoided:                    6
% 3.29/0.99  
% 3.29/0.99  ------ Simplifications
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  sim_fw_subset_subsumed:                 5
% 3.29/0.99  sim_bw_subset_subsumed:                 4
% 3.29/0.99  sim_fw_subsumed:                        18
% 3.29/0.99  sim_bw_subsumed:                        7
% 3.29/0.99  sim_fw_subsumption_res:                 13
% 3.29/0.99  sim_bw_subsumption_res:                 0
% 3.29/0.99  sim_tautology_del:                      0
% 3.29/0.99  sim_eq_tautology_del:                   0
% 3.29/0.99  sim_eq_res_simp:                        1
% 3.29/0.99  sim_fw_demodulated:                     0
% 3.29/0.99  sim_bw_demodulated:                     1
% 3.29/0.99  sim_light_normalised:                   32
% 3.29/0.99  sim_joinable_taut:                      0
% 3.29/0.99  sim_joinable_simp:                      0
% 3.29/0.99  sim_ac_normalised:                      0
% 3.29/0.99  sim_smt_subsumption:                    0
% 3.29/0.99  
%------------------------------------------------------------------------------
