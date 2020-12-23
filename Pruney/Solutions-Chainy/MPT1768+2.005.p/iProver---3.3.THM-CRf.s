%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:01 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  186 (3041 expanded)
%              Number of clauses        :  129 ( 699 expanded)
%              Number of leaves         :   14 (1300 expanded)
%              Depth                    :   23
%              Number of atoms          : 1133 (44167 expanded)
%              Number of equality atoms :  424 (1391 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   36 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,(
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

fof(f27,plain,(
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

fof(f26,plain,(
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

fof(f25,plain,
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

fof(f31,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f24,f30,f29,f28,f27,f26,f25])).

fof(f53,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f34,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
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
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
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
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f39,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_229,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_684,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_224,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_689,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_233,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_680,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_233])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_240,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X2_48,X0_48)
    | ~ m1_pre_topc(X0_48,X3_48)
    | ~ m1_pre_topc(X2_48,X3_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X3_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X3_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X3_48)
    | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_673,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | m1_pre_topc(X2_48,X3_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X3_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X3_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_240])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_235,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ m1_pre_topc(X2_48,X0_48)
    | m1_pre_topc(X2_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v2_pre_topc(X1_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_678,plain,
    ( m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X2_48,X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_235])).

cnf(c_864,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X3_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X3_48) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_673,c_678])).

cnf(c_3691,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_680,c_864])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_30,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_31,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_32,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_41,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_42,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3872,plain,
    ( v2_pre_topc(X1_48) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3691,c_30,c_31,c_32,c_41,c_42])).

cnf(c_3873,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_3872])).

cnf(c_3884,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(sK0,sK1,sK2,X0_48,sK5)
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_689,c_3873])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_27,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_28,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_29,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3889,plain,
    ( m1_pre_topc(X0_48,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(sK0,sK1,sK2,X0_48,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3884,c_27,c_28,c_29])).

cnf(c_3890,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(sK0,sK1,sK2,X0_48,sK5)
    | m1_pre_topc(X0_48,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3889])).

cnf(c_3897,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(superposition,[status(thm)],[c_684,c_3890])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_241,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X2_48,X0_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X0_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X0_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X0_48)
    | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_672,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48)
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_2059,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_680,c_672])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_33,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_34,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_242,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1418,plain,
    ( ~ m1_pre_topc(sK2,X0_48)
    | ~ l1_pre_topc(X0_48)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_1419,plain,
    ( m1_pre_topc(sK2,X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1418])).

cnf(c_1421,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1419])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_243,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v2_pre_topc(X1_48)
    | v2_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_670,plain,
    ( m1_pre_topc(X0_48,X1_48) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_243])).

cnf(c_1455,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_689,c_670])).

cnf(c_3367,plain,
    ( m1_pre_topc(X0_48,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2059,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_41,c_42,c_1421,c_1455])).

cnf(c_3368,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48)
    | m1_pre_topc(X0_48,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3367])).

cnf(c_3375,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_684,c_3368])).

cnf(c_3903,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
    inference(light_normalisation,[status(thm)],[c_3897,c_3375])).

cnf(c_13,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_230,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_683,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_230])).

cnf(c_1988,plain,
    ( m1_pre_topc(X0_48,sK2) = iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_684,c_678])).

cnf(c_2941,plain,
    ( m1_pre_topc(X0_48,sK2) = iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1988,c_28,c_29,c_34,c_1421,c_1455])).

cnf(c_2949,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_683,c_2941])).

cnf(c_3898,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK2,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_2949,c_3890])).

cnf(c_3376,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_2949,c_3368])).

cnf(c_3900,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
    inference(light_normalisation,[status(thm)],[c_3898,c_3376])).

cnf(c_9,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_234,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_679,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_6330,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k2_tmap_1(sK2,sK1,sK5,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3900,c_679])).

cnf(c_6941,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3903,c_6330])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_226,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_687,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X3,X2,X1,X4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_239,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | m1_subset_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X3_48,X2_48)
    | ~ m1_pre_topc(X0_48,X2_48)
    | v2_struct_0(X2_48)
    | v2_struct_0(X1_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X2_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_674,plain,
    ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) = iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_3692,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k3_tmap_1(X5_48,X1_48,X0_48,X4_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49))
    | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X5_48) != iProver_top
    | m1_pre_topc(X4_48,X0_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v2_struct_0(X5_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49)) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | l1_pre_topc(X5_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X5_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_674,c_864])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0))
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_237,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X0_48,X2_48)
    | ~ m1_pre_topc(X3_48,X2_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X2_48)
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49))
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X2_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_676,plain,
    ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X2_48,X3_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X3_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X3_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_238,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | v1_funct_2(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),u1_struct_0(X3_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X3_48,X2_48)
    | ~ m1_pre_topc(X0_48,X2_48)
    | v2_struct_0(X2_48)
    | v2_struct_0(X1_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X2_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_675,plain,
    ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),u1_struct_0(X3_48),u1_struct_0(X1_48)) = iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_238])).

cnf(c_4984,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k3_tmap_1(X5_48,X1_48,X0_48,X4_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49))
    | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | m1_pre_topc(X4_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X5_48) != iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X5_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | l1_pre_topc(X5_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X5_48) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3692,c_676,c_675])).

cnf(c_4988,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k3_tmap_1(X3_48,sK1,X0_48,X2_48,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5))
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X3_48) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X3_48) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_680,c_4984])).

cnf(c_5077,plain,
    ( v2_pre_topc(X3_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k3_tmap_1(X3_48,sK1,X0_48,X2_48,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5))
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X3_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4988,c_30,c_31,c_32,c_41,c_42])).

cnf(c_5078,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k3_tmap_1(X3_48,sK1,X0_48,X2_48,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5))
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X3_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X3_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_5077])).

cnf(c_5097,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_5078])).

cnf(c_6227,plain,
    ( v2_pre_topc(X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | m1_pre_topc(sK3,X1_48) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5097,c_27,c_28,c_29,c_34])).

cnf(c_6228,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_6227])).

cnf(c_6240,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(sK0,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_6228])).

cnf(c_6567,plain,
    ( m1_pre_topc(X0_48,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(sK0,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6240,c_27,c_28,c_29])).

cnf(c_6568,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(sK0,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
    | m1_pre_topc(X0_48,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6567])).

cnf(c_6575,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_683,c_6568])).

cnf(c_2801,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k2_tmap_1(X0_48,X1_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),X4_48)
    | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | m1_pre_topc(X4_48,X0_48) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49)) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_674,c_672])).

cnf(c_671,plain,
    ( m1_pre_topc(X0_48,X1_48) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_242])).

cnf(c_4030,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k2_tmap_1(X0_48,X1_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),X4_48)
    | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | m1_pre_topc(X4_48,X0_48) != iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2801,c_670,c_671,c_676,c_675])).

cnf(c_4034,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k2_tmap_1(X0_48,sK1,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),X2_48)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_680,c_4030])).

cnf(c_4269,plain,
    ( v2_pre_topc(X1_48) != iProver_top
    | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k2_tmap_1(X0_48,sK1,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),X2_48)
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4034,c_30,c_31,c_32,c_41,c_42])).

cnf(c_4270,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k2_tmap_1(X0_48,sK1,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),X2_48)
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_4269])).

cnf(c_4286,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK3,sK5),X0_48)
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_4270])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_35,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4634,plain,
    ( m1_pre_topc(X0_48,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK3,sK5),X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4286,c_27,c_28,c_29,c_34,c_35])).

cnf(c_4635,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK3,sK5),X0_48)
    | m1_pre_topc(X0_48,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4634])).

cnf(c_4642,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK4)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK3,sK5),sK4) ),
    inference(superposition,[status(thm)],[c_683,c_4635])).

cnf(c_6576,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK3,sK5),sK4) ),
    inference(light_normalisation,[status(thm)],[c_6575,c_4642])).

cnf(c_7387,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
    inference(light_normalisation,[status(thm)],[c_6576,c_3903])).

cnf(c_7786,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6941,c_7387])).

cnf(c_6239,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(sK2,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_684,c_6228])).

cnf(c_6315,plain,
    ( m1_pre_topc(X0_48,sK3) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(sK2,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6239,c_28,c_29,c_33,c_34,c_1421,c_1455])).

cnf(c_6316,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(sK2,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
    | m1_pre_topc(X0_48,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6315])).

cnf(c_6323,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK4)) = k3_tmap_1(sK2,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_683,c_6316])).

cnf(c_6324,plain,
    ( k3_tmap_1(sK2,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK3,sK5),sK4) ),
    inference(light_normalisation,[status(thm)],[c_6323,c_4642])).

cnf(c_7089,plain,
    ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
    inference(light_normalisation,[status(thm)],[c_6324,c_3903])).

cnf(c_7,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k2_tmap_1(X2,X1,X4,X3)),k2_tmap_1(X2,X1,X4,X0))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_236,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,k2_tmap_1(X2_48,X1_48,X0_49,X3_48)),k2_tmap_1(X2_48,X1_48,X0_49,X0_48))
    | ~ v1_funct_2(X0_49,u1_struct_0(X2_48),u1_struct_0(X1_48))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
    | ~ m1_pre_topc(X3_48,X2_48)
    | ~ m1_pre_topc(X0_48,X2_48)
    | ~ m1_pre_topc(X0_48,X3_48)
    | v2_struct_0(X2_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X0_48)
    | v2_struct_0(X3_48)
    | ~ v1_funct_1(X0_49)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X2_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_677,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,k2_tmap_1(X2_48,X1_48,X0_49,X3_48)),k2_tmap_1(X2_48,X1_48,X0_49,X0_48)) = iProver_top
    | v1_funct_2(X0_49,u1_struct_0(X2_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_892,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,k2_tmap_1(X2_48,X1_48,X0_49,X3_48)),k2_tmap_1(X2_48,X1_48,X0_49,X0_48)) = iProver_top
    | v1_funct_2(X0_49,u1_struct_0(X2_48),u1_struct_0(X1_48)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_677,c_678])).

cnf(c_7091,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7089,c_892])).

cnf(c_43,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_40,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_39,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_37,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7786,c_7091,c_1455,c_1421,c_43,c_42,c_41,c_40,c_39,c_37,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:46:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.73/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/0.98  
% 3.73/0.98  ------  iProver source info
% 3.73/0.98  
% 3.73/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.73/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/0.98  git: non_committed_changes: false
% 3.73/0.98  git: last_make_outside_of_git: false
% 3.73/0.98  
% 3.73/0.98  ------ 
% 3.73/0.98  ------ Parsing...
% 3.73/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.98  ------ Proving...
% 3.73/0.98  ------ Problem Properties 
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  clauses                                 27
% 3.73/0.98  conjectures                             18
% 3.73/0.98  EPR                                     18
% 3.73/0.98  Horn                                    21
% 3.73/0.98  unary                                   18
% 3.73/0.98  binary                                  0
% 3.73/0.98  lits                                    105
% 3.73/0.98  lits eq                                 2
% 3.73/0.98  fd_pure                                 0
% 3.73/0.98  fd_pseudo                               0
% 3.73/0.98  fd_cond                                 0
% 3.73/0.98  fd_pseudo_cond                          0
% 3.73/0.98  AC symbols                              0
% 3.73/0.98  
% 3.73/0.98  ------ Input Options Time Limit: Unbounded
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  ------ 
% 3.73/0.98  Current options:
% 3.73/0.98  ------ 
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  ------ Proving...
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  % SZS status Theorem for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  fof(f8,conjecture,(
% 3.73/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f9,negated_conjecture,(
% 3.73/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 3.73/0.98    inference(negated_conjecture,[],[f8])).
% 3.73/0.98  
% 3.73/0.98  fof(f23,plain,(
% 3.73/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f9])).
% 3.73/0.98  
% 3.73/0.98  fof(f24,plain,(
% 3.73/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.73/0.98    inference(flattening,[],[f23])).
% 3.73/0.98  
% 3.73/0.98  fof(f30,plain,(
% 3.73/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,sK5)),k3_tmap_1(X0,X1,X2,X4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f29,plain,(
% 3.73/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (? [X5] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,sK4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(sK4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f28,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X4,k3_tmap_1(X0,X1,X2,sK3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK3) & m1_pre_topc(sK3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f27,plain,(
% 3.73/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,sK2,X3,X5)),k3_tmap_1(X0,X1,sK2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,sK2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f26,plain,(
% 3.73/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X4,k3_tmap_1(X0,sK1,X2,X3,X5)),k3_tmap_1(X0,sK1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f25,plain,(
% 3.73/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X4,k3_tmap_1(sK0,X1,X2,X3,X5)),k3_tmap_1(sK0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f31,plain,(
% 3.73/0.98    (((((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK3) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f24,f30,f29,f28,f27,f26,f25])).
% 3.73/0.98  
% 3.73/0.98  fof(f53,plain,(
% 3.73/0.98    m1_pre_topc(sK3,sK2)),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f48,plain,(
% 3.73/0.98    m1_pre_topc(sK2,sK0)),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f57,plain,(
% 3.73/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f4,axiom,(
% 3.73/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f15,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f4])).
% 3.73/0.98  
% 3.73/0.98  fof(f16,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.73/0.98    inference(flattening,[],[f15])).
% 3.73/0.98  
% 3.73/0.98  fof(f35,plain,(
% 3.73/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f16])).
% 3.73/0.98  
% 3.73/0.98  fof(f7,axiom,(
% 3.73/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f21,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f7])).
% 3.73/0.98  
% 3.73/0.98  fof(f22,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.73/0.98    inference(flattening,[],[f21])).
% 3.73/0.98  
% 3.73/0.98  fof(f40,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f22])).
% 3.73/0.98  
% 3.73/0.98  fof(f44,plain,(
% 3.73/0.98    ~v2_struct_0(sK1)),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f45,plain,(
% 3.73/0.98    v2_pre_topc(sK1)),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f46,plain,(
% 3.73/0.98    l1_pre_topc(sK1)),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f55,plain,(
% 3.73/0.98    v1_funct_1(sK5)),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f56,plain,(
% 3.73/0.98    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f41,plain,(
% 3.73/0.98    ~v2_struct_0(sK0)),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f42,plain,(
% 3.73/0.98    v2_pre_topc(sK0)),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f43,plain,(
% 3.73/0.98    l1_pre_topc(sK0)),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f3,axiom,(
% 3.73/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f13,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f3])).
% 3.73/0.98  
% 3.73/0.98  fof(f14,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.73/0.98    inference(flattening,[],[f13])).
% 3.73/0.98  
% 3.73/0.98  fof(f34,plain,(
% 3.73/0.98    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f14])).
% 3.73/0.98  
% 3.73/0.98  fof(f47,plain,(
% 3.73/0.98    ~v2_struct_0(sK2)),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f2,axiom,(
% 3.73/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f12,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.73/0.98    inference(ennf_transformation,[],[f2])).
% 3.73/0.98  
% 3.73/0.98  fof(f33,plain,(
% 3.73/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f12])).
% 3.73/0.98  
% 3.73/0.98  fof(f1,axiom,(
% 3.73/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f10,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f1])).
% 3.73/0.98  
% 3.73/0.98  fof(f11,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.73/0.98    inference(flattening,[],[f10])).
% 3.73/0.98  
% 3.73/0.98  fof(f32,plain,(
% 3.73/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f11])).
% 3.73/0.98  
% 3.73/0.98  fof(f54,plain,(
% 3.73/0.98    m1_pre_topc(sK4,sK3)),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f58,plain,(
% 3.73/0.98    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f50,plain,(
% 3.73/0.98    m1_pre_topc(sK3,sK0)),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f5,axiom,(
% 3.73/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f17,plain,(
% 3.73/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f5])).
% 3.73/0.98  
% 3.73/0.98  fof(f18,plain,(
% 3.73/0.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.73/0.98    inference(flattening,[],[f17])).
% 3.73/0.98  
% 3.73/0.98  fof(f38,plain,(
% 3.73/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f18])).
% 3.73/0.98  
% 3.73/0.98  fof(f36,plain,(
% 3.73/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f18])).
% 3.73/0.98  
% 3.73/0.98  fof(f37,plain,(
% 3.73/0.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f18])).
% 3.73/0.98  
% 3.73/0.98  fof(f49,plain,(
% 3.73/0.98    ~v2_struct_0(sK3)),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  fof(f6,axiom,(
% 3.73/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))))))))),
% 3.73/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f19,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f6])).
% 3.73/0.98  
% 3.73/0.98  fof(f20,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.73/0.98    inference(flattening,[],[f19])).
% 3.73/0.98  
% 3.73/0.98  fof(f39,plain,(
% 3.73/0.98    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f20])).
% 3.73/0.98  
% 3.73/0.98  fof(f51,plain,(
% 3.73/0.98    ~v2_struct_0(sK4)),
% 3.73/0.98    inference(cnf_transformation,[],[f31])).
% 3.73/0.98  
% 3.73/0.98  cnf(c_14,negated_conjecture,
% 3.73/0.98      ( m1_pre_topc(sK3,sK2) ),
% 3.73/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_229,negated_conjecture,
% 3.73/0.98      ( m1_pre_topc(sK3,sK2) ),
% 3.73/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_684,plain,
% 3.73/0.98      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_19,negated_conjecture,
% 3.73/0.98      ( m1_pre_topc(sK2,sK0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_224,negated_conjecture,
% 3.73/0.98      ( m1_pre_topc(sK2,sK0) ),
% 3.73/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_689,plain,
% 3.73/0.98      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_10,negated_conjecture,
% 3.73/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 3.73/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_233,negated_conjecture,
% 3.73/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 3.73/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_680,plain,
% 3.73/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_233]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3,plain,
% 3.73/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.73/0.98      | ~ m1_pre_topc(X3,X4)
% 3.73/0.98      | ~ m1_pre_topc(X3,X1)
% 3.73/0.98      | ~ m1_pre_topc(X1,X4)
% 3.73/0.98      | v2_struct_0(X4)
% 3.73/0.98      | v2_struct_0(X2)
% 3.73/0.98      | ~ v1_funct_1(X0)
% 3.73/0.98      | ~ l1_pre_topc(X4)
% 3.73/0.98      | ~ l1_pre_topc(X2)
% 3.73/0.98      | ~ v2_pre_topc(X4)
% 3.73/0.98      | ~ v2_pre_topc(X2)
% 3.73/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_240,plain,
% 3.73/0.98      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.73/0.98      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.73/0.98      | ~ m1_pre_topc(X2_48,X0_48)
% 3.73/0.98      | ~ m1_pre_topc(X0_48,X3_48)
% 3.73/0.98      | ~ m1_pre_topc(X2_48,X3_48)
% 3.73/0.98      | v2_struct_0(X1_48)
% 3.73/0.98      | v2_struct_0(X3_48)
% 3.73/0.98      | ~ v1_funct_1(X0_49)
% 3.73/0.98      | ~ l1_pre_topc(X1_48)
% 3.73/0.98      | ~ l1_pre_topc(X3_48)
% 3.73/0.98      | ~ v2_pre_topc(X1_48)
% 3.73/0.98      | ~ v2_pre_topc(X3_48)
% 3.73/0.98      | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49) ),
% 3.73/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_673,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)
% 3.73/0.98      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.73/0.98      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.73/0.98      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X2_48,X3_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X3_48) = iProver_top
% 3.73/0.98      | v1_funct_1(X0_49) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X3_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X3_48) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_240]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_8,plain,
% 3.73/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.73/0.98      | ~ m1_pre_topc(X2,X0)
% 3.73/0.98      | m1_pre_topc(X2,X1)
% 3.73/0.98      | ~ l1_pre_topc(X1)
% 3.73/0.98      | ~ v2_pre_topc(X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_235,plain,
% 3.73/0.98      ( ~ m1_pre_topc(X0_48,X1_48)
% 3.73/0.98      | ~ m1_pre_topc(X2_48,X0_48)
% 3.73/0.98      | m1_pre_topc(X2_48,X1_48)
% 3.73/0.98      | ~ l1_pre_topc(X1_48)
% 3.73/0.98      | ~ v2_pre_topc(X1_48) ),
% 3.73/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_678,plain,
% 3.73/0.98      ( m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X2_48,X1_48) = iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_235]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_864,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)
% 3.73/0.98      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.73/0.98      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.73/0.98      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X3_48) = iProver_top
% 3.73/0.98      | v1_funct_1(X0_49) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X3_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X3_48) != iProver_top ),
% 3.73/0.98      inference(forward_subsumption_resolution,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_673,c_678]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3691,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
% 3.73/0.98      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,sK2) != iProver_top
% 3.73/0.98      | m1_pre_topc(sK2,X1_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(sK1) = iProver_top
% 3.73/0.98      | v1_funct_1(sK5) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_680,c_864]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_23,negated_conjecture,
% 3.73/0.98      ( ~ v2_struct_0(sK1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_30,plain,
% 3.73/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_22,negated_conjecture,
% 3.73/0.98      ( v2_pre_topc(sK1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_31,plain,
% 3.73/0.98      ( v2_pre_topc(sK1) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_21,negated_conjecture,
% 3.73/0.98      ( l1_pre_topc(sK1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_32,plain,
% 3.73/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_12,negated_conjecture,
% 3.73/0.98      ( v1_funct_1(sK5) ),
% 3.73/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_41,plain,
% 3.73/0.98      ( v1_funct_1(sK5) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_11,negated_conjecture,
% 3.73/0.98      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 3.73/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_42,plain,
% 3.73/0.98      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3872,plain,
% 3.73/0.98      ( v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
% 3.73/0.98      | m1_pre_topc(X0_48,sK2) != iProver_top
% 3.73/0.98      | m1_pre_topc(sK2,X1_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_3691,c_30,c_31,c_32,c_41,c_42]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3873,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
% 3.73/0.98      | m1_pre_topc(X0_48,sK2) != iProver_top
% 3.73/0.98      | m1_pre_topc(sK2,X1_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_3872]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3884,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(sK0,sK1,sK2,X0_48,sK5)
% 3.73/0.98      | m1_pre_topc(X0_48,sK2) != iProver_top
% 3.73/0.98      | v2_struct_0(sK0) = iProver_top
% 3.73/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.73/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_689,c_3873]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_26,negated_conjecture,
% 3.73/0.98      ( ~ v2_struct_0(sK0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_27,plain,
% 3.73/0.98      ( v2_struct_0(sK0) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_25,negated_conjecture,
% 3.73/0.98      ( v2_pre_topc(sK0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_28,plain,
% 3.73/0.98      ( v2_pre_topc(sK0) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_24,negated_conjecture,
% 3.73/0.98      ( l1_pre_topc(sK0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_29,plain,
% 3.73/0.98      ( l1_pre_topc(sK0) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3889,plain,
% 3.73/0.98      ( m1_pre_topc(X0_48,sK2) != iProver_top
% 3.73/0.98      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(sK0,sK1,sK2,X0_48,sK5) ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_3884,c_27,c_28,c_29]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3890,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(sK0,sK1,sK2,X0_48,sK5)
% 3.73/0.98      | m1_pre_topc(X0_48,sK2) != iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_3889]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3897,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK2,sK3,sK5) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_684,c_3890]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2,plain,
% 3.73/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.73/0.98      | ~ m1_pre_topc(X3,X1)
% 3.73/0.98      | v2_struct_0(X1)
% 3.73/0.98      | v2_struct_0(X2)
% 3.73/0.98      | ~ v1_funct_1(X0)
% 3.73/0.98      | ~ l1_pre_topc(X1)
% 3.73/0.98      | ~ l1_pre_topc(X2)
% 3.73/0.98      | ~ v2_pre_topc(X1)
% 3.73/0.98      | ~ v2_pre_topc(X2)
% 3.73/0.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.73/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_241,plain,
% 3.73/0.98      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.73/0.98      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.73/0.98      | ~ m1_pre_topc(X2_48,X0_48)
% 3.73/0.98      | v2_struct_0(X1_48)
% 3.73/0.98      | v2_struct_0(X0_48)
% 3.73/0.98      | ~ v1_funct_1(X0_49)
% 3.73/0.98      | ~ l1_pre_topc(X1_48)
% 3.73/0.98      | ~ l1_pre_topc(X0_48)
% 3.73/0.98      | ~ v2_pre_topc(X1_48)
% 3.73/0.98      | ~ v2_pre_topc(X0_48)
% 3.73/0.98      | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48) ),
% 3.73/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_672,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48)
% 3.73/0.98      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.73/0.98      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.73/0.98      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X0_48) = iProver_top
% 3.73/0.98      | v1_funct_1(X0_49) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X0_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X0_48) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_241]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2059,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48)
% 3.73/0.98      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,sK2) != iProver_top
% 3.73/0.98      | v2_struct_0(sK2) = iProver_top
% 3.73/0.98      | v2_struct_0(sK1) = iProver_top
% 3.73/0.98      | v1_funct_1(sK5) != iProver_top
% 3.73/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.73/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.73/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.73/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_680,c_672]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_20,negated_conjecture,
% 3.73/0.98      ( ~ v2_struct_0(sK2) ),
% 3.73/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_33,plain,
% 3.73/0.98      ( v2_struct_0(sK2) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_34,plain,
% 3.73/0.98      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1,plain,
% 3.73/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_242,plain,
% 3.73/0.98      ( ~ m1_pre_topc(X0_48,X1_48)
% 3.73/0.98      | ~ l1_pre_topc(X1_48)
% 3.73/0.98      | l1_pre_topc(X0_48) ),
% 3.73/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1418,plain,
% 3.73/0.98      ( ~ m1_pre_topc(sK2,X0_48)
% 3.73/0.98      | ~ l1_pre_topc(X0_48)
% 3.73/0.98      | l1_pre_topc(sK2) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_242]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1419,plain,
% 3.73/0.98      ( m1_pre_topc(sK2,X0_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X0_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(sK2) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_1418]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1421,plain,
% 3.73/0.98      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.73/0.98      | l1_pre_topc(sK2) = iProver_top
% 3.73/0.98      | l1_pre_topc(sK0) != iProver_top ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1419]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_0,plain,
% 3.73/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.73/0.98      | ~ l1_pre_topc(X1)
% 3.73/0.98      | ~ v2_pre_topc(X1)
% 3.73/0.98      | v2_pre_topc(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_243,plain,
% 3.73/0.98      ( ~ m1_pre_topc(X0_48,X1_48)
% 3.73/0.98      | ~ l1_pre_topc(X1_48)
% 3.73/0.98      | ~ v2_pre_topc(X1_48)
% 3.73/0.98      | v2_pre_topc(X0_48) ),
% 3.73/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_670,plain,
% 3.73/0.98      ( m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X0_48) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_243]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1455,plain,
% 3.73/0.98      ( l1_pre_topc(sK0) != iProver_top
% 3.73/0.98      | v2_pre_topc(sK2) = iProver_top
% 3.73/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_689,c_670]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3367,plain,
% 3.73/0.98      ( m1_pre_topc(X0_48,sK2) != iProver_top
% 3.73/0.98      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48) ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_2059,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_41,c_42,
% 3.73/0.98                 c_1421,c_1455]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3368,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48)
% 3.73/0.98      | m1_pre_topc(X0_48,sK2) != iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_3367]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3375,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_684,c_3368]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3903,plain,
% 3.73/0.98      ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
% 3.73/0.98      inference(light_normalisation,[status(thm)],[c_3897,c_3375]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_13,negated_conjecture,
% 3.73/0.98      ( m1_pre_topc(sK4,sK3) ),
% 3.73/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_230,negated_conjecture,
% 3.73/0.98      ( m1_pre_topc(sK4,sK3) ),
% 3.73/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_683,plain,
% 3.73/0.98      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_230]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1988,plain,
% 3.73/0.98      ( m1_pre_topc(X0_48,sK2) = iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.73/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.73/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_684,c_678]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2941,plain,
% 3.73/0.98      ( m1_pre_topc(X0_48,sK2) = iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,sK3) != iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_1988,c_28,c_29,c_34,c_1421,c_1455]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2949,plain,
% 3.73/0.98      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_683,c_2941]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3898,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK2,sK4,sK5) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_2949,c_3890]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3376,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_2949,c_3368]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3900,plain,
% 3.73/0.98      ( k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
% 3.73/0.98      inference(light_normalisation,[status(thm)],[c_3898,c_3376]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_9,negated_conjecture,
% 3.73/0.98      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
% 3.73/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_234,negated_conjecture,
% 3.73/0.98      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
% 3.73/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_679,plain,
% 3.73/0.98      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_234]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6330,plain,
% 3.73/0.98      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k2_tmap_1(sK2,sK1,sK5,sK4)) != iProver_top ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_3900,c_679]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6941,plain,
% 3.73/0.98      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4)) != iProver_top ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_3903,c_6330]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_17,negated_conjecture,
% 3.73/0.98      ( m1_pre_topc(sK3,sK0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_226,negated_conjecture,
% 3.73/0.98      ( m1_pre_topc(sK3,sK0) ),
% 3.73/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_687,plain,
% 3.73/0.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4,plain,
% 3.73/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.73/0.98      | m1_subset_1(k3_tmap_1(X3,X2,X1,X4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 3.73/0.98      | ~ m1_pre_topc(X4,X3)
% 3.73/0.98      | ~ m1_pre_topc(X1,X3)
% 3.73/0.98      | v2_struct_0(X3)
% 3.73/0.98      | v2_struct_0(X2)
% 3.73/0.98      | ~ v1_funct_1(X0)
% 3.73/0.98      | ~ l1_pre_topc(X3)
% 3.73/0.98      | ~ l1_pre_topc(X2)
% 3.73/0.98      | ~ v2_pre_topc(X3)
% 3.73/0.98      | ~ v2_pre_topc(X2) ),
% 3.73/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_239,plain,
% 3.73/0.98      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.73/0.98      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.73/0.98      | m1_subset_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48))))
% 3.73/0.98      | ~ m1_pre_topc(X3_48,X2_48)
% 3.73/0.98      | ~ m1_pre_topc(X0_48,X2_48)
% 3.73/0.98      | v2_struct_0(X2_48)
% 3.73/0.98      | v2_struct_0(X1_48)
% 3.73/0.98      | ~ v1_funct_1(X0_49)
% 3.73/0.98      | ~ l1_pre_topc(X1_48)
% 3.73/0.98      | ~ l1_pre_topc(X2_48)
% 3.73/0.98      | ~ v2_pre_topc(X1_48)
% 3.73/0.98      | ~ v2_pre_topc(X2_48) ),
% 3.73/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_674,plain,
% 3.73/0.98      ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.73/0.98      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.73/0.98      | m1_subset_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) = iProver_top
% 3.73/0.98      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X2_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v1_funct_1(X0_49) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X2_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X2_48) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3692,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k3_tmap_1(X5_48,X1_48,X0_48,X4_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49))
% 3.73/0.98      | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
% 3.73/0.98      | v1_funct_2(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.73/0.98      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
% 3.73/0.98      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X5_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X4_48,X0_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X2_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X5_48) = iProver_top
% 3.73/0.98      | v1_funct_1(X0_49) != iProver_top
% 3.73/0.98      | v1_funct_1(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49)) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X2_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X5_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X2_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X5_48) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_674,c_864]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6,plain,
% 3.73/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.73/0.98      | ~ m1_pre_topc(X3,X4)
% 3.73/0.98      | ~ m1_pre_topc(X1,X4)
% 3.73/0.98      | v2_struct_0(X4)
% 3.73/0.98      | v2_struct_0(X2)
% 3.73/0.98      | ~ v1_funct_1(X0)
% 3.73/0.98      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0))
% 3.73/0.98      | ~ l1_pre_topc(X4)
% 3.73/0.98      | ~ l1_pre_topc(X2)
% 3.73/0.98      | ~ v2_pre_topc(X4)
% 3.73/0.98      | ~ v2_pre_topc(X2) ),
% 3.73/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_237,plain,
% 3.73/0.98      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.73/0.98      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.73/0.98      | ~ m1_pre_topc(X0_48,X2_48)
% 3.73/0.98      | ~ m1_pre_topc(X3_48,X2_48)
% 3.73/0.98      | v2_struct_0(X1_48)
% 3.73/0.98      | v2_struct_0(X2_48)
% 3.73/0.98      | ~ v1_funct_1(X0_49)
% 3.73/0.98      | v1_funct_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49))
% 3.73/0.98      | ~ l1_pre_topc(X1_48)
% 3.73/0.98      | ~ l1_pre_topc(X2_48)
% 3.73/0.98      | ~ v2_pre_topc(X1_48)
% 3.73/0.98      | ~ v2_pre_topc(X2_48) ),
% 3.73/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_676,plain,
% 3.73/0.98      ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.73/0.98      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.73/0.98      | m1_pre_topc(X2_48,X3_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X3_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v1_funct_1(X0_49) != iProver_top
% 3.73/0.98      | v1_funct_1(k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)) = iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X3_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X3_48) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_237]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5,plain,
% 3.73/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.73/0.98      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.73/0.98      | ~ m1_pre_topc(X4,X3)
% 3.73/0.98      | ~ m1_pre_topc(X1,X3)
% 3.73/0.98      | v2_struct_0(X3)
% 3.73/0.98      | v2_struct_0(X2)
% 3.73/0.98      | ~ v1_funct_1(X0)
% 3.73/0.98      | ~ l1_pre_topc(X3)
% 3.73/0.98      | ~ l1_pre_topc(X2)
% 3.73/0.98      | ~ v2_pre_topc(X3)
% 3.73/0.98      | ~ v2_pre_topc(X2) ),
% 3.73/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_238,plain,
% 3.73/0.98      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.73/0.98      | v1_funct_2(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),u1_struct_0(X3_48),u1_struct_0(X1_48))
% 3.73/0.98      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.73/0.98      | ~ m1_pre_topc(X3_48,X2_48)
% 3.73/0.98      | ~ m1_pre_topc(X0_48,X2_48)
% 3.73/0.98      | v2_struct_0(X2_48)
% 3.73/0.98      | v2_struct_0(X1_48)
% 3.73/0.98      | ~ v1_funct_1(X0_49)
% 3.73/0.98      | ~ l1_pre_topc(X1_48)
% 3.73/0.98      | ~ l1_pre_topc(X2_48)
% 3.73/0.98      | ~ v2_pre_topc(X1_48)
% 3.73/0.98      | ~ v2_pre_topc(X2_48) ),
% 3.73/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_675,plain,
% 3.73/0.98      ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.73/0.98      | v1_funct_2(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),u1_struct_0(X3_48),u1_struct_0(X1_48)) = iProver_top
% 3.73/0.98      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.73/0.98      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X2_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v1_funct_1(X0_49) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X2_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X2_48) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_238]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4984,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k3_tmap_1(X5_48,X1_48,X0_48,X4_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49))
% 3.73/0.98      | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
% 3.73/0.98      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
% 3.73/0.98      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X4_48,X0_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X5_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X2_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X5_48) = iProver_top
% 3.73/0.98      | v1_funct_1(X0_49) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X2_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X5_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X2_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X5_48) != iProver_top ),
% 3.73/0.98      inference(forward_subsumption_resolution,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_3692,c_676,c_675]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4988,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k3_tmap_1(X3_48,sK1,X0_48,X2_48,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5))
% 3.73/0.98      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(sK2,X1_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X3_48) = iProver_top
% 3.73/0.98      | v2_struct_0(sK1) = iProver_top
% 3.73/0.98      | v1_funct_1(sK5) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X3_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X3_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_680,c_4984]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5077,plain,
% 3.73/0.98      ( v2_pre_topc(X3_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k3_tmap_1(X3_48,sK1,X0_48,X2_48,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5))
% 3.73/0.98      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(sK2,X1_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X3_48) = iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X3_48) != iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_4988,c_30,c_31,c_32,c_41,c_42]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5078,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k3_tmap_1(X3_48,sK1,X0_48,X2_48,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5))
% 3.73/0.98      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(sK2,X1_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X3_48) = iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X3_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X3_48) != iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_5077]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5097,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
% 3.73/0.98      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.73/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.73/0.98      | m1_pre_topc(sK3,X1_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(sK0) = iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_687,c_5078]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6227,plain,
% 3.73/0.98      ( v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | m1_pre_topc(sK3,X1_48) != iProver_top
% 3.73/0.98      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
% 3.73/0.98      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_5097,c_27,c_28,c_29,c_34]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6228,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
% 3.73/0.98      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.73/0.98      | m1_pre_topc(sK3,X1_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_6227]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6240,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(sK0,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
% 3.73/0.98      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.73/0.98      | v2_struct_0(sK0) = iProver_top
% 3.73/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.73/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_687,c_6228]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6567,plain,
% 3.73/0.98      ( m1_pre_topc(X0_48,sK3) != iProver_top
% 3.73/0.98      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(sK0,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_6240,c_27,c_28,c_29]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6568,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(sK0,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
% 3.73/0.98      | m1_pre_topc(X0_48,sK3) != iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_6567]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6575,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_683,c_6568]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2801,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k2_tmap_1(X0_48,X1_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),X4_48)
% 3.73/0.98      | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
% 3.73/0.98      | v1_funct_2(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.73/0.98      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
% 3.73/0.98      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X4_48,X0_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X0_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X2_48) = iProver_top
% 3.73/0.98      | v1_funct_1(X0_49) != iProver_top
% 3.73/0.98      | v1_funct_1(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49)) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X0_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X2_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X0_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X2_48) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_674,c_672]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_671,plain,
% 3.73/0.98      ( m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X0_48) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_242]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4030,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k2_tmap_1(X0_48,X1_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),X4_48)
% 3.73/0.98      | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
% 3.73/0.98      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
% 3.73/0.98      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X4_48,X0_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X2_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X0_48) = iProver_top
% 3.73/0.98      | v1_funct_1(X0_49) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X2_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X2_48) != iProver_top ),
% 3.73/0.98      inference(forward_subsumption_resolution,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_2801,c_670,c_671,c_676,c_675]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4034,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k2_tmap_1(X0_48,sK1,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),X2_48)
% 3.73/0.98      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(sK2,X1_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X0_48) = iProver_top
% 3.73/0.98      | v2_struct_0(sK1) = iProver_top
% 3.73/0.98      | v1_funct_1(sK5) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_680,c_4030]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4269,plain,
% 3.73/0.98      ( v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k2_tmap_1(X0_48,sK1,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),X2_48)
% 3.73/0.98      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(sK2,X1_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X0_48) = iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_4034,c_30,c_31,c_32,c_41,c_42]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4270,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),u1_struct_0(X2_48)) = k2_tmap_1(X0_48,sK1,k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5),X2_48)
% 3.73/0.98      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(sK2,X1_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X0_48) = iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_4269]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4286,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK3,sK5),X0_48)
% 3.73/0.98      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.73/0.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.73/0.98      | v2_struct_0(sK3) = iProver_top
% 3.73/0.98      | v2_struct_0(sK0) = iProver_top
% 3.73/0.98      | l1_pre_topc(sK0) != iProver_top
% 3.73/0.98      | v2_pre_topc(sK0) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_687,c_4270]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_18,negated_conjecture,
% 3.73/0.98      ( ~ v2_struct_0(sK3) ),
% 3.73/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_35,plain,
% 3.73/0.98      ( v2_struct_0(sK3) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4634,plain,
% 3.73/0.98      ( m1_pre_topc(X0_48,sK3) != iProver_top
% 3.73/0.98      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK3,sK5),X0_48) ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_4286,c_27,c_28,c_29,c_34,c_35]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4635,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK3,sK5),X0_48)
% 3.73/0.98      | m1_pre_topc(X0_48,sK3) != iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_4634]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4642,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK4)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK3,sK5),sK4) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_683,c_4635]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6576,plain,
% 3.73/0.98      ( k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK3,sK5),sK4) ),
% 3.73/0.98      inference(light_normalisation,[status(thm)],[c_6575,c_4642]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_7387,plain,
% 3.73/0.98      ( k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
% 3.73/0.98      inference(light_normalisation,[status(thm)],[c_6576,c_3903]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_7786,plain,
% 3.73/0.98      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) != iProver_top ),
% 3.73/0.98      inference(light_normalisation,[status(thm)],[c_6941,c_7387]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6239,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(sK2,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
% 3.73/0.98      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.73/0.98      | v2_struct_0(sK2) = iProver_top
% 3.73/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.73/0.98      | v2_pre_topc(sK2) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_684,c_6228]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6315,plain,
% 3.73/0.98      ( m1_pre_topc(X0_48,sK3) != iProver_top
% 3.73/0.98      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(sK2,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_6239,c_28,c_29,c_33,c_34,c_1421,c_1455]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6316,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(sK2,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
% 3.73/0.98      | m1_pre_topc(X0_48,sK3) != iProver_top ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_6315]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6323,plain,
% 3.73/0.98      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(sK4)) = k3_tmap_1(sK2,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_683,c_6316]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6324,plain,
% 3.73/0.98      ( k3_tmap_1(sK2,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK3,sK5),sK4) ),
% 3.73/0.98      inference(light_normalisation,[status(thm)],[c_6323,c_4642]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_7089,plain,
% 3.73/0.98      ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
% 3.73/0.98      inference(light_normalisation,[status(thm)],[c_6324,c_3903]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_7,plain,
% 3.73/0.98      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,k2_tmap_1(X2,X1,X4,X3)),k2_tmap_1(X2,X1,X4,X0))
% 3.73/0.98      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
% 3.73/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.73/0.98      | ~ m1_pre_topc(X3,X2)
% 3.73/0.98      | ~ m1_pre_topc(X0,X2)
% 3.73/0.98      | ~ m1_pre_topc(X0,X3)
% 3.73/0.98      | v2_struct_0(X2)
% 3.73/0.98      | v2_struct_0(X1)
% 3.73/0.98      | v2_struct_0(X0)
% 3.73/0.98      | v2_struct_0(X3)
% 3.73/0.98      | ~ v1_funct_1(X4)
% 3.73/0.98      | ~ l1_pre_topc(X2)
% 3.73/0.98      | ~ l1_pre_topc(X1)
% 3.73/0.98      | ~ v2_pre_topc(X2)
% 3.73/0.98      | ~ v2_pre_topc(X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_236,plain,
% 3.73/0.98      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,k2_tmap_1(X2_48,X1_48,X0_49,X3_48)),k2_tmap_1(X2_48,X1_48,X0_49,X0_48))
% 3.73/0.98      | ~ v1_funct_2(X0_49,u1_struct_0(X2_48),u1_struct_0(X1_48))
% 3.73/0.98      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
% 3.73/0.98      | ~ m1_pre_topc(X3_48,X2_48)
% 3.73/0.98      | ~ m1_pre_topc(X0_48,X2_48)
% 3.73/0.98      | ~ m1_pre_topc(X0_48,X3_48)
% 3.73/0.98      | v2_struct_0(X2_48)
% 3.73/0.98      | v2_struct_0(X1_48)
% 3.73/0.98      | v2_struct_0(X0_48)
% 3.73/0.98      | v2_struct_0(X3_48)
% 3.73/0.98      | ~ v1_funct_1(X0_49)
% 3.73/0.98      | ~ l1_pre_topc(X1_48)
% 3.73/0.98      | ~ l1_pre_topc(X2_48)
% 3.73/0.98      | ~ v2_pre_topc(X1_48)
% 3.73/0.98      | ~ v2_pre_topc(X2_48) ),
% 3.73/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_677,plain,
% 3.73/0.98      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,k2_tmap_1(X2_48,X1_48,X0_49,X3_48)),k2_tmap_1(X2_48,X1_48,X0_49,X0_48)) = iProver_top
% 3.73/0.98      | v1_funct_2(X0_49,u1_struct_0(X2_48),u1_struct_0(X1_48)) != iProver_top
% 3.73/0.98      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48)))) != iProver_top
% 3.73/0.98      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X2_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X0_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X3_48) = iProver_top
% 3.73/0.98      | v1_funct_1(X0_49) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X2_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X2_48) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_892,plain,
% 3.73/0.98      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,k2_tmap_1(X2_48,X1_48,X0_49,X3_48)),k2_tmap_1(X2_48,X1_48,X0_49,X0_48)) = iProver_top
% 3.73/0.98      | v1_funct_2(X0_49,u1_struct_0(X2_48),u1_struct_0(X1_48)) != iProver_top
% 3.73/0.98      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48)))) != iProver_top
% 3.73/0.98      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 3.73/0.98      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 3.73/0.98      | v2_struct_0(X2_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X1_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X0_48) = iProver_top
% 3.73/0.98      | v2_struct_0(X3_48) = iProver_top
% 3.73/0.98      | v1_funct_1(X0_49) != iProver_top
% 3.73/0.98      | l1_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | l1_pre_topc(X2_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X1_48) != iProver_top
% 3.73/0.98      | v2_pre_topc(X2_48) != iProver_top ),
% 3.73/0.98      inference(forward_subsumption_resolution,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_677,c_678]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_7091,plain,
% 3.73/0.98      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) = iProver_top
% 3.73/0.98      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/0.98      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.73/0.98      | m1_pre_topc(sK4,sK3) != iProver_top
% 3.73/0.98      | v2_struct_0(sK2) = iProver_top
% 3.73/0.98      | v2_struct_0(sK3) = iProver_top
% 3.73/0.98      | v2_struct_0(sK1) = iProver_top
% 3.73/0.98      | v2_struct_0(sK4) = iProver_top
% 3.73/0.98      | v1_funct_1(sK5) != iProver_top
% 3.73/0.98      | l1_pre_topc(sK2) != iProver_top
% 3.73/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.73/0.98      | v2_pre_topc(sK2) != iProver_top
% 3.73/0.98      | v2_pre_topc(sK1) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_7089,c_892]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_43,plain,
% 3.73/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_40,plain,
% 3.73/0.98      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_39,plain,
% 3.73/0.98      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_16,negated_conjecture,
% 3.73/0.98      ( ~ v2_struct_0(sK4) ),
% 3.73/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_37,plain,
% 3.73/0.98      ( v2_struct_0(sK4) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(contradiction,plain,
% 3.73/0.98      ( $false ),
% 3.73/0.98      inference(minisat,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_7786,c_7091,c_1455,c_1421,c_43,c_42,c_41,c_40,c_39,
% 3.73/0.98                 c_37,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_28]) ).
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  ------                               Statistics
% 3.73/0.98  
% 3.73/0.98  ------ Selected
% 3.73/0.98  
% 3.73/0.98  total_time:                             0.351
% 3.73/0.98  
%------------------------------------------------------------------------------
