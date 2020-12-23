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
% DateTime   : Thu Dec  3 12:23:00 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  205 (18348 expanded)
%              Number of clauses        :  141 (3808 expanded)
%              Number of leaves         :   15 (8214 expanded)
%              Depth                    :   25
%              Number of atoms          : 1296 (275835 expanded)
%              Number of equality atoms :  494 (6857 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal clause size      :   36 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f27,f34,f33,f32,f31,f30,f29])).

fof(f60,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f37])).

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
                         => ( ( m1_pre_topc(X3,X2)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) )
                           => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
                          | ~ m1_pre_topc(X3,X2)
                          | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
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
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
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
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_306,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_809,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_302,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_813,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_309,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_806,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f41])).

cnf(c_316,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_pre_topc(X2_48,X0_48)
    | ~ m1_pre_topc(X0_48,X3_48)
    | ~ m1_pre_topc(X2_48,X3_48)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | v2_struct_0(X3_48)
    | v2_struct_0(X1_48)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X3_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X3_48)
    | ~ v1_funct_1(X0_49)
    | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_799,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X3_48) != iProver_top
    | m1_pre_topc(X2_48,X3_48) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X3_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X3_48) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_1876,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_806,c_799])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_32,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_33,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_34,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_43,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_44,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2470,plain,
    ( l1_pre_topc(X1_48) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1876,c_32,c_33,c_34,c_43,c_44])).

cnf(c_2471,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_2470])).

cnf(c_2479,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK2,sK3,sK5)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_813,c_2471])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_305,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_810,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_4,plain,
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
    inference(cnf_transformation,[],[f40])).

cnf(c_317,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_pre_topc(X2_48,X0_48)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | v2_struct_0(X1_48)
    | v2_struct_0(X0_48)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X0_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X0_48)
    | ~ v1_funct_1(X0_49)
    | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_798,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48)
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X0_48) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_1709,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48)
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_806,c_798])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_30,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_31,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_35,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_36,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_318,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1108,plain,
    ( ~ m1_pre_topc(sK2,X0_48)
    | ~ l1_pre_topc(X0_48)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_1109,plain,
    ( m1_pre_topc(sK2,X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1108])).

cnf(c_1111,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_319,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v2_pre_topc(X1_48)
    | v2_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1298,plain,
    ( ~ m1_pre_topc(sK2,X0_48)
    | ~ l1_pre_topc(X0_48)
    | ~ v2_pre_topc(X0_48)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_1299,plain,
    ( m1_pre_topc(sK2,X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1298])).

cnf(c_1301,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1299])).

cnf(c_2288,plain,
    ( m1_pre_topc(X0_48,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1709,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_43,c_44,c_1111,c_1301])).

cnf(c_2289,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48)
    | m1_pre_topc(X0_48,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2288])).

cnf(c_2294,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
    inference(superposition,[status(thm)],[c_810,c_2289])).

cnf(c_2483,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2479,c_2294])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_29,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_41,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2548,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2483,c_29,c_30,c_31,c_36,c_41])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_315,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_pre_topc(X0_48,X2_48)
    | ~ m1_pre_topc(X3_48,X2_48)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | m1_subset_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48))))
    | v2_struct_0(X2_48)
    | v2_struct_0(X1_48)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X2_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48)
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_800,plain,
    ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_1957,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k2_tmap_1(X0_48,X1_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),X4_48)
    | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_pre_topc(X4_48,X0_48) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49)) != iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_798])).

cnf(c_3980,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK3,sK5),X0_48)
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2548,c_1957])).

cnf(c_3993,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_48)
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3980,c_2548])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_37,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_38,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_45,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1114,plain,
    ( ~ m1_pre_topc(sK3,X0_48)
    | ~ l1_pre_topc(X0_48)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_1115,plain,
    ( m1_pre_topc(sK3,X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1114])).

cnf(c_1117,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_1293,plain,
    ( ~ m1_pre_topc(sK3,X0_48)
    | ~ l1_pre_topc(X0_48)
    | ~ v2_pre_topc(X0_48)
    | v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_1294,plain,
    ( m1_pre_topc(sK3,X0_48) != iProver_top
    | l1_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(X0_48) != iProver_top
    | v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1293])).

cnf(c_1296,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1294])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_314,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | v1_funct_2(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),u1_struct_0(X3_48),u1_struct_0(X1_48))
    | ~ m1_pre_topc(X3_48,X2_48)
    | ~ m1_pre_topc(X0_48,X2_48)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | v2_struct_0(X1_48)
    | v2_struct_0(X2_48)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X2_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48)
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_801,plain,
    ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),u1_struct_0(X3_48),u1_struct_0(X1_48)) = iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_2553,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2548,c_801])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_313,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ m1_pre_topc(X0_48,X2_48)
    | ~ m1_pre_topc(X3_48,X2_48)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | v2_struct_0(X2_48)
    | v2_struct_0(X1_48)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X2_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48)
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_802,plain,
    ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_1714,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_806,c_802])).

cnf(c_2463,plain,
    ( v1_funct_1(k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1714,c_32,c_33,c_34,c_43,c_44])).

cnf(c_2464,plain,
    ( m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(sK2,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2463])).

cnf(c_2554,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2548,c_2464])).

cnf(c_2552,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2548,c_800])).

cnf(c_3048,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2552,c_29,c_30,c_31,c_32,c_33,c_34,c_36,c_38,c_43,c_44,c_45])).

cnf(c_3054,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_48)
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3048,c_798])).

cnf(c_5210,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_48)
    | m1_pre_topc(X0_48,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3993,c_29,c_30,c_31,c_32,c_33,c_34,c_36,c_37,c_38,c_43,c_44,c_45,c_1117,c_1296,c_2553,c_2554,c_3054])).

cnf(c_5216,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
    inference(superposition,[status(thm)],[c_809,c_5210])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_304,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_811,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_1955,plain,
    ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k3_tmap_1(X5_48,X1_48,X0_48,X4_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49))
    | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | m1_pre_topc(X4_48,X0_48) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | m1_pre_topc(X0_48,X5_48) != iProver_top
    | m1_pre_topc(X4_48,X5_48) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X5_48) = iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | l1_pre_topc(X5_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X5_48) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49)) != iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_799])).

cnf(c_3006,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,X1_48) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2548,c_1955])).

cnf(c_3019,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK3,X1_48) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3006,c_2548])).

cnf(c_3052,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3048,c_799])).

cnf(c_3717,plain,
    ( m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(sK3,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3019,c_29,c_30,c_31,c_32,c_33,c_34,c_36,c_38,c_43,c_44,c_45,c_2553,c_2554,c_3052])).

cnf(c_3718,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK3,X1_48) != iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_3717])).

cnf(c_3725,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_811,c_3718])).

cnf(c_42,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3909,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3725,c_29,c_30,c_31,c_38,c_42])).

cnf(c_5553,plain,
    ( k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
    inference(demodulation,[status(thm)],[c_5216,c_3909])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_311,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ m1_pre_topc(X2_48,X0_48)
    | m1_pre_topc(X2_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | ~ v2_pre_topc(X1_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_804,plain,
    ( m1_pre_topc(X0_48,X1_48) != iProver_top
    | m1_pre_topc(X2_48,X0_48) != iProver_top
    | m1_pre_topc(X2_48,X1_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_1689,plain,
    ( m1_pre_topc(X0_48,sK2) = iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_810,c_804])).

cnf(c_1322,plain,
    ( m1_pre_topc(X0_48,sK2)
    | ~ m1_pre_topc(X0_48,sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_1323,plain,
    ( m1_pre_topc(X0_48,sK2) = iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1322])).

cnf(c_2068,plain,
    ( m1_pre_topc(X0_48,sK2) = iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1689,c_30,c_31,c_36,c_41,c_1111,c_1301,c_1323])).

cnf(c_2074,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_2068])).

cnf(c_3728,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2074,c_3718])).

cnf(c_4712,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3728,c_30,c_31,c_35,c_36,c_41,c_42,c_1111,c_1301])).

cnf(c_4714,plain,
    ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_4712,c_3909])).

cnf(c_5603,plain,
    ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
    inference(demodulation,[status(thm)],[c_5553,c_4714])).

cnf(c_0,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_321,plain,
    ( r2_funct_2(X0_50,X1_50,X0_49,X0_49)
    | ~ v1_funct_2(X0_49,X0_50,X1_50)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_794,plain,
    ( r2_funct_2(X0_50,X1_50,X0_49,X0_49) = iProver_top
    | v1_funct_2(X0_49,X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_3056,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3048,c_794])).

cnf(c_3083,plain,
    ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3056,c_29,c_30,c_31,c_32,c_33,c_34,c_36,c_38,c_43,c_44,c_45,c_2553,c_2554])).

cnf(c_9,plain,
    ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
    | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_pre_topc(X5,X3)
    | ~ m1_pre_topc(X5,X0)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_312,plain,
    ( ~ r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k2_tmap_1(X2_48,X1_48,X1_49,X0_48))
    | r2_funct_2(u1_struct_0(X3_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k2_tmap_1(X2_48,X1_48,X1_49,X3_48))
    | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
    | ~ v1_funct_2(X1_49,u1_struct_0(X2_48),u1_struct_0(X1_48))
    | ~ m1_pre_topc(X3_48,X2_48)
    | ~ m1_pre_topc(X3_48,X0_48)
    | ~ m1_pre_topc(X0_48,X2_48)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
    | v2_struct_0(X3_48)
    | v2_struct_0(X1_48)
    | v2_struct_0(X0_48)
    | v2_struct_0(X2_48)
    | ~ l1_pre_topc(X1_48)
    | ~ l1_pre_topc(X2_48)
    | ~ v2_pre_topc(X1_48)
    | ~ v2_pre_topc(X2_48)
    | ~ v1_funct_1(X1_49)
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_803,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k2_tmap_1(X2_48,X1_48,X1_49,X0_48)) != iProver_top
    | r2_funct_2(u1_struct_0(X3_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k2_tmap_1(X2_48,X1_48,X1_49,X3_48)) = iProver_top
    | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
    | v1_funct_2(X1_49,u1_struct_0(X2_48),u1_struct_0(X1_48)) != iProver_top
    | m1_pre_topc(X3_48,X0_48) != iProver_top
    | m1_pre_topc(X0_48,X2_48) != iProver_top
    | m1_pre_topc(X3_48,X2_48) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
    | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48)))) != iProver_top
    | v2_struct_0(X3_48) = iProver_top
    | v2_struct_0(X1_48) = iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(X2_48) = iProver_top
    | l1_pre_topc(X1_48) != iProver_top
    | l1_pre_topc(X2_48) != iProver_top
    | v2_pre_topc(X1_48) != iProver_top
    | v2_pre_topc(X2_48) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_312])).

cnf(c_3087,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_48,sK2) != iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_48) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3083,c_803])).

cnf(c_7415,plain,
    ( v2_struct_0(X0_48) = iProver_top
    | r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3087,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_41,c_43,c_44,c_45,c_1111,c_1301,c_2068,c_2552,c_2553,c_2554])).

cnf(c_7416,plain,
    ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
    | m1_pre_topc(X0_48,sK3) != iProver_top
    | v2_struct_0(X0_48) = iProver_top ),
    inference(renaming,[status(thm)],[c_7415])).

cnf(c_7421,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) = iProver_top
    | m1_pre_topc(sK4,sK3) != iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5603,c_7416])).

cnf(c_2478,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK2,sK4,sK5)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_811,c_2471])).

cnf(c_2295,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_2074,c_2289])).

cnf(c_2484,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2478,c_2295])).

cnf(c_2671,plain,
    ( k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2484,c_29,c_30,c_31,c_36,c_2074])).

cnf(c_11,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_310,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_805,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_2550,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2548,c_805])).

cnf(c_2673,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2671,c_2550])).

cnf(c_5605,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5553,c_2673])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_39,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7421,c_5605,c_42,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.74/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.00  
% 3.74/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.74/1.00  
% 3.74/1.00  ------  iProver source info
% 3.74/1.00  
% 3.74/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.74/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.74/1.00  git: non_committed_changes: false
% 3.74/1.00  git: last_make_outside_of_git: false
% 3.74/1.00  
% 3.74/1.00  ------ 
% 3.74/1.00  
% 3.74/1.00  ------ Input Options
% 3.74/1.00  
% 3.74/1.00  --out_options                           all
% 3.74/1.00  --tptp_safe_out                         true
% 3.74/1.00  --problem_path                          ""
% 3.74/1.00  --include_path                          ""
% 3.74/1.00  --clausifier                            res/vclausify_rel
% 3.74/1.00  --clausifier_options                    ""
% 3.74/1.00  --stdin                                 false
% 3.74/1.00  --stats_out                             all
% 3.74/1.00  
% 3.74/1.00  ------ General Options
% 3.74/1.00  
% 3.74/1.00  --fof                                   false
% 3.74/1.00  --time_out_real                         305.
% 3.74/1.00  --time_out_virtual                      -1.
% 3.74/1.00  --symbol_type_check                     false
% 3.74/1.00  --clausify_out                          false
% 3.74/1.00  --sig_cnt_out                           false
% 3.74/1.00  --trig_cnt_out                          false
% 3.74/1.00  --trig_cnt_out_tolerance                1.
% 3.74/1.00  --trig_cnt_out_sk_spl                   false
% 3.74/1.00  --abstr_cl_out                          false
% 3.74/1.00  
% 3.74/1.00  ------ Global Options
% 3.74/1.00  
% 3.74/1.00  --schedule                              default
% 3.74/1.00  --add_important_lit                     false
% 3.74/1.00  --prop_solver_per_cl                    1000
% 3.74/1.00  --min_unsat_core                        false
% 3.74/1.00  --soft_assumptions                      false
% 3.74/1.00  --soft_lemma_size                       3
% 3.74/1.00  --prop_impl_unit_size                   0
% 3.74/1.00  --prop_impl_unit                        []
% 3.74/1.00  --share_sel_clauses                     true
% 3.74/1.00  --reset_solvers                         false
% 3.74/1.00  --bc_imp_inh                            [conj_cone]
% 3.74/1.00  --conj_cone_tolerance                   3.
% 3.74/1.00  --extra_neg_conj                        none
% 3.74/1.00  --large_theory_mode                     true
% 3.74/1.00  --prolific_symb_bound                   200
% 3.74/1.00  --lt_threshold                          2000
% 3.74/1.00  --clause_weak_htbl                      true
% 3.74/1.00  --gc_record_bc_elim                     false
% 3.74/1.00  
% 3.74/1.00  ------ Preprocessing Options
% 3.74/1.00  
% 3.74/1.00  --preprocessing_flag                    true
% 3.74/1.00  --time_out_prep_mult                    0.1
% 3.74/1.00  --splitting_mode                        input
% 3.74/1.00  --splitting_grd                         true
% 3.74/1.00  --splitting_cvd                         false
% 3.74/1.00  --splitting_cvd_svl                     false
% 3.74/1.00  --splitting_nvd                         32
% 3.74/1.00  --sub_typing                            true
% 3.74/1.00  --prep_gs_sim                           true
% 3.74/1.00  --prep_unflatten                        true
% 3.74/1.00  --prep_res_sim                          true
% 3.74/1.00  --prep_upred                            true
% 3.74/1.00  --prep_sem_filter                       exhaustive
% 3.74/1.00  --prep_sem_filter_out                   false
% 3.74/1.00  --pred_elim                             true
% 3.74/1.00  --res_sim_input                         true
% 3.74/1.00  --eq_ax_congr_red                       true
% 3.74/1.00  --pure_diseq_elim                       true
% 3.74/1.00  --brand_transform                       false
% 3.74/1.00  --non_eq_to_eq                          false
% 3.74/1.00  --prep_def_merge                        true
% 3.74/1.00  --prep_def_merge_prop_impl              false
% 3.74/1.00  --prep_def_merge_mbd                    true
% 3.74/1.00  --prep_def_merge_tr_red                 false
% 3.74/1.00  --prep_def_merge_tr_cl                  false
% 3.74/1.00  --smt_preprocessing                     true
% 3.74/1.00  --smt_ac_axioms                         fast
% 3.74/1.00  --preprocessed_out                      false
% 3.74/1.00  --preprocessed_stats                    false
% 3.74/1.00  
% 3.74/1.00  ------ Abstraction refinement Options
% 3.74/1.00  
% 3.74/1.00  --abstr_ref                             []
% 3.74/1.00  --abstr_ref_prep                        false
% 3.74/1.00  --abstr_ref_until_sat                   false
% 3.74/1.00  --abstr_ref_sig_restrict                funpre
% 3.74/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.74/1.00  --abstr_ref_under                       []
% 3.74/1.00  
% 3.74/1.00  ------ SAT Options
% 3.74/1.00  
% 3.74/1.00  --sat_mode                              false
% 3.74/1.00  --sat_fm_restart_options                ""
% 3.74/1.00  --sat_gr_def                            false
% 3.74/1.00  --sat_epr_types                         true
% 3.74/1.00  --sat_non_cyclic_types                  false
% 3.74/1.00  --sat_finite_models                     false
% 3.74/1.00  --sat_fm_lemmas                         false
% 3.74/1.00  --sat_fm_prep                           false
% 3.74/1.00  --sat_fm_uc_incr                        true
% 3.74/1.00  --sat_out_model                         small
% 3.74/1.00  --sat_out_clauses                       false
% 3.74/1.00  
% 3.74/1.00  ------ QBF Options
% 3.74/1.00  
% 3.74/1.00  --qbf_mode                              false
% 3.74/1.00  --qbf_elim_univ                         false
% 3.74/1.00  --qbf_dom_inst                          none
% 3.74/1.00  --qbf_dom_pre_inst                      false
% 3.74/1.00  --qbf_sk_in                             false
% 3.74/1.00  --qbf_pred_elim                         true
% 3.74/1.00  --qbf_split                             512
% 3.74/1.00  
% 3.74/1.00  ------ BMC1 Options
% 3.74/1.00  
% 3.74/1.00  --bmc1_incremental                      false
% 3.74/1.00  --bmc1_axioms                           reachable_all
% 3.74/1.00  --bmc1_min_bound                        0
% 3.74/1.00  --bmc1_max_bound                        -1
% 3.74/1.00  --bmc1_max_bound_default                -1
% 3.74/1.00  --bmc1_symbol_reachability              true
% 3.74/1.00  --bmc1_property_lemmas                  false
% 3.74/1.00  --bmc1_k_induction                      false
% 3.74/1.00  --bmc1_non_equiv_states                 false
% 3.74/1.00  --bmc1_deadlock                         false
% 3.74/1.00  --bmc1_ucm                              false
% 3.74/1.00  --bmc1_add_unsat_core                   none
% 3.74/1.00  --bmc1_unsat_core_children              false
% 3.74/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.74/1.00  --bmc1_out_stat                         full
% 3.74/1.00  --bmc1_ground_init                      false
% 3.74/1.00  --bmc1_pre_inst_next_state              false
% 3.74/1.00  --bmc1_pre_inst_state                   false
% 3.74/1.00  --bmc1_pre_inst_reach_state             false
% 3.74/1.00  --bmc1_out_unsat_core                   false
% 3.74/1.00  --bmc1_aig_witness_out                  false
% 3.74/1.00  --bmc1_verbose                          false
% 3.74/1.00  --bmc1_dump_clauses_tptp                false
% 3.74/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.74/1.00  --bmc1_dump_file                        -
% 3.74/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.74/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.74/1.00  --bmc1_ucm_extend_mode                  1
% 3.74/1.00  --bmc1_ucm_init_mode                    2
% 3.74/1.00  --bmc1_ucm_cone_mode                    none
% 3.74/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.74/1.00  --bmc1_ucm_relax_model                  4
% 3.74/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.74/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.74/1.00  --bmc1_ucm_layered_model                none
% 3.74/1.00  --bmc1_ucm_max_lemma_size               10
% 3.74/1.00  
% 3.74/1.00  ------ AIG Options
% 3.74/1.00  
% 3.74/1.00  --aig_mode                              false
% 3.74/1.00  
% 3.74/1.00  ------ Instantiation Options
% 3.74/1.00  
% 3.74/1.00  --instantiation_flag                    true
% 3.74/1.00  --inst_sos_flag                         true
% 3.74/1.00  --inst_sos_phase                        true
% 3.74/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.74/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.74/1.00  --inst_lit_sel_side                     num_symb
% 3.74/1.00  --inst_solver_per_active                1400
% 3.74/1.00  --inst_solver_calls_frac                1.
% 3.74/1.00  --inst_passive_queue_type               priority_queues
% 3.74/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.74/1.00  --inst_passive_queues_freq              [25;2]
% 3.74/1.00  --inst_dismatching                      true
% 3.74/1.00  --inst_eager_unprocessed_to_passive     true
% 3.74/1.00  --inst_prop_sim_given                   true
% 3.74/1.00  --inst_prop_sim_new                     false
% 3.74/1.00  --inst_subs_new                         false
% 3.74/1.00  --inst_eq_res_simp                      false
% 3.74/1.00  --inst_subs_given                       false
% 3.74/1.00  --inst_orphan_elimination               true
% 3.74/1.00  --inst_learning_loop_flag               true
% 3.74/1.00  --inst_learning_start                   3000
% 3.74/1.00  --inst_learning_factor                  2
% 3.74/1.00  --inst_start_prop_sim_after_learn       3
% 3.74/1.00  --inst_sel_renew                        solver
% 3.74/1.00  --inst_lit_activity_flag                true
% 3.74/1.00  --inst_restr_to_given                   false
% 3.74/1.00  --inst_activity_threshold               500
% 3.74/1.00  --inst_out_proof                        true
% 3.74/1.00  
% 3.74/1.00  ------ Resolution Options
% 3.74/1.00  
% 3.74/1.00  --resolution_flag                       true
% 3.74/1.00  --res_lit_sel                           adaptive
% 3.74/1.00  --res_lit_sel_side                      none
% 3.74/1.00  --res_ordering                          kbo
% 3.74/1.00  --res_to_prop_solver                    active
% 3.74/1.00  --res_prop_simpl_new                    false
% 3.74/1.00  --res_prop_simpl_given                  true
% 3.74/1.00  --res_passive_queue_type                priority_queues
% 3.74/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.74/1.00  --res_passive_queues_freq               [15;5]
% 3.74/1.00  --res_forward_subs                      full
% 3.74/1.00  --res_backward_subs                     full
% 3.74/1.00  --res_forward_subs_resolution           true
% 3.74/1.00  --res_backward_subs_resolution          true
% 3.74/1.00  --res_orphan_elimination                true
% 3.74/1.00  --res_time_limit                        2.
% 3.74/1.00  --res_out_proof                         true
% 3.74/1.00  
% 3.74/1.00  ------ Superposition Options
% 3.74/1.00  
% 3.74/1.00  --superposition_flag                    true
% 3.74/1.00  --sup_passive_queue_type                priority_queues
% 3.74/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.74/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.74/1.00  --demod_completeness_check              fast
% 3.74/1.00  --demod_use_ground                      true
% 3.74/1.00  --sup_to_prop_solver                    passive
% 3.74/1.00  --sup_prop_simpl_new                    true
% 3.74/1.00  --sup_prop_simpl_given                  true
% 3.74/1.00  --sup_fun_splitting                     true
% 3.74/1.00  --sup_smt_interval                      50000
% 3.74/1.00  
% 3.74/1.00  ------ Superposition Simplification Setup
% 3.74/1.00  
% 3.74/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.74/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.74/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.74/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.74/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.74/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.74/1.00  --sup_immed_triv                        [TrivRules]
% 3.74/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.00  --sup_immed_bw_main                     []
% 3.74/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.74/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.74/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.00  --sup_input_bw                          []
% 3.74/1.00  
% 3.74/1.00  ------ Combination Options
% 3.74/1.00  
% 3.74/1.00  --comb_res_mult                         3
% 3.74/1.00  --comb_sup_mult                         2
% 3.74/1.00  --comb_inst_mult                        10
% 3.74/1.00  
% 3.74/1.00  ------ Debug Options
% 3.74/1.00  
% 3.74/1.00  --dbg_backtrace                         false
% 3.74/1.00  --dbg_dump_prop_clauses                 false
% 3.74/1.00  --dbg_dump_prop_clauses_file            -
% 3.74/1.00  --dbg_out_stat                          false
% 3.74/1.00  ------ Parsing...
% 3.74/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.74/1.00  
% 3.74/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.74/1.00  
% 3.74/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.74/1.00  
% 3.74/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/1.00  ------ Proving...
% 3.74/1.00  ------ Problem Properties 
% 3.74/1.00  
% 3.74/1.00  
% 3.74/1.00  clauses                                 29
% 3.74/1.00  conjectures                             18
% 3.74/1.00  EPR                                     18
% 3.74/1.00  Horn                                    23
% 3.74/1.00  unary                                   18
% 3.74/1.00  binary                                  0
% 3.74/1.00  lits                                    121
% 3.74/1.00  lits eq                                 3
% 3.74/1.00  fd_pure                                 0
% 3.74/1.00  fd_pseudo                               0
% 3.74/1.00  fd_cond                                 0
% 3.74/1.00  fd_pseudo_cond                          1
% 3.74/1.00  AC symbols                              0
% 3.74/1.00  
% 3.74/1.00  ------ Schedule dynamic 5 is on 
% 3.74/1.00  
% 3.74/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.74/1.00  
% 3.74/1.00  
% 3.74/1.00  ------ 
% 3.74/1.00  Current options:
% 3.74/1.00  ------ 
% 3.74/1.00  
% 3.74/1.00  ------ Input Options
% 3.74/1.00  
% 3.74/1.00  --out_options                           all
% 3.74/1.00  --tptp_safe_out                         true
% 3.74/1.00  --problem_path                          ""
% 3.74/1.00  --include_path                          ""
% 3.74/1.00  --clausifier                            res/vclausify_rel
% 3.74/1.00  --clausifier_options                    ""
% 3.74/1.00  --stdin                                 false
% 3.74/1.00  --stats_out                             all
% 3.74/1.00  
% 3.74/1.00  ------ General Options
% 3.74/1.00  
% 3.74/1.00  --fof                                   false
% 3.74/1.00  --time_out_real                         305.
% 3.74/1.00  --time_out_virtual                      -1.
% 3.74/1.00  --symbol_type_check                     false
% 3.74/1.00  --clausify_out                          false
% 3.74/1.00  --sig_cnt_out                           false
% 3.74/1.00  --trig_cnt_out                          false
% 3.74/1.00  --trig_cnt_out_tolerance                1.
% 3.74/1.00  --trig_cnt_out_sk_spl                   false
% 3.74/1.00  --abstr_cl_out                          false
% 3.74/1.00  
% 3.74/1.00  ------ Global Options
% 3.74/1.00  
% 3.74/1.00  --schedule                              default
% 3.74/1.00  --add_important_lit                     false
% 3.74/1.00  --prop_solver_per_cl                    1000
% 3.74/1.00  --min_unsat_core                        false
% 3.74/1.00  --soft_assumptions                      false
% 3.74/1.00  --soft_lemma_size                       3
% 3.74/1.00  --prop_impl_unit_size                   0
% 3.74/1.00  --prop_impl_unit                        []
% 3.74/1.00  --share_sel_clauses                     true
% 3.74/1.00  --reset_solvers                         false
% 3.74/1.00  --bc_imp_inh                            [conj_cone]
% 3.74/1.00  --conj_cone_tolerance                   3.
% 3.74/1.00  --extra_neg_conj                        none
% 3.74/1.00  --large_theory_mode                     true
% 3.74/1.00  --prolific_symb_bound                   200
% 3.74/1.00  --lt_threshold                          2000
% 3.74/1.00  --clause_weak_htbl                      true
% 3.74/1.00  --gc_record_bc_elim                     false
% 3.74/1.00  
% 3.74/1.00  ------ Preprocessing Options
% 3.74/1.00  
% 3.74/1.00  --preprocessing_flag                    true
% 3.74/1.00  --time_out_prep_mult                    0.1
% 3.74/1.00  --splitting_mode                        input
% 3.74/1.00  --splitting_grd                         true
% 3.74/1.00  --splitting_cvd                         false
% 3.74/1.00  --splitting_cvd_svl                     false
% 3.74/1.00  --splitting_nvd                         32
% 3.74/1.00  --sub_typing                            true
% 3.74/1.00  --prep_gs_sim                           true
% 3.74/1.00  --prep_unflatten                        true
% 3.74/1.00  --prep_res_sim                          true
% 3.74/1.00  --prep_upred                            true
% 3.74/1.00  --prep_sem_filter                       exhaustive
% 3.74/1.00  --prep_sem_filter_out                   false
% 3.74/1.00  --pred_elim                             true
% 3.74/1.00  --res_sim_input                         true
% 3.74/1.00  --eq_ax_congr_red                       true
% 3.74/1.00  --pure_diseq_elim                       true
% 3.74/1.00  --brand_transform                       false
% 3.74/1.00  --non_eq_to_eq                          false
% 3.74/1.00  --prep_def_merge                        true
% 3.74/1.00  --prep_def_merge_prop_impl              false
% 3.74/1.00  --prep_def_merge_mbd                    true
% 3.74/1.00  --prep_def_merge_tr_red                 false
% 3.74/1.00  --prep_def_merge_tr_cl                  false
% 3.74/1.00  --smt_preprocessing                     true
% 3.74/1.00  --smt_ac_axioms                         fast
% 3.74/1.00  --preprocessed_out                      false
% 3.74/1.00  --preprocessed_stats                    false
% 3.74/1.00  
% 3.74/1.00  ------ Abstraction refinement Options
% 3.74/1.00  
% 3.74/1.00  --abstr_ref                             []
% 3.74/1.00  --abstr_ref_prep                        false
% 3.74/1.00  --abstr_ref_until_sat                   false
% 3.74/1.00  --abstr_ref_sig_restrict                funpre
% 3.74/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.74/1.00  --abstr_ref_under                       []
% 3.74/1.00  
% 3.74/1.00  ------ SAT Options
% 3.74/1.00  
% 3.74/1.00  --sat_mode                              false
% 3.74/1.00  --sat_fm_restart_options                ""
% 3.74/1.00  --sat_gr_def                            false
% 3.74/1.00  --sat_epr_types                         true
% 3.74/1.00  --sat_non_cyclic_types                  false
% 3.74/1.00  --sat_finite_models                     false
% 3.74/1.00  --sat_fm_lemmas                         false
% 3.74/1.00  --sat_fm_prep                           false
% 3.74/1.00  --sat_fm_uc_incr                        true
% 3.74/1.00  --sat_out_model                         small
% 3.74/1.00  --sat_out_clauses                       false
% 3.74/1.00  
% 3.74/1.00  ------ QBF Options
% 3.74/1.00  
% 3.74/1.00  --qbf_mode                              false
% 3.74/1.00  --qbf_elim_univ                         false
% 3.74/1.00  --qbf_dom_inst                          none
% 3.74/1.00  --qbf_dom_pre_inst                      false
% 3.74/1.00  --qbf_sk_in                             false
% 3.74/1.00  --qbf_pred_elim                         true
% 3.74/1.00  --qbf_split                             512
% 3.74/1.00  
% 3.74/1.00  ------ BMC1 Options
% 3.74/1.00  
% 3.74/1.00  --bmc1_incremental                      false
% 3.74/1.00  --bmc1_axioms                           reachable_all
% 3.74/1.00  --bmc1_min_bound                        0
% 3.74/1.00  --bmc1_max_bound                        -1
% 3.74/1.00  --bmc1_max_bound_default                -1
% 3.74/1.00  --bmc1_symbol_reachability              true
% 3.74/1.00  --bmc1_property_lemmas                  false
% 3.74/1.00  --bmc1_k_induction                      false
% 3.74/1.00  --bmc1_non_equiv_states                 false
% 3.74/1.00  --bmc1_deadlock                         false
% 3.74/1.00  --bmc1_ucm                              false
% 3.74/1.00  --bmc1_add_unsat_core                   none
% 3.74/1.00  --bmc1_unsat_core_children              false
% 3.74/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.74/1.00  --bmc1_out_stat                         full
% 3.74/1.00  --bmc1_ground_init                      false
% 3.74/1.00  --bmc1_pre_inst_next_state              false
% 3.74/1.00  --bmc1_pre_inst_state                   false
% 3.74/1.00  --bmc1_pre_inst_reach_state             false
% 3.74/1.00  --bmc1_out_unsat_core                   false
% 3.74/1.00  --bmc1_aig_witness_out                  false
% 3.74/1.00  --bmc1_verbose                          false
% 3.74/1.00  --bmc1_dump_clauses_tptp                false
% 3.74/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.74/1.00  --bmc1_dump_file                        -
% 3.74/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.74/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.74/1.00  --bmc1_ucm_extend_mode                  1
% 3.74/1.00  --bmc1_ucm_init_mode                    2
% 3.74/1.00  --bmc1_ucm_cone_mode                    none
% 3.74/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.74/1.00  --bmc1_ucm_relax_model                  4
% 3.74/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.74/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.74/1.00  --bmc1_ucm_layered_model                none
% 3.74/1.00  --bmc1_ucm_max_lemma_size               10
% 3.74/1.00  
% 3.74/1.00  ------ AIG Options
% 3.74/1.00  
% 3.74/1.00  --aig_mode                              false
% 3.74/1.00  
% 3.74/1.00  ------ Instantiation Options
% 3.74/1.00  
% 3.74/1.00  --instantiation_flag                    true
% 3.74/1.00  --inst_sos_flag                         true
% 3.74/1.00  --inst_sos_phase                        true
% 3.74/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.74/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.74/1.00  --inst_lit_sel_side                     none
% 3.74/1.00  --inst_solver_per_active                1400
% 3.74/1.00  --inst_solver_calls_frac                1.
% 3.74/1.00  --inst_passive_queue_type               priority_queues
% 3.74/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.74/1.00  --inst_passive_queues_freq              [25;2]
% 3.74/1.00  --inst_dismatching                      true
% 3.74/1.00  --inst_eager_unprocessed_to_passive     true
% 3.74/1.00  --inst_prop_sim_given                   true
% 3.74/1.00  --inst_prop_sim_new                     false
% 3.74/1.00  --inst_subs_new                         false
% 3.74/1.00  --inst_eq_res_simp                      false
% 3.74/1.00  --inst_subs_given                       false
% 3.74/1.00  --inst_orphan_elimination               true
% 3.74/1.00  --inst_learning_loop_flag               true
% 3.74/1.00  --inst_learning_start                   3000
% 3.74/1.00  --inst_learning_factor                  2
% 3.74/1.00  --inst_start_prop_sim_after_learn       3
% 3.74/1.00  --inst_sel_renew                        solver
% 3.74/1.00  --inst_lit_activity_flag                true
% 3.74/1.00  --inst_restr_to_given                   false
% 3.74/1.00  --inst_activity_threshold               500
% 3.74/1.00  --inst_out_proof                        true
% 3.74/1.00  
% 3.74/1.00  ------ Resolution Options
% 3.74/1.00  
% 3.74/1.00  --resolution_flag                       false
% 3.74/1.00  --res_lit_sel                           adaptive
% 3.74/1.00  --res_lit_sel_side                      none
% 3.74/1.00  --res_ordering                          kbo
% 3.74/1.00  --res_to_prop_solver                    active
% 3.74/1.00  --res_prop_simpl_new                    false
% 3.74/1.00  --res_prop_simpl_given                  true
% 3.74/1.00  --res_passive_queue_type                priority_queues
% 3.74/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.74/1.00  --res_passive_queues_freq               [15;5]
% 3.74/1.00  --res_forward_subs                      full
% 3.74/1.00  --res_backward_subs                     full
% 3.74/1.00  --res_forward_subs_resolution           true
% 3.74/1.00  --res_backward_subs_resolution          true
% 3.74/1.00  --res_orphan_elimination                true
% 3.74/1.00  --res_time_limit                        2.
% 3.74/1.00  --res_out_proof                         true
% 3.74/1.00  
% 3.74/1.00  ------ Superposition Options
% 3.74/1.00  
% 3.74/1.00  --superposition_flag                    true
% 3.74/1.00  --sup_passive_queue_type                priority_queues
% 3.74/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.74/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.74/1.00  --demod_completeness_check              fast
% 3.74/1.00  --demod_use_ground                      true
% 3.74/1.00  --sup_to_prop_solver                    passive
% 3.74/1.00  --sup_prop_simpl_new                    true
% 3.74/1.00  --sup_prop_simpl_given                  true
% 3.74/1.00  --sup_fun_splitting                     true
% 3.74/1.00  --sup_smt_interval                      50000
% 3.74/1.00  
% 3.74/1.00  ------ Superposition Simplification Setup
% 3.74/1.00  
% 3.74/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.74/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.74/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.74/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.74/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.74/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.74/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.74/1.00  --sup_immed_triv                        [TrivRules]
% 3.74/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.00  --sup_immed_bw_main                     []
% 3.74/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.74/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.74/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.74/1.00  --sup_input_bw                          []
% 3.74/1.00  
% 3.74/1.00  ------ Combination Options
% 3.74/1.00  
% 3.74/1.00  --comb_res_mult                         3
% 3.74/1.00  --comb_sup_mult                         2
% 3.74/1.00  --comb_inst_mult                        10
% 3.74/1.00  
% 3.74/1.00  ------ Debug Options
% 3.74/1.00  
% 3.74/1.00  --dbg_backtrace                         false
% 3.74/1.00  --dbg_dump_prop_clauses                 false
% 3.74/1.00  --dbg_dump_prop_clauses_file            -
% 3.74/1.00  --dbg_out_stat                          false
% 3.74/1.00  
% 3.74/1.00  
% 3.74/1.00  
% 3.74/1.00  
% 3.74/1.00  ------ Proving...
% 3.74/1.00  
% 3.74/1.00  
% 3.74/1.00  % SZS status Theorem for theBenchmark.p
% 3.74/1.00  
% 3.74/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.74/1.00  
% 3.74/1.00  fof(f9,conjecture,(
% 3.74/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 3.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f10,negated_conjecture,(
% 3.74/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)))))))))),
% 3.74/1.00    inference(negated_conjecture,[],[f9])).
% 3.74/1.00  
% 3.74/1.00  fof(f26,plain,(
% 3.74/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f10])).
% 3.74/1.00  
% 3.74/1.00  fof(f27,plain,(
% 3.74/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.74/1.00    inference(flattening,[],[f26])).
% 3.74/1.00  
% 3.74/1.00  fof(f34,plain,(
% 3.74/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,sK5)),k3_tmap_1(X0,X1,X2,X4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 3.74/1.00    introduced(choice_axiom,[])).
% 3.74/1.00  
% 3.74/1.00  fof(f33,plain,(
% 3.74/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => (? [X5] : (~r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,sK4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,sK4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(sK4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.74/1.00    introduced(choice_axiom,[])).
% 3.74/1.00  
% 3.74/1.00  fof(f32,plain,(
% 3.74/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,sK3,X4,k3_tmap_1(X0,X1,X2,sK3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,sK3) & m1_pre_topc(sK3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.74/1.00    introduced(choice_axiom,[])).
% 3.74/1.00  
% 3.74/1.00  fof(f31,plain,(
% 3.74/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,sK2,X3,X5)),k3_tmap_1(X0,X1,sK2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,sK2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.74/1.00    introduced(choice_axiom,[])).
% 3.74/1.00  
% 3.74/1.00  fof(f30,plain,(
% 3.74/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(sK1),k3_tmap_1(X0,sK1,X3,X4,k3_tmap_1(X0,sK1,X2,X3,X5)),k3_tmap_1(X0,sK1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.74/1.00    introduced(choice_axiom,[])).
% 3.74/1.00  
% 3.74/1.00  fof(f29,plain,(
% 3.74/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (~r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK0,X1,X3,X4,k3_tmap_1(sK0,X1,X2,X3,X5)),k3_tmap_1(sK0,X1,X2,X4,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_pre_topc(X4,X3) & m1_pre_topc(X3,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.74/1.00    introduced(choice_axiom,[])).
% 3.74/1.00  
% 3.74/1.00  fof(f35,plain,(
% 3.74/1.00    (((((~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK3) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.74/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f27,f34,f33,f32,f31,f30,f29])).
% 3.74/1.00  
% 3.74/1.00  fof(f60,plain,(
% 3.74/1.00    m1_pre_topc(sK4,sK3)),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f56,plain,(
% 3.74/1.00    m1_pre_topc(sK3,sK0)),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f63,plain,(
% 3.74/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f5,axiom,(
% 3.74/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f18,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f5])).
% 3.74/1.00  
% 3.74/1.00  fof(f19,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(flattening,[],[f18])).
% 3.74/1.00  
% 3.74/1.00  fof(f41,plain,(
% 3.74/1.00    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f19])).
% 3.74/1.00  
% 3.74/1.00  fof(f50,plain,(
% 3.74/1.00    ~v2_struct_0(sK1)),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f51,plain,(
% 3.74/1.00    v2_pre_topc(sK1)),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f52,plain,(
% 3.74/1.00    l1_pre_topc(sK1)),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f61,plain,(
% 3.74/1.00    v1_funct_1(sK5)),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f62,plain,(
% 3.74/1.00    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1))),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f59,plain,(
% 3.74/1.00    m1_pre_topc(sK3,sK2)),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f4,axiom,(
% 3.74/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f16,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f4])).
% 3.74/1.00  
% 3.74/1.00  fof(f17,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(flattening,[],[f16])).
% 3.74/1.00  
% 3.74/1.00  fof(f40,plain,(
% 3.74/1.00    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f17])).
% 3.74/1.00  
% 3.74/1.00  fof(f48,plain,(
% 3.74/1.00    v2_pre_topc(sK0)),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f49,plain,(
% 3.74/1.00    l1_pre_topc(sK0)),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f53,plain,(
% 3.74/1.00    ~v2_struct_0(sK2)),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f54,plain,(
% 3.74/1.00    m1_pre_topc(sK2,sK0)),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f3,axiom,(
% 3.74/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f15,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.74/1.00    inference(ennf_transformation,[],[f3])).
% 3.74/1.00  
% 3.74/1.00  fof(f39,plain,(
% 3.74/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f15])).
% 3.74/1.00  
% 3.74/1.00  fof(f2,axiom,(
% 3.74/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f13,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f2])).
% 3.74/1.00  
% 3.74/1.00  fof(f14,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.74/1.00    inference(flattening,[],[f13])).
% 3.74/1.00  
% 3.74/1.00  fof(f38,plain,(
% 3.74/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f14])).
% 3.74/1.00  
% 3.74/1.00  fof(f47,plain,(
% 3.74/1.00    ~v2_struct_0(sK0)),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f6,axiom,(
% 3.74/1.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 3.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f20,plain,(
% 3.74/1.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f6])).
% 3.74/1.00  
% 3.74/1.00  fof(f21,plain,(
% 3.74/1.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(flattening,[],[f20])).
% 3.74/1.00  
% 3.74/1.00  fof(f44,plain,(
% 3.74/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f21])).
% 3.74/1.00  
% 3.74/1.00  fof(f55,plain,(
% 3.74/1.00    ~v2_struct_0(sK3)),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f43,plain,(
% 3.74/1.00    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f21])).
% 3.74/1.00  
% 3.74/1.00  fof(f42,plain,(
% 3.74/1.00    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f21])).
% 3.74/1.00  
% 3.74/1.00  fof(f58,plain,(
% 3.74/1.00    m1_pre_topc(sK4,sK0)),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f8,axiom,(
% 3.74/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 3.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f24,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f8])).
% 3.74/1.00  
% 3.74/1.00  fof(f25,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.74/1.00    inference(flattening,[],[f24])).
% 3.74/1.00  
% 3.74/1.00  fof(f46,plain,(
% 3.74/1.00    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f25])).
% 3.74/1.00  
% 3.74/1.00  fof(f1,axiom,(
% 3.74/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f11,plain,(
% 3.74/1.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.74/1.00    inference(ennf_transformation,[],[f1])).
% 3.74/1.00  
% 3.74/1.00  fof(f12,plain,(
% 3.74/1.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.74/1.00    inference(flattening,[],[f11])).
% 3.74/1.00  
% 3.74/1.00  fof(f28,plain,(
% 3.74/1.00    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.74/1.00    inference(nnf_transformation,[],[f12])).
% 3.74/1.00  
% 3.74/1.00  fof(f37,plain,(
% 3.74/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f28])).
% 3.74/1.00  
% 3.74/1.00  fof(f65,plain,(
% 3.74/1.00    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.74/1.00    inference(equality_resolution,[],[f37])).
% 3.74/1.00  
% 3.74/1.00  fof(f7,axiom,(
% 3.74/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X5)) => ((m1_pre_topc(X3,X2) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2))) => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 3.74/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/1.00  
% 3.74/1.00  fof(f22,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | (~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.74/1.00    inference(ennf_transformation,[],[f7])).
% 3.74/1.00  
% 3.74/1.00  fof(f23,plain,(
% 3.74/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.74/1.00    inference(flattening,[],[f22])).
% 3.74/1.00  
% 3.74/1.00  fof(f45,plain,(
% 3.74/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,X3,X5),k2_tmap_1(X0,X1,X4,X3)) | ~m1_pre_topc(X3,X2) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X5,k2_tmap_1(X0,X1,X4,X2)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.74/1.00    inference(cnf_transformation,[],[f23])).
% 3.74/1.00  
% 3.74/1.00  fof(f64,plain,(
% 3.74/1.00    ~r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5))),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  fof(f57,plain,(
% 3.74/1.00    ~v2_struct_0(sK4)),
% 3.74/1.00    inference(cnf_transformation,[],[f35])).
% 3.74/1.00  
% 3.74/1.00  cnf(c_15,negated_conjecture,
% 3.74/1.00      ( m1_pre_topc(sK4,sK3) ),
% 3.74/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_306,negated_conjecture,
% 3.74/1.00      ( m1_pre_topc(sK4,sK3) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_809,plain,
% 3.74/1.00      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_19,negated_conjecture,
% 3.74/1.00      ( m1_pre_topc(sK3,sK0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_302,negated_conjecture,
% 3.74/1.00      ( m1_pre_topc(sK3,sK0) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_813,plain,
% 3.74/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_12,negated_conjecture,
% 3.74/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 3.74/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_309,negated_conjecture,
% 3.74/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_806,plain,
% 3.74/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_5,plain,
% 3.74/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.74/1.00      | ~ m1_pre_topc(X3,X4)
% 3.74/1.00      | ~ m1_pre_topc(X3,X1)
% 3.74/1.00      | ~ m1_pre_topc(X1,X4)
% 3.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.74/1.00      | v2_struct_0(X4)
% 3.74/1.00      | v2_struct_0(X2)
% 3.74/1.00      | ~ l1_pre_topc(X4)
% 3.74/1.00      | ~ l1_pre_topc(X2)
% 3.74/1.00      | ~ v2_pre_topc(X4)
% 3.74/1.00      | ~ v2_pre_topc(X2)
% 3.74/1.00      | ~ v1_funct_1(X0)
% 3.74/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_316,plain,
% 3.74/1.00      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.74/1.00      | ~ m1_pre_topc(X2_48,X0_48)
% 3.74/1.00      | ~ m1_pre_topc(X0_48,X3_48)
% 3.74/1.00      | ~ m1_pre_topc(X2_48,X3_48)
% 3.74/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.74/1.00      | v2_struct_0(X3_48)
% 3.74/1.00      | v2_struct_0(X1_48)
% 3.74/1.00      | ~ l1_pre_topc(X1_48)
% 3.74/1.00      | ~ l1_pre_topc(X3_48)
% 3.74/1.00      | ~ v2_pre_topc(X1_48)
% 3.74/1.00      | ~ v2_pre_topc(X3_48)
% 3.74/1.00      | ~ v1_funct_1(X0_49)
% 3.74/1.00      | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_799,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k3_tmap_1(X3_48,X1_48,X0_48,X2_48,X0_49)
% 3.74/1.00      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,X3_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X2_48,X3_48) != iProver_top
% 3.74/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.74/1.00      | v2_struct_0(X3_48) = iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(X3_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X3_48) != iProver_top
% 3.74/1.00      | v1_funct_1(X0_49) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1876,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
% 3.74/1.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK2) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK2,X1_48) != iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | v2_struct_0(sK1) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_806,c_799]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_25,negated_conjecture,
% 3.74/1.00      ( ~ v2_struct_0(sK1) ),
% 3.74/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_32,plain,
% 3.74/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_24,negated_conjecture,
% 3.74/1.00      ( v2_pre_topc(sK1) ),
% 3.74/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_33,plain,
% 3.74/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_23,negated_conjecture,
% 3.74/1.00      ( l1_pre_topc(sK1) ),
% 3.74/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_34,plain,
% 3.74/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_14,negated_conjecture,
% 3.74/1.00      ( v1_funct_1(sK5) ),
% 3.74/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_43,plain,
% 3.74/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_13,negated_conjecture,
% 3.74/1.00      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 3.74/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_44,plain,
% 3.74/1.00      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2470,plain,
% 3.74/1.00      ( l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
% 3.74/1.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK2) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK2,X1_48) != iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_1876,c_32,c_33,c_34,c_43,c_44]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2471,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)
% 3.74/1.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK2) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK2,X1_48) != iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_2470]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2479,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK2,sK3,sK5)
% 3.74/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.74/1.00      | v2_struct_0(sK0) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_813,c_2471]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_16,negated_conjecture,
% 3.74/1.00      ( m1_pre_topc(sK3,sK2) ),
% 3.74/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_305,negated_conjecture,
% 3.74/1.00      ( m1_pre_topc(sK3,sK2) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_810,plain,
% 3.74/1.00      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_4,plain,
% 3.74/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.74/1.00      | ~ m1_pre_topc(X3,X1)
% 3.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.74/1.00      | v2_struct_0(X1)
% 3.74/1.00      | v2_struct_0(X2)
% 3.74/1.00      | ~ l1_pre_topc(X1)
% 3.74/1.00      | ~ l1_pre_topc(X2)
% 3.74/1.00      | ~ v2_pre_topc(X1)
% 3.74/1.00      | ~ v2_pre_topc(X2)
% 3.74/1.00      | ~ v1_funct_1(X0)
% 3.74/1.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.74/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_317,plain,
% 3.74/1.00      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.74/1.00      | ~ m1_pre_topc(X2_48,X0_48)
% 3.74/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.74/1.00      | v2_struct_0(X1_48)
% 3.74/1.00      | v2_struct_0(X0_48)
% 3.74/1.00      | ~ l1_pre_topc(X1_48)
% 3.74/1.00      | ~ l1_pre_topc(X0_48)
% 3.74/1.00      | ~ v2_pre_topc(X1_48)
% 3.74/1.00      | ~ v2_pre_topc(X0_48)
% 3.74/1.00      | ~ v1_funct_1(X0_49)
% 3.74/1.00      | k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_798,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,u1_struct_0(X2_48)) = k2_tmap_1(X0_48,X1_48,X0_49,X2_48)
% 3.74/1.00      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 3.74/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | v2_struct_0(X0_48) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(X0_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X0_48) != iProver_top
% 3.74/1.00      | v1_funct_1(X0_49) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1709,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48)
% 3.74/1.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK2) != iProver_top
% 3.74/1.00      | v2_struct_0(sK2) = iProver_top
% 3.74/1.00      | v2_struct_0(sK1) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_806,c_798]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_27,negated_conjecture,
% 3.74/1.00      ( v2_pre_topc(sK0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_30,plain,
% 3.74/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_26,negated_conjecture,
% 3.74/1.00      ( l1_pre_topc(sK0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_31,plain,
% 3.74/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_22,negated_conjecture,
% 3.74/1.00      ( ~ v2_struct_0(sK2) ),
% 3.74/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_35,plain,
% 3.74/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_21,negated_conjecture,
% 3.74/1.00      ( m1_pre_topc(sK2,sK0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_36,plain,
% 3.74/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3,plain,
% 3.74/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_318,plain,
% 3.74/1.00      ( ~ m1_pre_topc(X0_48,X1_48)
% 3.74/1.00      | ~ l1_pre_topc(X1_48)
% 3.74/1.00      | l1_pre_topc(X0_48) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1108,plain,
% 3.74/1.00      ( ~ m1_pre_topc(sK2,X0_48)
% 3.74/1.00      | ~ l1_pre_topc(X0_48)
% 3.74/1.00      | l1_pre_topc(sK2) ),
% 3.74/1.00      inference(instantiation,[status(thm)],[c_318]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1109,plain,
% 3.74/1.00      ( m1_pre_topc(sK2,X0_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(X0_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK2) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1108]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1111,plain,
% 3.74/1.00      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK2) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.74/1.00      inference(instantiation,[status(thm)],[c_1109]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2,plain,
% 3.74/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.74/1.00      | ~ l1_pre_topc(X1)
% 3.74/1.00      | ~ v2_pre_topc(X1)
% 3.74/1.00      | v2_pre_topc(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_319,plain,
% 3.74/1.00      ( ~ m1_pre_topc(X0_48,X1_48)
% 3.74/1.00      | ~ l1_pre_topc(X1_48)
% 3.74/1.00      | ~ v2_pre_topc(X1_48)
% 3.74/1.00      | v2_pre_topc(X0_48) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1298,plain,
% 3.74/1.00      ( ~ m1_pre_topc(sK2,X0_48)
% 3.74/1.00      | ~ l1_pre_topc(X0_48)
% 3.74/1.00      | ~ v2_pre_topc(X0_48)
% 3.74/1.00      | v2_pre_topc(sK2) ),
% 3.74/1.00      inference(instantiation,[status(thm)],[c_319]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1299,plain,
% 3.74/1.00      ( m1_pre_topc(sK2,X0_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(X0_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X0_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK2) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1298]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1301,plain,
% 3.74/1.00      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK2) = iProver_top
% 3.74/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 3.74/1.00      inference(instantiation,[status(thm)],[c_1299]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2288,plain,
% 3.74/1.00      ( m1_pre_topc(X0_48,sK2) != iProver_top
% 3.74/1.00      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_1709,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_43,c_44,
% 3.74/1.00                 c_1111,c_1301]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2289,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(X0_48)) = k2_tmap_1(sK2,sK1,sK5,X0_48)
% 3.74/1.00      | m1_pre_topc(X0_48,sK2) != iProver_top ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_2288]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2294,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_810,c_2289]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2483,plain,
% 3.74/1.00      ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3)
% 3.74/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.74/1.00      | v2_struct_0(sK0) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 3.74/1.00      inference(light_normalisation,[status(thm)],[c_2479,c_2294]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_28,negated_conjecture,
% 3.74/1.00      ( ~ v2_struct_0(sK0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_29,plain,
% 3.74/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_41,plain,
% 3.74/1.00      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2548,plain,
% 3.74/1.00      ( k3_tmap_1(sK0,sK1,sK2,sK3,sK5) = k2_tmap_1(sK2,sK1,sK5,sK3) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_2483,c_29,c_30,c_31,c_36,c_41]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_6,plain,
% 3.74/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.74/1.00      | ~ m1_pre_topc(X3,X4)
% 3.74/1.00      | ~ m1_pre_topc(X1,X4)
% 3.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.74/1.00      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 3.74/1.00      | v2_struct_0(X4)
% 3.74/1.00      | v2_struct_0(X2)
% 3.74/1.00      | ~ l1_pre_topc(X4)
% 3.74/1.00      | ~ l1_pre_topc(X2)
% 3.74/1.00      | ~ v2_pre_topc(X4)
% 3.74/1.00      | ~ v2_pre_topc(X2)
% 3.74/1.00      | ~ v1_funct_1(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_315,plain,
% 3.74/1.00      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.74/1.00      | ~ m1_pre_topc(X0_48,X2_48)
% 3.74/1.00      | ~ m1_pre_topc(X3_48,X2_48)
% 3.74/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.74/1.00      | m1_subset_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48))))
% 3.74/1.00      | v2_struct_0(X2_48)
% 3.74/1.00      | v2_struct_0(X1_48)
% 3.74/1.00      | ~ l1_pre_topc(X1_48)
% 3.74/1.00      | ~ l1_pre_topc(X2_48)
% 3.74/1.00      | ~ v2_pre_topc(X1_48)
% 3.74/1.00      | ~ v2_pre_topc(X2_48)
% 3.74/1.00      | ~ v1_funct_1(X0_49) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_800,plain,
% 3.74/1.00      ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 3.74/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.74/1.00      | m1_subset_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) = iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | v2_struct_0(X2_48) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(X2_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X2_48) != iProver_top
% 3.74/1.00      | v1_funct_1(X0_49) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1957,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k2_tmap_1(X0_48,X1_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),X4_48)
% 3.74/1.00      | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
% 3.74/1.00      | v1_funct_2(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X4_48,X0_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 3.74/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
% 3.74/1.00      | v2_struct_0(X0_48) = iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | v2_struct_0(X2_48) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(X0_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(X2_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X0_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X2_48) != iProver_top
% 3.74/1.00      | v1_funct_1(X0_49) != iProver_top
% 3.74/1.00      | v1_funct_1(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49)) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_800,c_798]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3980,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k3_tmap_1(sK0,sK1,sK2,sK3,sK5),X0_48)
% 3.74/1.00      | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.74/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.74/1.00      | v2_struct_0(sK3) = iProver_top
% 3.74/1.00      | v2_struct_0(sK0) = iProver_top
% 3.74/1.00      | v2_struct_0(sK1) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) != iProver_top
% 3.74/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_2548,c_1957]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3993,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_48)
% 3.74/1.00      | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.74/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.74/1.00      | v2_struct_0(sK3) = iProver_top
% 3.74/1.00      | v2_struct_0(sK0) = iProver_top
% 3.74/1.00      | v2_struct_0(sK1) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top
% 3.74/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.74/1.00      inference(light_normalisation,[status(thm)],[c_3980,c_2548]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_20,negated_conjecture,
% 3.74/1.00      ( ~ v2_struct_0(sK3) ),
% 3.74/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_37,plain,
% 3.74/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_38,plain,
% 3.74/1.00      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_45,plain,
% 3.74/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1114,plain,
% 3.74/1.00      ( ~ m1_pre_topc(sK3,X0_48)
% 3.74/1.00      | ~ l1_pre_topc(X0_48)
% 3.74/1.00      | l1_pre_topc(sK3) ),
% 3.74/1.00      inference(instantiation,[status(thm)],[c_318]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1115,plain,
% 3.74/1.00      ( m1_pre_topc(sK3,X0_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(X0_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1114]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1117,plain,
% 3.74/1.00      ( m1_pre_topc(sK3,sK0) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK3) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.74/1.00      inference(instantiation,[status(thm)],[c_1115]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1293,plain,
% 3.74/1.00      ( ~ m1_pre_topc(sK3,X0_48)
% 3.74/1.00      | ~ l1_pre_topc(X0_48)
% 3.74/1.00      | ~ v2_pre_topc(X0_48)
% 3.74/1.00      | v2_pre_topc(sK3) ),
% 3.74/1.00      inference(instantiation,[status(thm)],[c_319]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1294,plain,
% 3.74/1.00      ( m1_pre_topc(sK3,X0_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(X0_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X0_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK3) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1293]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1296,plain,
% 3.74/1.00      ( m1_pre_topc(sK3,sK0) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK3) = iProver_top
% 3.74/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 3.74/1.00      inference(instantiation,[status(thm)],[c_1294]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_7,plain,
% 3.74/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.74/1.00      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 3.74/1.00      | ~ m1_pre_topc(X4,X3)
% 3.74/1.00      | ~ m1_pre_topc(X1,X3)
% 3.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.74/1.00      | v2_struct_0(X3)
% 3.74/1.00      | v2_struct_0(X2)
% 3.74/1.00      | ~ l1_pre_topc(X3)
% 3.74/1.00      | ~ l1_pre_topc(X2)
% 3.74/1.00      | ~ v2_pre_topc(X3)
% 3.74/1.00      | ~ v2_pre_topc(X2)
% 3.74/1.00      | ~ v1_funct_1(X0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_314,plain,
% 3.74/1.00      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.74/1.00      | v1_funct_2(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),u1_struct_0(X3_48),u1_struct_0(X1_48))
% 3.74/1.00      | ~ m1_pre_topc(X3_48,X2_48)
% 3.74/1.00      | ~ m1_pre_topc(X0_48,X2_48)
% 3.74/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.74/1.00      | v2_struct_0(X1_48)
% 3.74/1.00      | v2_struct_0(X2_48)
% 3.74/1.00      | ~ l1_pre_topc(X1_48)
% 3.74/1.00      | ~ l1_pre_topc(X2_48)
% 3.74/1.00      | ~ v2_pre_topc(X1_48)
% 3.74/1.00      | ~ v2_pre_topc(X2_48)
% 3.74/1.00      | ~ v1_funct_1(X0_49) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_801,plain,
% 3.74/1.00      ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.74/1.00      | v1_funct_2(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),u1_struct_0(X3_48),u1_struct_0(X1_48)) = iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 3.74/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | v2_struct_0(X2_48) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(X2_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X2_48) != iProver_top
% 3.74/1.00      | v1_funct_1(X0_49) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2553,plain,
% 3.74/1.00      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 3.74/1.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.74/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.74/1.00      | v2_struct_0(sK0) = iProver_top
% 3.74/1.00      | v2_struct_0(sK1) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_2548,c_801]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_8,plain,
% 3.74/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.74/1.00      | ~ m1_pre_topc(X3,X4)
% 3.74/1.00      | ~ m1_pre_topc(X1,X4)
% 3.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.74/1.00      | v2_struct_0(X4)
% 3.74/1.00      | v2_struct_0(X2)
% 3.74/1.00      | ~ l1_pre_topc(X4)
% 3.74/1.00      | ~ l1_pre_topc(X2)
% 3.74/1.00      | ~ v2_pre_topc(X4)
% 3.74/1.00      | ~ v2_pre_topc(X2)
% 3.74/1.00      | ~ v1_funct_1(X0)
% 3.74/1.00      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 3.74/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_313,plain,
% 3.74/1.00      ( ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.74/1.00      | ~ m1_pre_topc(X0_48,X2_48)
% 3.74/1.00      | ~ m1_pre_topc(X3_48,X2_48)
% 3.74/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.74/1.00      | v2_struct_0(X2_48)
% 3.74/1.00      | v2_struct_0(X1_48)
% 3.74/1.00      | ~ l1_pre_topc(X1_48)
% 3.74/1.00      | ~ l1_pre_topc(X2_48)
% 3.74/1.00      | ~ v2_pre_topc(X1_48)
% 3.74/1.00      | ~ v2_pre_topc(X2_48)
% 3.74/1.00      | ~ v1_funct_1(X0_49)
% 3.74/1.00      | v1_funct_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49)) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_802,plain,
% 3.74/1.00      ( v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 3.74/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | v2_struct_0(X2_48) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(X2_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X2_48) != iProver_top
% 3.74/1.00      | v1_funct_1(X0_49) != iProver_top
% 3.74/1.00      | v1_funct_1(k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49)) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1714,plain,
% 3.74/1.00      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK2,X1_48) != iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | v2_struct_0(sK1) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v1_funct_1(k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)) = iProver_top
% 3.74/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_806,c_802]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2463,plain,
% 3.74/1.00      ( v1_funct_1(k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK2,X1_48) != iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_1714,c_32,c_33,c_34,c_43,c_44]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2464,plain,
% 3.74/1.00      ( m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK2,X1_48) != iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v1_funct_1(k3_tmap_1(X1_48,sK1,sK2,X0_48,sK5)) = iProver_top ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_2463]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2554,plain,
% 3.74/1.00      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.74/1.00      | v2_struct_0(sK0) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.74/1.00      | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) = iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_2548,c_2464]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2552,plain,
% 3.74/1.00      ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.74/1.00      | m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 3.74/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.74/1.00      | v2_struct_0(sK0) = iProver_top
% 3.74/1.00      | v2_struct_0(sK1) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_2548,c_800]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3048,plain,
% 3.74/1.00      ( m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_2552,c_29,c_30,c_31,c_32,c_33,c_34,c_36,c_38,c_43,
% 3.74/1.00                 c_44,c_45]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3054,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_48)
% 3.74/1.00      | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.74/1.00      | v2_struct_0(sK3) = iProver_top
% 3.74/1.00      | v2_struct_0(sK1) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK3) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK3) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_3048,c_798]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_5210,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),X0_48)
% 3.74/1.00      | m1_pre_topc(X0_48,sK3) != iProver_top ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_3993,c_29,c_30,c_31,c_32,c_33,c_34,c_36,c_37,c_38,
% 3.74/1.00                 c_43,c_44,c_45,c_1117,c_1296,c_2553,c_2554,c_3054]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_5216,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_809,c_5210]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_17,negated_conjecture,
% 3.74/1.00      ( m1_pre_topc(sK4,sK0) ),
% 3.74/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_304,negated_conjecture,
% 3.74/1.00      ( m1_pre_topc(sK4,sK0) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_811,plain,
% 3.74/1.00      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1955,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(X0_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X4_48)) = k3_tmap_1(X5_48,X1_48,X0_48,X4_48,k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49))
% 3.74/1.00      | v1_funct_2(X0_49,u1_struct_0(X3_48),u1_struct_0(X1_48)) != iProver_top
% 3.74/1.00      | v1_funct_2(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49),u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X4_48,X0_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,X5_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X4_48,X5_48) != iProver_top
% 3.74/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_48),u1_struct_0(X1_48)))) != iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | v2_struct_0(X5_48) = iProver_top
% 3.74/1.00      | v2_struct_0(X2_48) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(X2_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(X5_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X2_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X5_48) != iProver_top
% 3.74/1.00      | v1_funct_1(X0_49) != iProver_top
% 3.74/1.00      | v1_funct_1(k3_tmap_1(X2_48,X1_48,X3_48,X0_48,X0_49)) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_800,c_799]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3006,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK2,sK3,sK5),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k3_tmap_1(sK0,sK1,sK2,sK3,sK5))
% 3.74/1.00      | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK3,X1_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.74/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | v2_struct_0(sK0) = iProver_top
% 3.74/1.00      | v2_struct_0(sK1) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v1_funct_1(k3_tmap_1(sK0,sK1,sK2,sK3,sK5)) != iProver_top
% 3.74/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_2548,c_1955]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3019,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
% 3.74/1.00      | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK3,X1_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.74/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | v2_struct_0(sK0) = iProver_top
% 3.74/1.00      | v2_struct_0(sK1) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top
% 3.74/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.74/1.00      inference(light_normalisation,[status(thm)],[c_3006,c_2548]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3052,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
% 3.74/1.00      | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK3,X1_48) != iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | v2_struct_0(sK1) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_3048,c_799]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3717,plain,
% 3.74/1.00      ( m1_pre_topc(X0_48,sK3) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.74/1.00      | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
% 3.74/1.00      | m1_pre_topc(sK3,X1_48) != iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_3019,c_29,c_30,c_31,c_32,c_33,c_34,c_36,c_38,c_43,
% 3.74/1.00                 c_44,c_45,c_2553,c_2554,c_3052]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3718,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(X0_48)) = k3_tmap_1(X1_48,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3))
% 3.74/1.00      | m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK3,X1_48) != iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_3717]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3725,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
% 3.74/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK4,sK3) != iProver_top
% 3.74/1.00      | v2_struct_0(sK0) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_811,c_3718]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_42,plain,
% 3.74/1.00      ( m1_pre_topc(sK4,sK3) = iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3909,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_3725,c_29,c_30,c_31,c_38,c_42]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_5553,plain,
% 3.74/1.00      ( k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
% 3.74/1.00      inference(demodulation,[status(thm)],[c_5216,c_3909]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_10,plain,
% 3.74/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.74/1.00      | ~ m1_pre_topc(X2,X0)
% 3.74/1.00      | m1_pre_topc(X2,X1)
% 3.74/1.00      | ~ l1_pre_topc(X1)
% 3.74/1.00      | ~ v2_pre_topc(X1) ),
% 3.74/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_311,plain,
% 3.74/1.00      ( ~ m1_pre_topc(X0_48,X1_48)
% 3.74/1.00      | ~ m1_pre_topc(X2_48,X0_48)
% 3.74/1.00      | m1_pre_topc(X2_48,X1_48)
% 3.74/1.00      | ~ l1_pre_topc(X1_48)
% 3.74/1.00      | ~ v2_pre_topc(X1_48) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_804,plain,
% 3.74/1.00      ( m1_pre_topc(X0_48,X1_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X2_48,X0_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X2_48,X1_48) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1689,plain,
% 3.74/1.00      ( m1_pre_topc(X0_48,sK2) = iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_810,c_804]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1322,plain,
% 3.74/1.00      ( m1_pre_topc(X0_48,sK2)
% 3.74/1.00      | ~ m1_pre_topc(X0_48,sK3)
% 3.74/1.00      | ~ m1_pre_topc(sK3,sK2)
% 3.74/1.00      | ~ l1_pre_topc(sK2)
% 3.74/1.00      | ~ v2_pre_topc(sK2) ),
% 3.74/1.00      inference(instantiation,[status(thm)],[c_311]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_1323,plain,
% 3.74/1.00      ( m1_pre_topc(X0_48,sK2) = iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1322]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2068,plain,
% 3.74/1.00      ( m1_pre_topc(X0_48,sK2) = iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK3) != iProver_top ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_1689,c_30,c_31,c_36,c_41,c_1111,c_1301,c_1323]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2074,plain,
% 3.74/1.00      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_809,c_2068]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3728,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3))
% 3.74/1.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK4,sK3) != iProver_top
% 3.74/1.00      | v2_struct_0(sK2) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_2074,c_3718]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_4712,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK4)) = k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_3728,c_30,c_31,c_35,c_36,c_41,c_42,c_1111,c_1301]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_4714,plain,
% 3.74/1.00      ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) ),
% 3.74/1.00      inference(light_normalisation,[status(thm)],[c_4712,c_3909]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_5603,plain,
% 3.74/1.00      ( k3_tmap_1(sK2,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)) = k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4) ),
% 3.74/1.00      inference(demodulation,[status(thm)],[c_5553,c_4714]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_0,plain,
% 3.74/1.00      ( r2_funct_2(X0,X1,X2,X2)
% 3.74/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.74/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.74/1.00      | ~ v1_funct_1(X2) ),
% 3.74/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_321,plain,
% 3.74/1.00      ( r2_funct_2(X0_50,X1_50,X0_49,X0_49)
% 3.74/1.00      | ~ v1_funct_2(X0_49,X0_50,X1_50)
% 3.74/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 3.74/1.00      | ~ v1_funct_1(X0_49) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_794,plain,
% 3.74/1.00      ( r2_funct_2(X0_50,X1_50,X0_49,X0_49) = iProver_top
% 3.74/1.00      | v1_funct_2(X0_49,X0_50,X1_50) != iProver_top
% 3.74/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 3.74/1.00      | v1_funct_1(X0_49) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3056,plain,
% 3.74/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) = iProver_top
% 3.74/1.00      | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_3048,c_794]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3083,plain,
% 3.74/1.00      ( r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK5,sK3),k2_tmap_1(sK2,sK1,sK5,sK3)) = iProver_top ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_3056,c_29,c_30,c_31,c_32,c_33,c_34,c_36,c_38,c_43,
% 3.74/1.00                 c_44,c_45,c_2553,c_2554]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_9,plain,
% 3.74/1.00      ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k2_tmap_1(X3,X1,X4,X0))
% 3.74/1.00      | r2_funct_2(u1_struct_0(X5),u1_struct_0(X1),k3_tmap_1(X3,X1,X0,X5,X2),k2_tmap_1(X3,X1,X4,X5))
% 3.74/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.74/1.00      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 3.74/1.00      | ~ m1_pre_topc(X5,X3)
% 3.74/1.00      | ~ m1_pre_topc(X5,X0)
% 3.74/1.00      | ~ m1_pre_topc(X0,X3)
% 3.74/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.74/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 3.74/1.00      | v2_struct_0(X3)
% 3.74/1.00      | v2_struct_0(X1)
% 3.74/1.00      | v2_struct_0(X5)
% 3.74/1.00      | v2_struct_0(X0)
% 3.74/1.00      | ~ l1_pre_topc(X3)
% 3.74/1.00      | ~ l1_pre_topc(X1)
% 3.74/1.00      | ~ v2_pre_topc(X3)
% 3.74/1.00      | ~ v2_pre_topc(X1)
% 3.74/1.00      | ~ v1_funct_1(X4)
% 3.74/1.00      | ~ v1_funct_1(X2) ),
% 3.74/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_312,plain,
% 3.74/1.00      ( ~ r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k2_tmap_1(X2_48,X1_48,X1_49,X0_48))
% 3.74/1.00      | r2_funct_2(u1_struct_0(X3_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k2_tmap_1(X2_48,X1_48,X1_49,X3_48))
% 3.74/1.00      | ~ v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48))
% 3.74/1.00      | ~ v1_funct_2(X1_49,u1_struct_0(X2_48),u1_struct_0(X1_48))
% 3.74/1.00      | ~ m1_pre_topc(X3_48,X2_48)
% 3.74/1.00      | ~ m1_pre_topc(X3_48,X0_48)
% 3.74/1.00      | ~ m1_pre_topc(X0_48,X2_48)
% 3.74/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48))))
% 3.74/1.00      | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48))))
% 3.74/1.00      | v2_struct_0(X3_48)
% 3.74/1.00      | v2_struct_0(X1_48)
% 3.74/1.00      | v2_struct_0(X0_48)
% 3.74/1.00      | v2_struct_0(X2_48)
% 3.74/1.00      | ~ l1_pre_topc(X1_48)
% 3.74/1.00      | ~ l1_pre_topc(X2_48)
% 3.74/1.00      | ~ v2_pre_topc(X1_48)
% 3.74/1.00      | ~ v2_pre_topc(X2_48)
% 3.74/1.00      | ~ v1_funct_1(X1_49)
% 3.74/1.00      | ~ v1_funct_1(X0_49) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_803,plain,
% 3.74/1.00      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(X1_48),X0_49,k2_tmap_1(X2_48,X1_48,X1_49,X0_48)) != iProver_top
% 3.74/1.00      | r2_funct_2(u1_struct_0(X3_48),u1_struct_0(X1_48),k3_tmap_1(X2_48,X1_48,X0_48,X3_48,X0_49),k2_tmap_1(X2_48,X1_48,X1_49,X3_48)) = iProver_top
% 3.74/1.00      | v1_funct_2(X0_49,u1_struct_0(X0_48),u1_struct_0(X1_48)) != iProver_top
% 3.74/1.00      | v1_funct_2(X1_49,u1_struct_0(X2_48),u1_struct_0(X1_48)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X3_48,X0_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,X2_48) != iProver_top
% 3.74/1.00      | m1_pre_topc(X3_48,X2_48) != iProver_top
% 3.74/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_48),u1_struct_0(X1_48)))) != iProver_top
% 3.74/1.00      | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_48),u1_struct_0(X1_48)))) != iProver_top
% 3.74/1.00      | v2_struct_0(X3_48) = iProver_top
% 3.74/1.00      | v2_struct_0(X1_48) = iProver_top
% 3.74/1.00      | v2_struct_0(X0_48) = iProver_top
% 3.74/1.00      | v2_struct_0(X2_48) = iProver_top
% 3.74/1.00      | l1_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | l1_pre_topc(X2_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X1_48) != iProver_top
% 3.74/1.00      | v2_pre_topc(X2_48) != iProver_top
% 3.74/1.00      | v1_funct_1(X0_49) != iProver_top
% 3.74/1.00      | v1_funct_1(X1_49) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_312]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_3087,plain,
% 3.74/1.00      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
% 3.74/1.00      | v1_funct_2(k2_tmap_1(sK2,sK1,sK5,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK2) != iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK3,sK2) != iProver_top
% 3.74/1.00      | m1_subset_1(k2_tmap_1(sK2,sK1,sK5,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.74/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.74/1.00      | v2_struct_0(X0_48) = iProver_top
% 3.74/1.00      | v2_struct_0(sK2) = iProver_top
% 3.74/1.00      | v2_struct_0(sK3) = iProver_top
% 3.74/1.00      | v2_struct_0(sK1) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK2) != iProver_top
% 3.74/1.00      | l1_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK1) != iProver_top
% 3.74/1.00      | v1_funct_1(k2_tmap_1(sK2,sK1,sK5,sK3)) != iProver_top
% 3.74/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_3083,c_803]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_7415,plain,
% 3.74/1.00      ( v2_struct_0(X0_48) = iProver_top
% 3.74/1.00      | r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK3) != iProver_top ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_3087,c_29,c_30,c_31,c_32,c_33,c_34,c_35,c_36,c_37,
% 3.74/1.00                 c_38,c_41,c_43,c_44,c_45,c_1111,c_1301,c_2068,c_2552,
% 3.74/1.00                 c_2553,c_2554]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_7416,plain,
% 3.74/1.00      ( r2_funct_2(u1_struct_0(X0_48),u1_struct_0(sK1),k3_tmap_1(sK2,sK1,sK3,X0_48,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,X0_48)) = iProver_top
% 3.74/1.00      | m1_pre_topc(X0_48,sK3) != iProver_top
% 3.74/1.00      | v2_struct_0(X0_48) = iProver_top ),
% 3.74/1.00      inference(renaming,[status(thm)],[c_7415]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_7421,plain,
% 3.74/1.00      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) = iProver_top
% 3.74/1.00      | m1_pre_topc(sK4,sK3) != iProver_top
% 3.74/1.00      | v2_struct_0(sK4) = iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_5603,c_7416]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2478,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k3_tmap_1(sK0,sK1,sK2,sK4,sK5)
% 3.74/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.74/1.00      | v2_struct_0(sK0) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_811,c_2471]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2295,plain,
% 3.74/1.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
% 3.74/1.00      inference(superposition,[status(thm)],[c_2074,c_2289]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2484,plain,
% 3.74/1.00      ( k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4)
% 3.74/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.74/1.00      | m1_pre_topc(sK4,sK2) != iProver_top
% 3.74/1.00      | v2_struct_0(sK0) = iProver_top
% 3.74/1.00      | l1_pre_topc(sK0) != iProver_top
% 3.74/1.00      | v2_pre_topc(sK0) != iProver_top ),
% 3.74/1.00      inference(light_normalisation,[status(thm)],[c_2478,c_2295]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2671,plain,
% 3.74/1.00      ( k3_tmap_1(sK0,sK1,sK2,sK4,sK5) = k2_tmap_1(sK2,sK1,sK5,sK4) ),
% 3.74/1.00      inference(global_propositional_subsumption,
% 3.74/1.00                [status(thm)],
% 3.74/1.00                [c_2484,c_29,c_30,c_31,c_36,c_2074]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_11,negated_conjecture,
% 3.74/1.00      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
% 3.74/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_310,negated_conjecture,
% 3.74/1.00      ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) ),
% 3.74/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_805,plain,
% 3.74/1.00      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k3_tmap_1(sK0,sK1,sK2,sK3,sK5)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2550,plain,
% 3.74/1.00      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k3_tmap_1(sK0,sK1,sK2,sK4,sK5)) != iProver_top ),
% 3.74/1.00      inference(demodulation,[status(thm)],[c_2548,c_805]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_2673,plain,
% 3.74/1.00      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK3,sK4,k2_tmap_1(sK2,sK1,sK5,sK3)),k2_tmap_1(sK2,sK1,sK5,sK4)) != iProver_top ),
% 3.74/1.00      inference(demodulation,[status(thm)],[c_2671,c_2550]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_5605,plain,
% 3.74/1.00      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK1),k2_tmap_1(sK3,sK1,k2_tmap_1(sK2,sK1,sK5,sK3),sK4),k2_tmap_1(sK2,sK1,sK5,sK4)) != iProver_top ),
% 3.74/1.00      inference(demodulation,[status(thm)],[c_5553,c_2673]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_18,negated_conjecture,
% 3.74/1.00      ( ~ v2_struct_0(sK4) ),
% 3.74/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(c_39,plain,
% 3.74/1.00      ( v2_struct_0(sK4) != iProver_top ),
% 3.74/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.74/1.00  
% 3.74/1.00  cnf(contradiction,plain,
% 3.74/1.00      ( $false ),
% 3.74/1.00      inference(minisat,[status(thm)],[c_7421,c_5605,c_42,c_39]) ).
% 3.74/1.00  
% 3.74/1.00  
% 3.74/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.74/1.00  
% 3.74/1.00  ------                               Statistics
% 3.74/1.00  
% 3.74/1.00  ------ General
% 3.74/1.00  
% 3.74/1.00  abstr_ref_over_cycles:                  0
% 3.74/1.00  abstr_ref_under_cycles:                 0
% 3.74/1.00  gc_basic_clause_elim:                   0
% 3.74/1.00  forced_gc_time:                         0
% 3.74/1.00  parsing_time:                           0.015
% 3.74/1.00  unif_index_cands_time:                  0.
% 3.74/1.00  unif_index_add_time:                    0.
% 3.74/1.00  orderings_time:                         0.
% 3.74/1.00  out_proof_time:                         0.02
% 3.74/1.00  total_time:                             0.45
% 3.74/1.00  num_of_symbols:                         53
% 3.74/1.00  num_of_terms:                           11235
% 3.74/1.00  
% 3.74/1.00  ------ Preprocessing
% 3.74/1.00  
% 3.74/1.00  num_of_splits:                          0
% 3.74/1.00  num_of_split_atoms:                     0
% 3.74/1.00  num_of_reused_defs:                     0
% 3.74/1.00  num_eq_ax_congr_red:                    31
% 3.74/1.00  num_of_sem_filtered_clauses:            1
% 3.74/1.00  num_of_subtypes:                        5
% 3.74/1.00  monotx_restored_types:                  0
% 3.74/1.00  sat_num_of_epr_types:                   0
% 3.74/1.00  sat_num_of_non_cyclic_types:            0
% 3.74/1.00  sat_guarded_non_collapsed_types:        1
% 3.74/1.00  num_pure_diseq_elim:                    0
% 3.74/1.00  simp_replaced_by:                       0
% 3.74/1.00  res_preprocessed:                       102
% 3.74/1.00  prep_upred:                             0
% 3.74/1.00  prep_unflattend:                        0
% 3.74/1.00  smt_new_axioms:                         0
% 3.74/1.00  pred_elim_cands:                        8
% 3.74/1.00  pred_elim:                              0
% 3.74/1.00  pred_elim_cl:                           0
% 3.74/1.00  pred_elim_cycles:                       1
% 3.74/1.00  merged_defs:                            0
% 3.74/1.00  merged_defs_ncl:                        0
% 3.74/1.00  bin_hyper_res:                          0
% 3.74/1.00  prep_cycles:                            3
% 3.74/1.00  pred_elim_time:                         0.
% 3.74/1.00  splitting_time:                         0.
% 3.74/1.00  sem_filter_time:                        0.
% 3.74/1.00  monotx_time:                            0.
% 3.74/1.00  subtype_inf_time:                       0.
% 3.74/1.00  
% 3.74/1.00  ------ Problem properties
% 3.74/1.00  
% 3.74/1.00  clauses:                                29
% 3.74/1.00  conjectures:                            18
% 3.74/1.00  epr:                                    18
% 3.74/1.00  horn:                                   23
% 3.74/1.00  ground:                                 18
% 3.74/1.00  unary:                                  18
% 3.74/1.00  binary:                                 0
% 3.74/1.00  lits:                                   121
% 3.74/1.00  lits_eq:                                3
% 3.74/1.00  fd_pure:                                0
% 3.74/1.00  fd_pseudo:                              0
% 3.74/1.00  fd_cond:                                0
% 3.74/1.00  fd_pseudo_cond:                         1
% 3.74/1.00  ac_symbols:                             0
% 3.74/1.00  
% 3.74/1.00  ------ Propositional Solver
% 3.74/1.00  
% 3.74/1.00  prop_solver_calls:                      26
% 3.74/1.00  prop_fast_solver_calls:                 2077
% 3.74/1.00  smt_solver_calls:                       0
% 3.74/1.00  smt_fast_solver_calls:                  0
% 3.74/1.00  prop_num_of_clauses:                    4332
% 3.74/1.00  prop_preprocess_simplified:             8214
% 3.74/1.00  prop_fo_subsumed:                       475
% 3.74/1.00  prop_solver_time:                       0.
% 3.74/1.00  smt_solver_time:                        0.
% 3.74/1.00  smt_fast_solver_time:                   0.
% 3.74/1.00  prop_fast_solver_time:                  0.
% 3.74/1.00  prop_unsat_core_time:                   0.001
% 3.74/1.00  
% 3.74/1.00  ------ QBF
% 3.74/1.00  
% 3.74/1.00  qbf_q_res:                              0
% 3.74/1.00  qbf_num_tautologies:                    0
% 3.74/1.00  qbf_prep_cycles:                        0
% 3.74/1.00  
% 3.74/1.00  ------ BMC1
% 3.74/1.00  
% 3.74/1.00  bmc1_current_bound:                     -1
% 3.74/1.00  bmc1_last_solved_bound:                 -1
% 3.74/1.00  bmc1_unsat_core_size:                   -1
% 3.74/1.00  bmc1_unsat_core_parents_size:           -1
% 3.74/1.00  bmc1_merge_next_fun:                    0
% 3.74/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.74/1.00  
% 3.74/1.00  ------ Instantiation
% 3.74/1.00  
% 3.74/1.00  inst_num_of_clauses:                    1019
% 3.74/1.00  inst_num_in_passive:                    194
% 3.74/1.00  inst_num_in_active:                     513
% 3.74/1.00  inst_num_in_unprocessed:                312
% 3.74/1.00  inst_num_of_loops:                      610
% 3.74/1.00  inst_num_of_learning_restarts:          0
% 3.74/1.00  inst_num_moves_active_passive:          94
% 3.74/1.00  inst_lit_activity:                      0
% 3.74/1.00  inst_lit_activity_moves:                0
% 3.74/1.00  inst_num_tautologies:                   0
% 3.74/1.00  inst_num_prop_implied:                  0
% 3.74/1.00  inst_num_existing_simplified:           0
% 3.74/1.00  inst_num_eq_res_simplified:             0
% 3.74/1.00  inst_num_child_elim:                    0
% 3.74/1.00  inst_num_of_dismatching_blockings:      214
% 3.74/1.00  inst_num_of_non_proper_insts:           855
% 3.74/1.00  inst_num_of_duplicates:                 0
% 3.74/1.00  inst_inst_num_from_inst_to_res:         0
% 3.74/1.00  inst_dismatching_checking_time:         0.
% 3.74/1.00  
% 3.74/1.00  ------ Resolution
% 3.74/1.00  
% 3.74/1.00  res_num_of_clauses:                     0
% 3.74/1.00  res_num_in_passive:                     0
% 3.74/1.00  res_num_in_active:                      0
% 3.74/1.00  res_num_of_loops:                       105
% 3.74/1.00  res_forward_subset_subsumed:            26
% 3.74/1.00  res_backward_subset_subsumed:           0
% 3.74/1.00  res_forward_subsumed:                   0
% 3.74/1.00  res_backward_subsumed:                  0
% 3.74/1.00  res_forward_subsumption_resolution:     0
% 3.74/1.00  res_backward_subsumption_resolution:    0
% 3.74/1.00  res_clause_to_clause_subsumption:       297
% 3.74/1.00  res_orphan_elimination:                 0
% 3.74/1.00  res_tautology_del:                      15
% 3.74/1.00  res_num_eq_res_simplified:              0
% 3.74/1.00  res_num_sel_changes:                    0
% 3.74/1.00  res_moves_from_active_to_pass:          0
% 3.74/1.00  
% 3.74/1.00  ------ Superposition
% 3.74/1.00  
% 3.74/1.00  sup_time_total:                         0.
% 3.74/1.00  sup_time_generating:                    0.
% 3.74/1.00  sup_time_sim_full:                      0.
% 3.74/1.00  sup_time_sim_immed:                     0.
% 3.74/1.00  
% 3.74/1.00  sup_num_of_clauses:                     129
% 3.74/1.00  sup_num_in_active:                      108
% 3.74/1.00  sup_num_in_passive:                     21
% 3.74/1.00  sup_num_of_loops:                       120
% 3.74/1.00  sup_fw_superposition:                   92
% 3.74/1.00  sup_bw_superposition:                   55
% 3.74/1.00  sup_immediate_simplified:               29
% 3.74/1.00  sup_given_eliminated:                   2
% 3.74/1.00  comparisons_done:                       0
% 3.74/1.00  comparisons_avoided:                    0
% 3.74/1.00  
% 3.74/1.00  ------ Simplifications
% 3.74/1.00  
% 3.74/1.00  
% 3.74/1.00  sim_fw_subset_subsumed:                 13
% 3.74/1.00  sim_bw_subset_subsumed:                 1
% 3.74/1.00  sim_fw_subsumed:                        4
% 3.74/1.00  sim_bw_subsumed:                        2
% 3.74/1.00  sim_fw_subsumption_res:                 0
% 3.74/1.00  sim_bw_subsumption_res:                 0
% 3.74/1.00  sim_tautology_del:                      0
% 3.74/1.00  sim_eq_tautology_del:                   3
% 3.74/1.00  sim_eq_res_simp:                        0
% 3.74/1.00  sim_fw_demodulated:                     6
% 3.74/1.00  sim_bw_demodulated:                     11
% 3.74/1.00  sim_light_normalised:                   24
% 3.74/1.00  sim_joinable_taut:                      0
% 3.74/1.00  sim_joinable_simp:                      0
% 3.74/1.00  sim_ac_normalised:                      0
% 3.74/1.00  sim_smt_subsumption:                    0
% 3.74/1.00  
%------------------------------------------------------------------------------
