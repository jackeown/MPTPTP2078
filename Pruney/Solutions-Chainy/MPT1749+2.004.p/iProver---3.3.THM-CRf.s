%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:21 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  220 (3246 expanded)
%              Number of clauses        :  137 ( 760 expanded)
%              Number of leaves         :   21 (1249 expanded)
%              Depth                    :   26
%              Number of atoms          :  976 (45474 expanded)
%              Number of equality atoms :  211 (3706 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ( r2_hidden(X5,u1_struct_0(X2))
                               => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                         => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
          & ! [X5] :
              ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
              | ~ r2_hidden(X5,u1_struct_0(X2))
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK5)
        & ! [X5] :
            ( k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
            | ~ r2_hidden(X5,u1_struct_0(X2))
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
              & ! [X5] :
                  ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                  | ~ r2_hidden(X5,u1_struct_0(X2))
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK4,X2),X4)
            & ! [X5] :
                ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),sK4,X5)
                | ~ r2_hidden(X5,u1_struct_0(X2))
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                  & ! [X5] :
                      ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                      | ~ r2_hidden(X5,u1_struct_0(X2))
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK3),X4)
                & ! [X5] :
                    ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                    | ~ r2_hidden(X5,u1_struct_0(sK3))
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X3) )
        & m1_pre_topc(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK2,X0,X3,X2),X4)
                    & ! [X5] :
                        ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X3,X5)
                        | ~ r2_hidden(X5,u1_struct_0(X2))
                        | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                        & ! [X5] :
                            ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                            | ~ r2_hidden(X5,u1_struct_0(X2))
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
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
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X1,sK1,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK1),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)
    & ! [X5] :
        ( k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X5)
        | ~ r2_hidden(X5,u1_struct_0(sK3))
        | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f40,f49,f48,f47,f46,f45])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

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
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f72,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f69,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r2_funct_2(X0,X1,X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                  | ~ m1_subset_1(X4,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & m1_subset_1(X4,X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & m1_subset_1(X4,X0) )
     => ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
        & m1_subset_1(sK0(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r2_funct_2(X0,X1,X2,X3)
              | ( k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
                & m1_subset_1(sK0(X0,X2,X3),X0) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X3,X5)
                  | ~ m1_subset_1(X5,X0) )
              | ~ r2_funct_2(X0,X1,X2,X3) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | m1_subset_1(sK0(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,(
    ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
    ! [X5] :
      ( k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X5)
      | ~ r2_hidden(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1316,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1887,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1316])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_507,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | sK2 != X1
    | sK3 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_508,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_512,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_30,c_29,c_28])).

cnf(c_513,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
    inference(renaming,[status(thm)],[c_512])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_576,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_513,c_32])).

cnf(c_577,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0,sK3) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_581,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_577,c_33,c_31])).

cnf(c_1311,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0_54,sK3) ),
    inference(subtyping,[status(esa)],[c_581])).

cnf(c_1892,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0_54,sK3)
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1311])).

cnf(c_2841,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1887,c_1892])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1325,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1878,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1325])).

cnf(c_2302,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1887,c_1878])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2767,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2302,c_42])).

cnf(c_2843,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK3) = k7_relat_1(sK4,u1_struct_0(sK3))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2841,c_2767])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_43,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3339,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK3) = k7_relat_1(sK4,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2843,c_42,c_43])).

cnf(c_6,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(sK0(X0,X2,X3),X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_18,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_860,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK0(X1,X3,X0),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK2,sK1,sK4,sK3) != X3
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK3) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_861,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_1(sK5) ),
    inference(unflattening,[status(thm)],[c_860])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_863,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_861,c_22,c_21,c_20])).

cnf(c_864,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) ),
    inference(renaming,[status(thm)],[c_863])).

cnf(c_1302,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) ),
    inference(subtyping,[status(esa)],[c_864])).

cnf(c_1901,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1302])).

cnf(c_36,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_71,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_73,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_610,plain,
    ( l1_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_28])).

cnf(c_611,plain,
    ( l1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_612,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_496,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_497,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_499,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_28])).

cnf(c_624,plain,
    ( l1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_499])).

cnf(c_625,plain,
    ( l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_626,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_865,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_864])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1321,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ l1_struct_0(X1_55)
    | ~ l1_struct_0(X2_55)
    | ~ l1_struct_0(X0_55)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_tmap_1(X0_55,X1_55,X0_54,X2_55)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1961,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_1962,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1961])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1322,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v1_funct_2(k2_tmap_1(X0_55,X1_55,X0_54,X2_55),u1_struct_0(X2_55),u1_struct_0(X1_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ l1_struct_0(X1_55)
    | ~ l1_struct_0(X2_55)
    | ~ l1_struct_0(X0_55)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2028,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1322])).

cnf(c_2029,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2028])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1323,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | m1_subset_1(k2_tmap_1(X0_55,X1_55,X0_54,X2_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ l1_struct_0(X1_55)
    | ~ l1_struct_0(X2_55)
    | ~ l1_struct_0(X0_55)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2057,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_2058,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2057])).

cnf(c_2900,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1901,c_36,c_42,c_43,c_44,c_73,c_612,c_626,c_865,c_1962,c_2029,c_2058])).

cnf(c_3342,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3339,c_2900])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1330,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | r2_hidden(X0_54,X1_54)
    | v1_xboole_0(X1_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1873,plain,
    ( m1_subset_1(X0_54,X1_54) != iProver_top
    | r2_hidden(X0_54,X1_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1330])).

cnf(c_3351,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3342,c_1873])).

cnf(c_12,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_637,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_638,plain,
    ( ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_639,plain,
    ( l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_3507,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3351,c_626,c_639])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_485,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_486,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_488,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_28])).

cnf(c_1313,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_488])).

cnf(c_1890,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1313])).

cnf(c_1,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1329,plain,
    ( m1_subset_1(X0_54,X1_54)
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(X1_54))
    | ~ r2_hidden(X0_54,X2_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1874,plain,
    ( m1_subset_1(X0_54,X1_54) = iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(X1_54)) != iProver_top
    | r2_hidden(X0_54,X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1329])).

cnf(c_2441,plain,
    ( m1_subset_1(X0_54,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0_54,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1890,c_1874])).

cnf(c_3511,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3507,c_2441])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1324,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ m1_subset_1(X3_54,X1_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | v1_xboole_0(X1_54)
    | k3_funct_2(X1_54,X2_54,X0_54,X3_54) = k1_funct_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1879,plain,
    ( k3_funct_2(X0_54,X1_54,X2_54,X3_54) = k1_funct_1(X2_54,X3_54)
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | m1_subset_1(X3_54,X0_54) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1324])).

cnf(c_2624,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK4,X0_54)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1887,c_1879])).

cnf(c_648,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_649,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_650,plain,
    ( l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_3238,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK4,X0_54)
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2624,c_42,c_43,c_612,c_650])).

cnf(c_5190,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
    inference(superposition,[status(thm)],[c_3511,c_3238])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,u1_struct_0(sK3))
    | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1320,negated_conjecture,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ r2_hidden(X0_54,u1_struct_0(sK3))
    | k1_funct_1(sK5,X0_54) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1883,plain,
    ( k1_funct_1(sK5,X0_54) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54)
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_54,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1320])).

cnf(c_5191,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
    | r2_hidden(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3511,c_1883])).

cnf(c_5194,plain,
    ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
    | r2_hidden(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5190,c_5191])).

cnf(c_1314,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1889,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1314])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1326,plain,
    ( ~ r2_hidden(X0_54,X1_54)
    | ~ v1_funct_1(X2_54)
    | ~ v1_relat_1(X2_54)
    | k1_funct_1(k7_relat_1(X2_54,X1_54),X0_54) = k1_funct_1(X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1877,plain,
    ( k1_funct_1(k7_relat_1(X0_54,X1_54),X2_54) = k1_funct_1(X0_54,X2_54)
    | r2_hidden(X2_54,X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1326])).

cnf(c_3512,plain,
    ( k1_funct_1(k7_relat_1(X0_54,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(X0_54,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_3507,c_1877])).

cnf(c_4484,plain,
    ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1889,c_3512])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1327,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1876,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1327])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1328,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ v1_relat_1(X1_54)
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1875,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
    | v1_relat_1(X1_54) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1328])).

cnf(c_2249,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1887,c_1875])).

cnf(c_2526,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1876,c_2249])).

cnf(c_3515,plain,
    ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3512])).

cnf(c_4550,plain,
    ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4484,c_42,c_2526,c_3515])).

cnf(c_5,plain,
    ( r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_880,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK2,sK1,sK4,sK3) != X3
    | k1_funct_1(X0,sK0(X1,X3,X0)) != k1_funct_1(X3,sK0(X1,X3,X0))
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK3) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_18])).

cnf(c_881,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_1(sK5)
    | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(unflattening,[status(thm)],[c_880])).

cnf(c_883,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_881,c_22,c_21,c_20])).

cnf(c_884,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(renaming,[status(thm)],[c_883])).

cnf(c_1301,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(subtyping,[status(esa)],[c_884])).

cnf(c_1902,plain,
    ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5))
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1301])).

cnf(c_72,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3120,plain,
    ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1902,c_31,c_25,c_24,c_23,c_72,c_611,c_625,c_1301,c_1961,c_2028,c_2057])).

cnf(c_3341,plain,
    ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) != k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
    inference(demodulation,[status(thm)],[c_3339,c_3120])).

cnf(c_4552,plain,
    ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) != k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
    inference(demodulation,[status(thm)],[c_4550,c_3341])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5194,c_4552,c_3351,c_639,c_626])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:30:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.90/1.06  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.06  
% 2.90/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.90/1.06  
% 2.90/1.06  ------  iProver source info
% 2.90/1.06  
% 2.90/1.06  git: date: 2020-06-30 10:37:57 +0100
% 2.90/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.90/1.06  git: non_committed_changes: false
% 2.90/1.06  git: last_make_outside_of_git: false
% 2.90/1.06  
% 2.90/1.06  ------ 
% 2.90/1.06  
% 2.90/1.06  ------ Input Options
% 2.90/1.06  
% 2.90/1.06  --out_options                           all
% 2.90/1.06  --tptp_safe_out                         true
% 2.90/1.06  --problem_path                          ""
% 2.90/1.06  --include_path                          ""
% 2.90/1.06  --clausifier                            res/vclausify_rel
% 2.90/1.06  --clausifier_options                    ""
% 2.90/1.06  --stdin                                 false
% 2.90/1.06  --stats_out                             all
% 2.90/1.06  
% 2.90/1.06  ------ General Options
% 2.90/1.06  
% 2.90/1.06  --fof                                   false
% 2.90/1.06  --time_out_real                         305.
% 2.90/1.06  --time_out_virtual                      -1.
% 2.90/1.06  --symbol_type_check                     false
% 2.90/1.06  --clausify_out                          false
% 2.90/1.06  --sig_cnt_out                           false
% 2.90/1.06  --trig_cnt_out                          false
% 2.90/1.06  --trig_cnt_out_tolerance                1.
% 2.90/1.06  --trig_cnt_out_sk_spl                   false
% 2.90/1.06  --abstr_cl_out                          false
% 2.90/1.06  
% 2.90/1.06  ------ Global Options
% 2.90/1.06  
% 2.90/1.06  --schedule                              default
% 2.90/1.06  --add_important_lit                     false
% 2.90/1.06  --prop_solver_per_cl                    1000
% 2.90/1.06  --min_unsat_core                        false
% 2.90/1.06  --soft_assumptions                      false
% 2.90/1.06  --soft_lemma_size                       3
% 2.90/1.06  --prop_impl_unit_size                   0
% 2.90/1.06  --prop_impl_unit                        []
% 2.90/1.06  --share_sel_clauses                     true
% 2.90/1.06  --reset_solvers                         false
% 2.90/1.06  --bc_imp_inh                            [conj_cone]
% 2.90/1.06  --conj_cone_tolerance                   3.
% 2.90/1.06  --extra_neg_conj                        none
% 2.90/1.06  --large_theory_mode                     true
% 2.90/1.06  --prolific_symb_bound                   200
% 2.90/1.06  --lt_threshold                          2000
% 2.90/1.06  --clause_weak_htbl                      true
% 2.90/1.06  --gc_record_bc_elim                     false
% 2.90/1.06  
% 2.90/1.06  ------ Preprocessing Options
% 2.90/1.06  
% 2.90/1.06  --preprocessing_flag                    true
% 2.90/1.06  --time_out_prep_mult                    0.1
% 2.90/1.06  --splitting_mode                        input
% 2.90/1.06  --splitting_grd                         true
% 2.90/1.06  --splitting_cvd                         false
% 2.90/1.06  --splitting_cvd_svl                     false
% 2.90/1.06  --splitting_nvd                         32
% 2.90/1.06  --sub_typing                            true
% 2.90/1.06  --prep_gs_sim                           true
% 2.90/1.06  --prep_unflatten                        true
% 2.90/1.06  --prep_res_sim                          true
% 2.90/1.06  --prep_upred                            true
% 2.90/1.06  --prep_sem_filter                       exhaustive
% 2.90/1.06  --prep_sem_filter_out                   false
% 2.90/1.06  --pred_elim                             true
% 2.90/1.06  --res_sim_input                         true
% 2.90/1.06  --eq_ax_congr_red                       true
% 2.90/1.06  --pure_diseq_elim                       true
% 2.90/1.06  --brand_transform                       false
% 2.90/1.06  --non_eq_to_eq                          false
% 2.90/1.06  --prep_def_merge                        true
% 2.90/1.06  --prep_def_merge_prop_impl              false
% 2.90/1.06  --prep_def_merge_mbd                    true
% 2.90/1.06  --prep_def_merge_tr_red                 false
% 2.90/1.06  --prep_def_merge_tr_cl                  false
% 2.90/1.06  --smt_preprocessing                     true
% 2.90/1.06  --smt_ac_axioms                         fast
% 2.90/1.06  --preprocessed_out                      false
% 2.90/1.06  --preprocessed_stats                    false
% 2.90/1.06  
% 2.90/1.06  ------ Abstraction refinement Options
% 2.90/1.06  
% 2.90/1.06  --abstr_ref                             []
% 2.90/1.06  --abstr_ref_prep                        false
% 2.90/1.06  --abstr_ref_until_sat                   false
% 2.90/1.06  --abstr_ref_sig_restrict                funpre
% 2.90/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.90/1.06  --abstr_ref_under                       []
% 2.90/1.06  
% 2.90/1.06  ------ SAT Options
% 2.90/1.06  
% 2.90/1.06  --sat_mode                              false
% 2.90/1.06  --sat_fm_restart_options                ""
% 2.90/1.06  --sat_gr_def                            false
% 2.90/1.06  --sat_epr_types                         true
% 2.90/1.06  --sat_non_cyclic_types                  false
% 2.90/1.06  --sat_finite_models                     false
% 2.90/1.06  --sat_fm_lemmas                         false
% 2.90/1.06  --sat_fm_prep                           false
% 2.90/1.06  --sat_fm_uc_incr                        true
% 2.90/1.06  --sat_out_model                         small
% 2.90/1.06  --sat_out_clauses                       false
% 2.90/1.06  
% 2.90/1.06  ------ QBF Options
% 2.90/1.06  
% 2.90/1.06  --qbf_mode                              false
% 2.90/1.06  --qbf_elim_univ                         false
% 2.90/1.06  --qbf_dom_inst                          none
% 2.90/1.06  --qbf_dom_pre_inst                      false
% 2.90/1.06  --qbf_sk_in                             false
% 2.90/1.06  --qbf_pred_elim                         true
% 2.90/1.06  --qbf_split                             512
% 2.90/1.06  
% 2.90/1.06  ------ BMC1 Options
% 2.90/1.06  
% 2.90/1.06  --bmc1_incremental                      false
% 2.90/1.06  --bmc1_axioms                           reachable_all
% 2.90/1.06  --bmc1_min_bound                        0
% 2.90/1.06  --bmc1_max_bound                        -1
% 2.90/1.06  --bmc1_max_bound_default                -1
% 2.90/1.06  --bmc1_symbol_reachability              true
% 2.90/1.06  --bmc1_property_lemmas                  false
% 2.90/1.06  --bmc1_k_induction                      false
% 2.90/1.06  --bmc1_non_equiv_states                 false
% 2.90/1.06  --bmc1_deadlock                         false
% 2.90/1.06  --bmc1_ucm                              false
% 2.90/1.06  --bmc1_add_unsat_core                   none
% 2.90/1.06  --bmc1_unsat_core_children              false
% 2.90/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.90/1.06  --bmc1_out_stat                         full
% 2.90/1.06  --bmc1_ground_init                      false
% 2.90/1.06  --bmc1_pre_inst_next_state              false
% 2.90/1.06  --bmc1_pre_inst_state                   false
% 2.90/1.06  --bmc1_pre_inst_reach_state             false
% 2.90/1.06  --bmc1_out_unsat_core                   false
% 2.90/1.06  --bmc1_aig_witness_out                  false
% 2.90/1.06  --bmc1_verbose                          false
% 2.90/1.06  --bmc1_dump_clauses_tptp                false
% 2.90/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.90/1.06  --bmc1_dump_file                        -
% 2.90/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.90/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.90/1.06  --bmc1_ucm_extend_mode                  1
% 2.90/1.06  --bmc1_ucm_init_mode                    2
% 2.90/1.06  --bmc1_ucm_cone_mode                    none
% 2.90/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.90/1.06  --bmc1_ucm_relax_model                  4
% 2.90/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.90/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.90/1.06  --bmc1_ucm_layered_model                none
% 2.90/1.06  --bmc1_ucm_max_lemma_size               10
% 2.90/1.06  
% 2.90/1.06  ------ AIG Options
% 2.90/1.06  
% 2.90/1.06  --aig_mode                              false
% 2.90/1.06  
% 2.90/1.06  ------ Instantiation Options
% 2.90/1.06  
% 2.90/1.06  --instantiation_flag                    true
% 2.90/1.06  --inst_sos_flag                         true
% 2.90/1.06  --inst_sos_phase                        true
% 2.90/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.90/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.90/1.06  --inst_lit_sel_side                     num_symb
% 2.90/1.06  --inst_solver_per_active                1400
% 2.90/1.06  --inst_solver_calls_frac                1.
% 2.90/1.06  --inst_passive_queue_type               priority_queues
% 2.90/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.90/1.06  --inst_passive_queues_freq              [25;2]
% 2.90/1.06  --inst_dismatching                      true
% 2.90/1.06  --inst_eager_unprocessed_to_passive     true
% 2.90/1.06  --inst_prop_sim_given                   true
% 2.90/1.06  --inst_prop_sim_new                     false
% 2.90/1.06  --inst_subs_new                         false
% 2.90/1.06  --inst_eq_res_simp                      false
% 2.90/1.06  --inst_subs_given                       false
% 2.90/1.06  --inst_orphan_elimination               true
% 2.90/1.06  --inst_learning_loop_flag               true
% 2.90/1.06  --inst_learning_start                   3000
% 2.90/1.06  --inst_learning_factor                  2
% 2.90/1.06  --inst_start_prop_sim_after_learn       3
% 2.90/1.06  --inst_sel_renew                        solver
% 2.90/1.06  --inst_lit_activity_flag                true
% 2.90/1.06  --inst_restr_to_given                   false
% 2.90/1.06  --inst_activity_threshold               500
% 2.90/1.06  --inst_out_proof                        true
% 2.90/1.06  
% 2.90/1.06  ------ Resolution Options
% 2.90/1.06  
% 2.90/1.06  --resolution_flag                       true
% 2.90/1.06  --res_lit_sel                           adaptive
% 2.90/1.06  --res_lit_sel_side                      none
% 2.90/1.06  --res_ordering                          kbo
% 2.90/1.06  --res_to_prop_solver                    active
% 2.90/1.06  --res_prop_simpl_new                    false
% 2.90/1.06  --res_prop_simpl_given                  true
% 2.90/1.06  --res_passive_queue_type                priority_queues
% 2.90/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.90/1.06  --res_passive_queues_freq               [15;5]
% 2.90/1.06  --res_forward_subs                      full
% 2.90/1.06  --res_backward_subs                     full
% 2.90/1.06  --res_forward_subs_resolution           true
% 2.90/1.06  --res_backward_subs_resolution          true
% 2.90/1.06  --res_orphan_elimination                true
% 2.90/1.06  --res_time_limit                        2.
% 2.90/1.06  --res_out_proof                         true
% 2.90/1.06  
% 2.90/1.06  ------ Superposition Options
% 2.90/1.06  
% 2.90/1.06  --superposition_flag                    true
% 2.90/1.06  --sup_passive_queue_type                priority_queues
% 2.90/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.90/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.90/1.06  --demod_completeness_check              fast
% 2.90/1.06  --demod_use_ground                      true
% 2.90/1.06  --sup_to_prop_solver                    passive
% 2.90/1.06  --sup_prop_simpl_new                    true
% 2.90/1.06  --sup_prop_simpl_given                  true
% 2.90/1.06  --sup_fun_splitting                     true
% 2.90/1.06  --sup_smt_interval                      50000
% 2.90/1.06  
% 2.90/1.06  ------ Superposition Simplification Setup
% 2.90/1.06  
% 2.90/1.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.90/1.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.90/1.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.90/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.90/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.90/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.90/1.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.90/1.06  --sup_immed_triv                        [TrivRules]
% 2.90/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/1.06  --sup_immed_bw_main                     []
% 2.90/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.90/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.90/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/1.06  --sup_input_bw                          []
% 2.90/1.06  
% 2.90/1.06  ------ Combination Options
% 2.90/1.06  
% 2.90/1.06  --comb_res_mult                         3
% 2.90/1.06  --comb_sup_mult                         2
% 2.90/1.06  --comb_inst_mult                        10
% 2.90/1.06  
% 2.90/1.06  ------ Debug Options
% 2.90/1.06  
% 2.90/1.06  --dbg_backtrace                         false
% 2.90/1.06  --dbg_dump_prop_clauses                 false
% 2.90/1.06  --dbg_dump_prop_clauses_file            -
% 2.90/1.06  --dbg_out_stat                          false
% 2.90/1.06  ------ Parsing...
% 2.90/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.90/1.06  
% 2.90/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.90/1.06  
% 2.90/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.90/1.06  
% 2.90/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.90/1.06  ------ Proving...
% 2.90/1.06  ------ Problem Properties 
% 2.90/1.06  
% 2.90/1.06  
% 2.90/1.06  clauses                                 30
% 2.90/1.06  conjectures                             7
% 2.90/1.06  EPR                                     6
% 2.90/1.06  Horn                                    27
% 2.90/1.06  unary                                   14
% 2.90/1.06  binary                                  0
% 2.90/1.06  lits                                    94
% 2.90/1.06  lits eq                                 10
% 2.90/1.06  fd_pure                                 0
% 2.90/1.06  fd_pseudo                               0
% 2.90/1.06  fd_cond                                 0
% 2.90/1.06  fd_pseudo_cond                          0
% 2.90/1.06  AC symbols                              0
% 2.90/1.06  
% 2.90/1.06  ------ Schedule dynamic 5 is on 
% 2.90/1.06  
% 2.90/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.90/1.06  
% 2.90/1.06  
% 2.90/1.06  ------ 
% 2.90/1.06  Current options:
% 2.90/1.06  ------ 
% 2.90/1.06  
% 2.90/1.06  ------ Input Options
% 2.90/1.06  
% 2.90/1.06  --out_options                           all
% 2.90/1.06  --tptp_safe_out                         true
% 2.90/1.06  --problem_path                          ""
% 2.90/1.06  --include_path                          ""
% 2.90/1.06  --clausifier                            res/vclausify_rel
% 2.90/1.06  --clausifier_options                    ""
% 2.90/1.06  --stdin                                 false
% 2.90/1.06  --stats_out                             all
% 2.90/1.06  
% 2.90/1.06  ------ General Options
% 2.90/1.06  
% 2.90/1.06  --fof                                   false
% 2.90/1.06  --time_out_real                         305.
% 2.90/1.06  --time_out_virtual                      -1.
% 2.90/1.06  --symbol_type_check                     false
% 2.90/1.06  --clausify_out                          false
% 2.90/1.06  --sig_cnt_out                           false
% 2.90/1.06  --trig_cnt_out                          false
% 2.90/1.06  --trig_cnt_out_tolerance                1.
% 2.90/1.06  --trig_cnt_out_sk_spl                   false
% 2.90/1.06  --abstr_cl_out                          false
% 2.90/1.06  
% 2.90/1.06  ------ Global Options
% 2.90/1.06  
% 2.90/1.06  --schedule                              default
% 2.90/1.06  --add_important_lit                     false
% 2.90/1.06  --prop_solver_per_cl                    1000
% 2.90/1.06  --min_unsat_core                        false
% 2.90/1.06  --soft_assumptions                      false
% 2.90/1.06  --soft_lemma_size                       3
% 2.90/1.06  --prop_impl_unit_size                   0
% 2.90/1.06  --prop_impl_unit                        []
% 2.90/1.06  --share_sel_clauses                     true
% 2.90/1.06  --reset_solvers                         false
% 2.90/1.06  --bc_imp_inh                            [conj_cone]
% 2.90/1.06  --conj_cone_tolerance                   3.
% 2.90/1.06  --extra_neg_conj                        none
% 2.90/1.06  --large_theory_mode                     true
% 2.90/1.06  --prolific_symb_bound                   200
% 2.90/1.06  --lt_threshold                          2000
% 2.90/1.06  --clause_weak_htbl                      true
% 2.90/1.06  --gc_record_bc_elim                     false
% 2.90/1.06  
% 2.90/1.06  ------ Preprocessing Options
% 2.90/1.06  
% 2.90/1.06  --preprocessing_flag                    true
% 2.90/1.06  --time_out_prep_mult                    0.1
% 2.90/1.06  --splitting_mode                        input
% 2.90/1.06  --splitting_grd                         true
% 2.90/1.06  --splitting_cvd                         false
% 2.90/1.06  --splitting_cvd_svl                     false
% 2.90/1.06  --splitting_nvd                         32
% 2.90/1.06  --sub_typing                            true
% 2.90/1.06  --prep_gs_sim                           true
% 2.90/1.06  --prep_unflatten                        true
% 2.90/1.06  --prep_res_sim                          true
% 2.90/1.06  --prep_upred                            true
% 2.90/1.06  --prep_sem_filter                       exhaustive
% 2.90/1.06  --prep_sem_filter_out                   false
% 2.90/1.06  --pred_elim                             true
% 2.90/1.06  --res_sim_input                         true
% 2.90/1.06  --eq_ax_congr_red                       true
% 2.90/1.06  --pure_diseq_elim                       true
% 2.90/1.06  --brand_transform                       false
% 2.90/1.06  --non_eq_to_eq                          false
% 2.90/1.06  --prep_def_merge                        true
% 2.90/1.06  --prep_def_merge_prop_impl              false
% 2.90/1.06  --prep_def_merge_mbd                    true
% 2.90/1.06  --prep_def_merge_tr_red                 false
% 2.90/1.06  --prep_def_merge_tr_cl                  false
% 2.90/1.06  --smt_preprocessing                     true
% 2.90/1.06  --smt_ac_axioms                         fast
% 2.90/1.06  --preprocessed_out                      false
% 2.90/1.06  --preprocessed_stats                    false
% 2.90/1.06  
% 2.90/1.06  ------ Abstraction refinement Options
% 2.90/1.06  
% 2.90/1.06  --abstr_ref                             []
% 2.90/1.06  --abstr_ref_prep                        false
% 2.90/1.06  --abstr_ref_until_sat                   false
% 2.90/1.06  --abstr_ref_sig_restrict                funpre
% 2.90/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.90/1.06  --abstr_ref_under                       []
% 2.90/1.06  
% 2.90/1.06  ------ SAT Options
% 2.90/1.06  
% 2.90/1.06  --sat_mode                              false
% 2.90/1.06  --sat_fm_restart_options                ""
% 2.90/1.06  --sat_gr_def                            false
% 2.90/1.06  --sat_epr_types                         true
% 2.90/1.06  --sat_non_cyclic_types                  false
% 2.90/1.06  --sat_finite_models                     false
% 2.90/1.06  --sat_fm_lemmas                         false
% 2.90/1.06  --sat_fm_prep                           false
% 2.90/1.06  --sat_fm_uc_incr                        true
% 2.90/1.06  --sat_out_model                         small
% 2.90/1.06  --sat_out_clauses                       false
% 2.90/1.06  
% 2.90/1.06  ------ QBF Options
% 2.90/1.06  
% 2.90/1.06  --qbf_mode                              false
% 2.90/1.06  --qbf_elim_univ                         false
% 2.90/1.06  --qbf_dom_inst                          none
% 2.90/1.06  --qbf_dom_pre_inst                      false
% 2.90/1.06  --qbf_sk_in                             false
% 2.90/1.06  --qbf_pred_elim                         true
% 2.90/1.06  --qbf_split                             512
% 2.90/1.06  
% 2.90/1.06  ------ BMC1 Options
% 2.90/1.06  
% 2.90/1.06  --bmc1_incremental                      false
% 2.90/1.06  --bmc1_axioms                           reachable_all
% 2.90/1.06  --bmc1_min_bound                        0
% 2.90/1.06  --bmc1_max_bound                        -1
% 2.90/1.06  --bmc1_max_bound_default                -1
% 2.90/1.06  --bmc1_symbol_reachability              true
% 2.90/1.06  --bmc1_property_lemmas                  false
% 2.90/1.06  --bmc1_k_induction                      false
% 2.90/1.06  --bmc1_non_equiv_states                 false
% 2.90/1.06  --bmc1_deadlock                         false
% 2.90/1.06  --bmc1_ucm                              false
% 2.90/1.06  --bmc1_add_unsat_core                   none
% 2.90/1.06  --bmc1_unsat_core_children              false
% 2.90/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.90/1.06  --bmc1_out_stat                         full
% 2.90/1.06  --bmc1_ground_init                      false
% 2.90/1.06  --bmc1_pre_inst_next_state              false
% 2.90/1.06  --bmc1_pre_inst_state                   false
% 2.90/1.06  --bmc1_pre_inst_reach_state             false
% 2.90/1.06  --bmc1_out_unsat_core                   false
% 2.90/1.06  --bmc1_aig_witness_out                  false
% 2.90/1.06  --bmc1_verbose                          false
% 2.90/1.06  --bmc1_dump_clauses_tptp                false
% 2.90/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.90/1.06  --bmc1_dump_file                        -
% 2.90/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.90/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.90/1.06  --bmc1_ucm_extend_mode                  1
% 2.90/1.06  --bmc1_ucm_init_mode                    2
% 2.90/1.06  --bmc1_ucm_cone_mode                    none
% 2.90/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.90/1.06  --bmc1_ucm_relax_model                  4
% 2.90/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.90/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.90/1.06  --bmc1_ucm_layered_model                none
% 2.90/1.06  --bmc1_ucm_max_lemma_size               10
% 2.90/1.06  
% 2.90/1.06  ------ AIG Options
% 2.90/1.06  
% 2.90/1.06  --aig_mode                              false
% 2.90/1.06  
% 2.90/1.06  ------ Instantiation Options
% 2.90/1.06  
% 2.90/1.06  --instantiation_flag                    true
% 2.90/1.06  --inst_sos_flag                         true
% 2.90/1.06  --inst_sos_phase                        true
% 2.90/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.90/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.90/1.06  --inst_lit_sel_side                     none
% 2.90/1.06  --inst_solver_per_active                1400
% 2.90/1.06  --inst_solver_calls_frac                1.
% 2.90/1.06  --inst_passive_queue_type               priority_queues
% 2.90/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.90/1.06  --inst_passive_queues_freq              [25;2]
% 2.90/1.06  --inst_dismatching                      true
% 2.90/1.06  --inst_eager_unprocessed_to_passive     true
% 2.90/1.06  --inst_prop_sim_given                   true
% 2.90/1.06  --inst_prop_sim_new                     false
% 2.90/1.06  --inst_subs_new                         false
% 2.90/1.06  --inst_eq_res_simp                      false
% 2.90/1.06  --inst_subs_given                       false
% 2.90/1.06  --inst_orphan_elimination               true
% 2.90/1.06  --inst_learning_loop_flag               true
% 2.90/1.06  --inst_learning_start                   3000
% 2.90/1.06  --inst_learning_factor                  2
% 2.90/1.06  --inst_start_prop_sim_after_learn       3
% 2.90/1.06  --inst_sel_renew                        solver
% 2.90/1.06  --inst_lit_activity_flag                true
% 2.90/1.06  --inst_restr_to_given                   false
% 2.90/1.06  --inst_activity_threshold               500
% 2.90/1.06  --inst_out_proof                        true
% 2.90/1.06  
% 2.90/1.06  ------ Resolution Options
% 2.90/1.06  
% 2.90/1.06  --resolution_flag                       false
% 2.90/1.06  --res_lit_sel                           adaptive
% 2.90/1.06  --res_lit_sel_side                      none
% 2.90/1.06  --res_ordering                          kbo
% 2.90/1.06  --res_to_prop_solver                    active
% 2.90/1.06  --res_prop_simpl_new                    false
% 2.90/1.06  --res_prop_simpl_given                  true
% 2.90/1.06  --res_passive_queue_type                priority_queues
% 2.90/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.90/1.06  --res_passive_queues_freq               [15;5]
% 2.90/1.06  --res_forward_subs                      full
% 2.90/1.06  --res_backward_subs                     full
% 2.90/1.06  --res_forward_subs_resolution           true
% 2.90/1.06  --res_backward_subs_resolution          true
% 2.90/1.06  --res_orphan_elimination                true
% 2.90/1.06  --res_time_limit                        2.
% 2.90/1.06  --res_out_proof                         true
% 2.90/1.06  
% 2.90/1.06  ------ Superposition Options
% 2.90/1.06  
% 2.90/1.06  --superposition_flag                    true
% 2.90/1.06  --sup_passive_queue_type                priority_queues
% 2.90/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.90/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.90/1.06  --demod_completeness_check              fast
% 2.90/1.06  --demod_use_ground                      true
% 2.90/1.06  --sup_to_prop_solver                    passive
% 2.90/1.06  --sup_prop_simpl_new                    true
% 2.90/1.06  --sup_prop_simpl_given                  true
% 2.90/1.06  --sup_fun_splitting                     true
% 2.90/1.06  --sup_smt_interval                      50000
% 2.90/1.06  
% 2.90/1.06  ------ Superposition Simplification Setup
% 2.90/1.06  
% 2.90/1.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.90/1.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.90/1.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.90/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.90/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.90/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.90/1.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.90/1.06  --sup_immed_triv                        [TrivRules]
% 2.90/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/1.06  --sup_immed_bw_main                     []
% 2.90/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.90/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.90/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/1.06  --sup_input_bw                          []
% 2.90/1.06  
% 2.90/1.06  ------ Combination Options
% 2.90/1.06  
% 2.90/1.06  --comb_res_mult                         3
% 2.90/1.06  --comb_sup_mult                         2
% 2.90/1.06  --comb_inst_mult                        10
% 2.90/1.06  
% 2.90/1.06  ------ Debug Options
% 2.90/1.06  
% 2.90/1.06  --dbg_backtrace                         false
% 2.90/1.06  --dbg_dump_prop_clauses                 false
% 2.90/1.06  --dbg_dump_prop_clauses_file            -
% 2.90/1.06  --dbg_out_stat                          false
% 2.90/1.06  
% 2.90/1.06  
% 2.90/1.06  
% 2.90/1.06  
% 2.90/1.06  ------ Proving...
% 2.90/1.06  
% 2.90/1.06  
% 2.90/1.06  % SZS status Theorem for theBenchmark.p
% 2.90/1.06  
% 2.90/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 2.90/1.06  
% 2.90/1.06  fof(f15,conjecture,(
% 2.90/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 2.90/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.06  
% 2.90/1.06  fof(f16,negated_conjecture,(
% 2.90/1.06    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 2.90/1.06    inference(negated_conjecture,[],[f15])).
% 2.90/1.06  
% 2.90/1.06  fof(f39,plain,(
% 2.90/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : ((k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1)))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.90/1.06    inference(ennf_transformation,[],[f16])).
% 2.90/1.06  
% 2.90/1.06  fof(f40,plain,(
% 2.90/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.90/1.06    inference(flattening,[],[f39])).
% 2.90/1.06  
% 2.90/1.06  fof(f49,plain,(
% 2.90/1.06    ( ! [X2,X0,X3,X1] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK5) & ! [X5] : (k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 2.90/1.06    introduced(choice_axiom,[])).
% 2.90/1.06  
% 2.90/1.06  fof(f48,plain,(
% 2.90/1.06    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK4,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),sK4,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 2.90/1.06    introduced(choice_axiom,[])).
% 2.90/1.06  
% 2.90/1.06  fof(f47,plain,(
% 2.90/1.06    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK3),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK3,X1) & ~v2_struct_0(sK3))) )),
% 2.90/1.06    introduced(choice_axiom,[])).
% 2.90/1.06  
% 2.90/1.06  fof(f46,plain,(
% 2.90/1.06    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK2,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.90/1.06    introduced(choice_axiom,[])).
% 2.90/1.06  
% 2.90/1.06  fof(f45,plain,(
% 2.90/1.06    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X1,sK1,X3,X2),X4) & ! [X5] : (k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK1),X3,X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.90/1.06    introduced(choice_axiom,[])).
% 2.90/1.06  
% 2.90/1.06  fof(f50,plain,(
% 2.90/1.06    ((((~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5) & ! [X5] : (k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X5) | ~r2_hidden(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.90/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f40,f49,f48,f47,f46,f45])).
% 2.90/1.06  
% 2.90/1.06  fof(f79,plain,(
% 2.90/1.06    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f12,axiom,(
% 2.90/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 2.90/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.06  
% 2.90/1.06  fof(f34,plain,(
% 2.90/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.90/1.06    inference(ennf_transformation,[],[f12])).
% 2.90/1.06  
% 2.90/1.06  fof(f35,plain,(
% 2.90/1.06    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.90/1.06    inference(flattening,[],[f34])).
% 2.90/1.06  
% 2.90/1.06  fof(f64,plain,(
% 2.90/1.06    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f35])).
% 2.90/1.06  
% 2.90/1.06  fof(f76,plain,(
% 2.90/1.06    m1_pre_topc(sK3,sK2)),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f72,plain,(
% 2.90/1.06    ~v2_struct_0(sK2)),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f73,plain,(
% 2.90/1.06    v2_pre_topc(sK2)),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f74,plain,(
% 2.90/1.06    l1_pre_topc(sK2)),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f70,plain,(
% 2.90/1.06    v2_pre_topc(sK1)),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f69,plain,(
% 2.90/1.06    ~v2_struct_0(sK1)),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f71,plain,(
% 2.90/1.06    l1_pre_topc(sK1)),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f7,axiom,(
% 2.90/1.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 2.90/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.06  
% 2.90/1.06  fof(f26,plain,(
% 2.90/1.06    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.90/1.06    inference(ennf_transformation,[],[f7])).
% 2.90/1.06  
% 2.90/1.06  fof(f27,plain,(
% 2.90/1.06    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.90/1.06    inference(flattening,[],[f26])).
% 2.90/1.06  
% 2.90/1.06  fof(f59,plain,(
% 2.90/1.06    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f27])).
% 2.90/1.06  
% 2.90/1.06  fof(f77,plain,(
% 2.90/1.06    v1_funct_1(sK4)),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f78,plain,(
% 2.90/1.06    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f6,axiom,(
% 2.90/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)))))),
% 2.90/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.06  
% 2.90/1.06  fof(f24,plain,(
% 2.90/1.06    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.90/1.06    inference(ennf_transformation,[],[f6])).
% 2.90/1.06  
% 2.90/1.06  fof(f25,plain,(
% 2.90/1.06    ! [X0,X1,X2] : (! [X3] : ((r2_funct_2(X0,X1,X2,X3) <=> ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.90/1.06    inference(flattening,[],[f24])).
% 2.90/1.06  
% 2.90/1.06  fof(f41,plain,(
% 2.90/1.06    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.90/1.06    inference(nnf_transformation,[],[f25])).
% 2.90/1.06  
% 2.90/1.06  fof(f42,plain,(
% 2.90/1.06    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.90/1.06    inference(rectify,[],[f41])).
% 2.90/1.06  
% 2.90/1.06  fof(f43,plain,(
% 2.90/1.06    ! [X3,X2,X0] : (? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & m1_subset_1(X4,X0)) => (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0)))),
% 2.90/1.06    introduced(choice_axiom,[])).
% 2.90/1.06  
% 2.90/1.06  fof(f44,plain,(
% 2.90/1.06    ! [X0,X1,X2] : (! [X3] : (((r2_funct_2(X0,X1,X2,X3) | (k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) & m1_subset_1(sK0(X0,X2,X3),X0))) & (! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X3,X5) | ~m1_subset_1(X5,X0)) | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.90/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 2.90/1.06  
% 2.90/1.06  fof(f57,plain,(
% 2.90/1.06    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | m1_subset_1(sK0(X0,X2,X3),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f44])).
% 2.90/1.06  
% 2.90/1.06  fof(f84,plain,(
% 2.90/1.06    ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f80,plain,(
% 2.90/1.06    v1_funct_1(sK5)),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f81,plain,(
% 2.90/1.06    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f82,plain,(
% 2.90/1.06    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f9,axiom,(
% 2.90/1.06    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.90/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.06  
% 2.90/1.06  fof(f30,plain,(
% 2.90/1.06    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.90/1.06    inference(ennf_transformation,[],[f9])).
% 2.90/1.06  
% 2.90/1.06  fof(f61,plain,(
% 2.90/1.06    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f30])).
% 2.90/1.06  
% 2.90/1.06  fof(f10,axiom,(
% 2.90/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.90/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.06  
% 2.90/1.06  fof(f31,plain,(
% 2.90/1.06    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.90/1.06    inference(ennf_transformation,[],[f10])).
% 2.90/1.06  
% 2.90/1.06  fof(f62,plain,(
% 2.90/1.06    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f31])).
% 2.90/1.06  
% 2.90/1.06  fof(f13,axiom,(
% 2.90/1.06    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 2.90/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.06  
% 2.90/1.06  fof(f36,plain,(
% 2.90/1.06    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.90/1.06    inference(ennf_transformation,[],[f13])).
% 2.90/1.06  
% 2.90/1.06  fof(f37,plain,(
% 2.90/1.06    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.90/1.06    inference(flattening,[],[f36])).
% 2.90/1.06  
% 2.90/1.06  fof(f65,plain,(
% 2.90/1.06    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f37])).
% 2.90/1.06  
% 2.90/1.06  fof(f66,plain,(
% 2.90/1.06    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f37])).
% 2.90/1.06  
% 2.90/1.06  fof(f67,plain,(
% 2.90/1.06    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f37])).
% 2.90/1.06  
% 2.90/1.06  fof(f1,axiom,(
% 2.90/1.06    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.90/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.06  
% 2.90/1.06  fof(f17,plain,(
% 2.90/1.06    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.90/1.06    inference(ennf_transformation,[],[f1])).
% 2.90/1.06  
% 2.90/1.06  fof(f18,plain,(
% 2.90/1.06    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.90/1.06    inference(flattening,[],[f17])).
% 2.90/1.06  
% 2.90/1.06  fof(f51,plain,(
% 2.90/1.06    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f18])).
% 2.90/1.06  
% 2.90/1.06  fof(f11,axiom,(
% 2.90/1.06    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.90/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.06  
% 2.90/1.06  fof(f32,plain,(
% 2.90/1.06    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.90/1.06    inference(ennf_transformation,[],[f11])).
% 2.90/1.06  
% 2.90/1.06  fof(f33,plain,(
% 2.90/1.06    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.90/1.06    inference(flattening,[],[f32])).
% 2.90/1.06  
% 2.90/1.06  fof(f63,plain,(
% 2.90/1.06    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f33])).
% 2.90/1.06  
% 2.90/1.06  fof(f75,plain,(
% 2.90/1.06    ~v2_struct_0(sK3)),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f14,axiom,(
% 2.90/1.06    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.90/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.06  
% 2.90/1.06  fof(f38,plain,(
% 2.90/1.06    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.90/1.06    inference(ennf_transformation,[],[f14])).
% 2.90/1.06  
% 2.90/1.06  fof(f68,plain,(
% 2.90/1.06    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f38])).
% 2.90/1.06  
% 2.90/1.06  fof(f2,axiom,(
% 2.90/1.06    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.90/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.06  
% 2.90/1.06  fof(f19,plain,(
% 2.90/1.06    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.90/1.06    inference(ennf_transformation,[],[f2])).
% 2.90/1.06  
% 2.90/1.06  fof(f20,plain,(
% 2.90/1.06    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.90/1.06    inference(flattening,[],[f19])).
% 2.90/1.06  
% 2.90/1.06  fof(f52,plain,(
% 2.90/1.06    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f20])).
% 2.90/1.06  
% 2.90/1.06  fof(f8,axiom,(
% 2.90/1.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 2.90/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.06  
% 2.90/1.06  fof(f28,plain,(
% 2.90/1.06    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 2.90/1.06    inference(ennf_transformation,[],[f8])).
% 2.90/1.06  
% 2.90/1.06  fof(f29,plain,(
% 2.90/1.06    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 2.90/1.06    inference(flattening,[],[f28])).
% 2.90/1.06  
% 2.90/1.06  fof(f60,plain,(
% 2.90/1.06    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f29])).
% 2.90/1.06  
% 2.90/1.06  fof(f83,plain,(
% 2.90/1.06    ( ! [X5] : (k1_funct_1(sK5,X5) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X5) | ~r2_hidden(X5,u1_struct_0(sK3)) | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 2.90/1.06    inference(cnf_transformation,[],[f50])).
% 2.90/1.06  
% 2.90/1.06  fof(f5,axiom,(
% 2.90/1.06    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,X1) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 2.90/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.06  
% 2.90/1.06  fof(f22,plain,(
% 2.90/1.06    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.90/1.06    inference(ennf_transformation,[],[f5])).
% 2.90/1.06  
% 2.90/1.06  fof(f23,plain,(
% 2.90/1.06    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.90/1.06    inference(flattening,[],[f22])).
% 2.90/1.06  
% 2.90/1.06  fof(f55,plain,(
% 2.90/1.06    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) | ~r2_hidden(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f23])).
% 2.90/1.06  
% 2.90/1.06  fof(f4,axiom,(
% 2.90/1.06    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.90/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.06  
% 2.90/1.06  fof(f54,plain,(
% 2.90/1.06    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.90/1.06    inference(cnf_transformation,[],[f4])).
% 2.90/1.06  
% 2.90/1.06  fof(f3,axiom,(
% 2.90/1.06    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.90/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.06  
% 2.90/1.06  fof(f21,plain,(
% 2.90/1.06    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.90/1.06    inference(ennf_transformation,[],[f3])).
% 2.90/1.06  
% 2.90/1.06  fof(f53,plain,(
% 2.90/1.06    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f21])).
% 2.90/1.06  
% 2.90/1.06  fof(f58,plain,(
% 2.90/1.06    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | k1_funct_1(X2,sK0(X0,X2,X3)) != k1_funct_1(X3,sK0(X0,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.90/1.06    inference(cnf_transformation,[],[f44])).
% 2.90/1.06  
% 2.90/1.06  cnf(c_23,negated_conjecture,
% 2.90/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 2.90/1.06      inference(cnf_transformation,[],[f79]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1316,negated_conjecture,
% 2.90/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_23]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1887,plain,
% 2.90/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_1316]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_13,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.90/1.06      | ~ m1_pre_topc(X3,X1)
% 2.90/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.90/1.06      | ~ v2_pre_topc(X2)
% 2.90/1.06      | ~ v2_pre_topc(X1)
% 2.90/1.06      | v2_struct_0(X1)
% 2.90/1.06      | v2_struct_0(X2)
% 2.90/1.06      | ~ l1_pre_topc(X1)
% 2.90/1.06      | ~ l1_pre_topc(X2)
% 2.90/1.06      | ~ v1_funct_1(X0)
% 2.90/1.06      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 2.90/1.06      inference(cnf_transformation,[],[f64]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_26,negated_conjecture,
% 2.90/1.06      ( m1_pre_topc(sK3,sK2) ),
% 2.90/1.06      inference(cnf_transformation,[],[f76]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_507,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.90/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.90/1.06      | ~ v2_pre_topc(X1)
% 2.90/1.06      | ~ v2_pre_topc(X2)
% 2.90/1.06      | v2_struct_0(X1)
% 2.90/1.06      | v2_struct_0(X2)
% 2.90/1.06      | ~ l1_pre_topc(X1)
% 2.90/1.06      | ~ l1_pre_topc(X2)
% 2.90/1.06      | ~ v1_funct_1(X0)
% 2.90/1.06      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 2.90/1.06      | sK2 != X1
% 2.90/1.06      | sK3 != X3 ),
% 2.90/1.06      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_508,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 2.90/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.90/1.06      | ~ v2_pre_topc(X1)
% 2.90/1.06      | ~ v2_pre_topc(sK2)
% 2.90/1.06      | v2_struct_0(X1)
% 2.90/1.06      | v2_struct_0(sK2)
% 2.90/1.06      | ~ l1_pre_topc(X1)
% 2.90/1.06      | ~ l1_pre_topc(sK2)
% 2.90/1.06      | ~ v1_funct_1(X0)
% 2.90/1.06      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
% 2.90/1.06      inference(unflattening,[status(thm)],[c_507]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_30,negated_conjecture,
% 2.90/1.06      ( ~ v2_struct_0(sK2) ),
% 2.90/1.06      inference(cnf_transformation,[],[f72]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_29,negated_conjecture,
% 2.90/1.06      ( v2_pre_topc(sK2) ),
% 2.90/1.06      inference(cnf_transformation,[],[f73]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_28,negated_conjecture,
% 2.90/1.06      ( l1_pre_topc(sK2) ),
% 2.90/1.06      inference(cnf_transformation,[],[f74]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_512,plain,
% 2.90/1.06      ( ~ l1_pre_topc(X1)
% 2.90/1.06      | ~ v2_pre_topc(X1)
% 2.90/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.90/1.06      | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 2.90/1.06      | v2_struct_0(X1)
% 2.90/1.06      | ~ v1_funct_1(X0)
% 2.90/1.06      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
% 2.90/1.06      inference(global_propositional_subsumption,
% 2.90/1.06                [status(thm)],
% 2.90/1.06                [c_508,c_30,c_29,c_28]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_513,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 2.90/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.90/1.06      | ~ v2_pre_topc(X1)
% 2.90/1.06      | v2_struct_0(X1)
% 2.90/1.06      | ~ l1_pre_topc(X1)
% 2.90/1.06      | ~ v1_funct_1(X0)
% 2.90/1.06      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
% 2.90/1.06      inference(renaming,[status(thm)],[c_512]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_32,negated_conjecture,
% 2.90/1.06      ( v2_pre_topc(sK1) ),
% 2.90/1.06      inference(cnf_transformation,[],[f70]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_576,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
% 2.90/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
% 2.90/1.06      | v2_struct_0(X1)
% 2.90/1.06      | ~ l1_pre_topc(X1)
% 2.90/1.06      | ~ v1_funct_1(X0)
% 2.90/1.06      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3)
% 2.90/1.06      | sK1 != X1 ),
% 2.90/1.06      inference(resolution_lifted,[status(thm)],[c_513,c_32]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_577,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
% 2.90/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.90/1.06      | v2_struct_0(sK1)
% 2.90/1.06      | ~ l1_pre_topc(sK1)
% 2.90/1.06      | ~ v1_funct_1(X0)
% 2.90/1.06      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0,sK3) ),
% 2.90/1.06      inference(unflattening,[status(thm)],[c_576]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_33,negated_conjecture,
% 2.90/1.06      ( ~ v2_struct_0(sK1) ),
% 2.90/1.06      inference(cnf_transformation,[],[f69]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_31,negated_conjecture,
% 2.90/1.06      ( l1_pre_topc(sK1) ),
% 2.90/1.06      inference(cnf_transformation,[],[f71]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_581,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
% 2.90/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.90/1.06      | ~ v1_funct_1(X0)
% 2.90/1.06      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0,sK3) ),
% 2.90/1.06      inference(global_propositional_subsumption,
% 2.90/1.06                [status(thm)],
% 2.90/1.06                [c_577,c_33,c_31]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1311,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1))
% 2.90/1.06      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.90/1.06      | ~ v1_funct_1(X0_54)
% 2.90/1.06      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0_54,sK3) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_581]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1892,plain,
% 2.90/1.06      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_54,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0_54,sK3)
% 2.90/1.06      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.90/1.06      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.90/1.06      | v1_funct_1(X0_54) != iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_1311]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_2841,plain,
% 2.90/1.06      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK4,sK3)
% 2.90/1.06      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.90/1.06      | v1_funct_1(sK4) != iProver_top ),
% 2.90/1.06      inference(superposition,[status(thm)],[c_1887,c_1892]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_8,plain,
% 2.90/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.06      | ~ v1_funct_1(X0)
% 2.90/1.06      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.90/1.06      inference(cnf_transformation,[],[f59]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1325,plain,
% 2.90/1.06      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 2.90/1.06      | ~ v1_funct_1(X0_54)
% 2.90/1.06      | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_8]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1878,plain,
% 2.90/1.06      ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
% 2.90/1.06      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.90/1.06      | v1_funct_1(X2_54) != iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_1325]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_2302,plain,
% 2.90/1.06      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54)
% 2.90/1.06      | v1_funct_1(sK4) != iProver_top ),
% 2.90/1.06      inference(superposition,[status(thm)],[c_1887,c_1878]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_25,negated_conjecture,
% 2.90/1.06      ( v1_funct_1(sK4) ),
% 2.90/1.06      inference(cnf_transformation,[],[f77]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_42,plain,
% 2.90/1.06      ( v1_funct_1(sK4) = iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_2767,plain,
% 2.90/1.06      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 2.90/1.06      inference(global_propositional_subsumption,
% 2.90/1.06                [status(thm)],
% 2.90/1.06                [c_2302,c_42]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_2843,plain,
% 2.90/1.06      ( k2_tmap_1(sK2,sK1,sK4,sK3) = k7_relat_1(sK4,u1_struct_0(sK3))
% 2.90/1.06      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.90/1.06      | v1_funct_1(sK4) != iProver_top ),
% 2.90/1.06      inference(demodulation,[status(thm)],[c_2841,c_2767]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_24,negated_conjecture,
% 2.90/1.06      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 2.90/1.06      inference(cnf_transformation,[],[f78]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_43,plain,
% 2.90/1.06      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_3339,plain,
% 2.90/1.06      ( k2_tmap_1(sK2,sK1,sK4,sK3) = k7_relat_1(sK4,u1_struct_0(sK3)) ),
% 2.90/1.06      inference(global_propositional_subsumption,
% 2.90/1.06                [status(thm)],
% 2.90/1.06                [c_2843,c_42,c_43]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_6,plain,
% 2.90/1.06      ( r2_funct_2(X0,X1,X2,X3)
% 2.90/1.06      | ~ v1_funct_2(X3,X0,X1)
% 2.90/1.06      | ~ v1_funct_2(X2,X0,X1)
% 2.90/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.90/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.90/1.06      | m1_subset_1(sK0(X0,X2,X3),X0)
% 2.90/1.06      | ~ v1_funct_1(X2)
% 2.90/1.06      | ~ v1_funct_1(X3) ),
% 2.90/1.06      inference(cnf_transformation,[],[f57]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_18,negated_conjecture,
% 2.90/1.06      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5) ),
% 2.90/1.06      inference(cnf_transformation,[],[f84]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_860,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 2.90/1.06      | ~ v1_funct_2(X3,X1,X2)
% 2.90/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.06      | m1_subset_1(sK0(X1,X3,X0),X1)
% 2.90/1.06      | ~ v1_funct_1(X3)
% 2.90/1.06      | ~ v1_funct_1(X0)
% 2.90/1.06      | k2_tmap_1(sK2,sK1,sK4,sK3) != X3
% 2.90/1.06      | u1_struct_0(sK1) != X2
% 2.90/1.06      | u1_struct_0(sK3) != X1
% 2.90/1.06      | sK5 != X0 ),
% 2.90/1.06      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_861,plain,
% 2.90/1.06      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 2.90/1.06      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 2.90/1.06      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.90/1.06      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
% 2.90/1.06      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.90/1.06      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 2.90/1.06      | ~ v1_funct_1(sK5) ),
% 2.90/1.06      inference(unflattening,[status(thm)],[c_860]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_22,negated_conjecture,
% 2.90/1.06      ( v1_funct_1(sK5) ),
% 2.90/1.06      inference(cnf_transformation,[],[f80]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_21,negated_conjecture,
% 2.90/1.06      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
% 2.90/1.06      inference(cnf_transformation,[],[f81]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_20,negated_conjecture,
% 2.90/1.06      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
% 2.90/1.06      inference(cnf_transformation,[],[f82]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_863,plain,
% 2.90/1.06      ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 2.90/1.06      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 2.90/1.06      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.90/1.06      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) ),
% 2.90/1.06      inference(global_propositional_subsumption,
% 2.90/1.06                [status(thm)],
% 2.90/1.06                [c_861,c_22,c_21,c_20]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_864,plain,
% 2.90/1.06      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 2.90/1.06      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.90/1.06      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
% 2.90/1.06      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) ),
% 2.90/1.06      inference(renaming,[status(thm)],[c_863]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1302,plain,
% 2.90/1.06      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 2.90/1.06      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.90/1.06      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3))
% 2.90/1.06      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_864]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1901,plain,
% 2.90/1.06      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.90/1.06      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.90/1.06      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top
% 2.90/1.06      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_1302]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_36,plain,
% 2.90/1.06      ( l1_pre_topc(sK1) = iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_44,plain,
% 2.90/1.06      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_10,plain,
% 2.90/1.06      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.90/1.06      inference(cnf_transformation,[],[f61]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_71,plain,
% 2.90/1.06      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_73,plain,
% 2.90/1.06      ( l1_pre_topc(sK1) != iProver_top
% 2.90/1.06      | l1_struct_0(sK1) = iProver_top ),
% 2.90/1.06      inference(instantiation,[status(thm)],[c_71]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_610,plain,
% 2.90/1.06      ( l1_struct_0(X0) | sK2 != X0 ),
% 2.90/1.06      inference(resolution_lifted,[status(thm)],[c_10,c_28]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_611,plain,
% 2.90/1.06      ( l1_struct_0(sK2) ),
% 2.90/1.06      inference(unflattening,[status(thm)],[c_610]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_612,plain,
% 2.90/1.06      ( l1_struct_0(sK2) = iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_11,plain,
% 2.90/1.06      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.90/1.06      inference(cnf_transformation,[],[f62]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_496,plain,
% 2.90/1.06      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X0 | sK3 != X1 ),
% 2.90/1.06      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_497,plain,
% 2.90/1.06      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK3) ),
% 2.90/1.06      inference(unflattening,[status(thm)],[c_496]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_499,plain,
% 2.90/1.06      ( l1_pre_topc(sK3) ),
% 2.90/1.06      inference(global_propositional_subsumption,
% 2.90/1.06                [status(thm)],
% 2.90/1.06                [c_497,c_28]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_624,plain,
% 2.90/1.06      ( l1_struct_0(X0) | sK3 != X0 ),
% 2.90/1.06      inference(resolution_lifted,[status(thm)],[c_10,c_499]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_625,plain,
% 2.90/1.06      ( l1_struct_0(sK3) ),
% 2.90/1.06      inference(unflattening,[status(thm)],[c_624]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_626,plain,
% 2.90/1.06      ( l1_struct_0(sK3) = iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_865,plain,
% 2.90/1.06      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.90/1.06      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.90/1.06      | m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top
% 2.90/1.06      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_864]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_16,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.90/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.90/1.06      | ~ l1_struct_0(X1)
% 2.90/1.06      | ~ l1_struct_0(X3)
% 2.90/1.06      | ~ l1_struct_0(X2)
% 2.90/1.06      | ~ v1_funct_1(X0)
% 2.90/1.06      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 2.90/1.06      inference(cnf_transformation,[],[f65]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1321,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 2.90/1.06      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 2.90/1.06      | ~ l1_struct_0(X1_55)
% 2.90/1.06      | ~ l1_struct_0(X2_55)
% 2.90/1.06      | ~ l1_struct_0(X0_55)
% 2.90/1.06      | ~ v1_funct_1(X0_54)
% 2.90/1.06      | v1_funct_1(k2_tmap_1(X0_55,X1_55,X0_54,X2_55)) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_16]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1961,plain,
% 2.90/1.06      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
% 2.90/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.90/1.06      | ~ l1_struct_0(sK2)
% 2.90/1.06      | ~ l1_struct_0(sK1)
% 2.90/1.06      | ~ l1_struct_0(sK3)
% 2.90/1.06      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 2.90/1.06      | ~ v1_funct_1(sK4) ),
% 2.90/1.06      inference(instantiation,[status(thm)],[c_1321]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1962,plain,
% 2.90/1.06      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.90/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.90/1.06      | l1_struct_0(sK2) != iProver_top
% 2.90/1.06      | l1_struct_0(sK1) != iProver_top
% 2.90/1.06      | l1_struct_0(sK3) != iProver_top
% 2.90/1.06      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) = iProver_top
% 2.90/1.06      | v1_funct_1(sK4) != iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_1961]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_15,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.90/1.06      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 2.90/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.90/1.06      | ~ l1_struct_0(X1)
% 2.90/1.06      | ~ l1_struct_0(X3)
% 2.90/1.06      | ~ l1_struct_0(X2)
% 2.90/1.06      | ~ v1_funct_1(X0) ),
% 2.90/1.06      inference(cnf_transformation,[],[f66]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1322,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 2.90/1.06      | v1_funct_2(k2_tmap_1(X0_55,X1_55,X0_54,X2_55),u1_struct_0(X2_55),u1_struct_0(X1_55))
% 2.90/1.06      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 2.90/1.06      | ~ l1_struct_0(X1_55)
% 2.90/1.06      | ~ l1_struct_0(X2_55)
% 2.90/1.06      | ~ l1_struct_0(X0_55)
% 2.90/1.06      | ~ v1_funct_1(X0_54) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_15]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_2028,plain,
% 2.90/1.06      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 2.90/1.06      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
% 2.90/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.90/1.06      | ~ l1_struct_0(sK2)
% 2.90/1.06      | ~ l1_struct_0(sK1)
% 2.90/1.06      | ~ l1_struct_0(sK3)
% 2.90/1.06      | ~ v1_funct_1(sK4) ),
% 2.90/1.06      inference(instantiation,[status(thm)],[c_1322]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_2029,plain,
% 2.90/1.06      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 2.90/1.06      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.90/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.90/1.06      | l1_struct_0(sK2) != iProver_top
% 2.90/1.06      | l1_struct_0(sK1) != iProver_top
% 2.90/1.06      | l1_struct_0(sK3) != iProver_top
% 2.90/1.06      | v1_funct_1(sK4) != iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_2028]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_14,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.90/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.90/1.06      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 2.90/1.06      | ~ l1_struct_0(X1)
% 2.90/1.06      | ~ l1_struct_0(X3)
% 2.90/1.06      | ~ l1_struct_0(X2)
% 2.90/1.06      | ~ v1_funct_1(X0) ),
% 2.90/1.06      inference(cnf_transformation,[],[f67]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1323,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 2.90/1.06      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 2.90/1.06      | m1_subset_1(k2_tmap_1(X0_55,X1_55,X0_54,X2_55),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 2.90/1.06      | ~ l1_struct_0(X1_55)
% 2.90/1.06      | ~ l1_struct_0(X2_55)
% 2.90/1.06      | ~ l1_struct_0(X0_55)
% 2.90/1.06      | ~ v1_funct_1(X0_54) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_14]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_2057,plain,
% 2.90/1.06      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
% 2.90/1.06      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.90/1.06      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.90/1.06      | ~ l1_struct_0(sK2)
% 2.90/1.06      | ~ l1_struct_0(sK1)
% 2.90/1.06      | ~ l1_struct_0(sK3)
% 2.90/1.06      | ~ v1_funct_1(sK4) ),
% 2.90/1.06      inference(instantiation,[status(thm)],[c_1323]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_2058,plain,
% 2.90/1.06      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.90/1.06      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 2.90/1.06      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 2.90/1.06      | l1_struct_0(sK2) != iProver_top
% 2.90/1.06      | l1_struct_0(sK1) != iProver_top
% 2.90/1.06      | l1_struct_0(sK3) != iProver_top
% 2.90/1.06      | v1_funct_1(sK4) != iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_2057]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_2900,plain,
% 2.90/1.06      ( m1_subset_1(sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5),u1_struct_0(sK3)) = iProver_top ),
% 2.90/1.06      inference(global_propositional_subsumption,
% 2.90/1.06                [status(thm)],
% 2.90/1.06                [c_1901,c_36,c_42,c_43,c_44,c_73,c_612,c_626,c_865,
% 2.90/1.06                 c_1962,c_2029,c_2058]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_3342,plain,
% 2.90/1.06      ( m1_subset_1(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK3)) = iProver_top ),
% 2.90/1.06      inference(demodulation,[status(thm)],[c_3339,c_2900]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_0,plain,
% 2.90/1.06      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.90/1.06      inference(cnf_transformation,[],[f51]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1330,plain,
% 2.90/1.06      ( ~ m1_subset_1(X0_54,X1_54)
% 2.90/1.06      | r2_hidden(X0_54,X1_54)
% 2.90/1.06      | v1_xboole_0(X1_54) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_0]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1873,plain,
% 2.90/1.06      ( m1_subset_1(X0_54,X1_54) != iProver_top
% 2.90/1.06      | r2_hidden(X0_54,X1_54) = iProver_top
% 2.90/1.06      | v1_xboole_0(X1_54) = iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_1330]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_3351,plain,
% 2.90/1.06      ( r2_hidden(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK3)) = iProver_top
% 2.90/1.06      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.90/1.06      inference(superposition,[status(thm)],[c_3342,c_1873]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_12,plain,
% 2.90/1.06      ( v2_struct_0(X0)
% 2.90/1.06      | ~ l1_struct_0(X0)
% 2.90/1.06      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.90/1.06      inference(cnf_transformation,[],[f63]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_27,negated_conjecture,
% 2.90/1.06      ( ~ v2_struct_0(sK3) ),
% 2.90/1.06      inference(cnf_transformation,[],[f75]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_637,plain,
% 2.90/1.06      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK3 != X0 ),
% 2.90/1.06      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_638,plain,
% 2.90/1.06      ( ~ l1_struct_0(sK3) | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.90/1.06      inference(unflattening,[status(thm)],[c_637]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_639,plain,
% 2.90/1.06      ( l1_struct_0(sK3) != iProver_top
% 2.90/1.06      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_3507,plain,
% 2.90/1.06      ( r2_hidden(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK3)) = iProver_top ),
% 2.90/1.06      inference(global_propositional_subsumption,
% 2.90/1.06                [status(thm)],
% 2.90/1.06                [c_3351,c_626,c_639]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_17,plain,
% 2.90/1.06      ( ~ m1_pre_topc(X0,X1)
% 2.90/1.06      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.90/1.06      | ~ l1_pre_topc(X1) ),
% 2.90/1.06      inference(cnf_transformation,[],[f68]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_485,plain,
% 2.90/1.06      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.90/1.06      | ~ l1_pre_topc(X1)
% 2.90/1.06      | sK2 != X1
% 2.90/1.06      | sK3 != X0 ),
% 2.90/1.06      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_486,plain,
% 2.90/1.06      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.90/1.06      | ~ l1_pre_topc(sK2) ),
% 2.90/1.06      inference(unflattening,[status(thm)],[c_485]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_488,plain,
% 2.90/1.06      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.90/1.06      inference(global_propositional_subsumption,
% 2.90/1.06                [status(thm)],
% 2.90/1.06                [c_486,c_28]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1313,plain,
% 2.90/1.06      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_488]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1890,plain,
% 2.90/1.06      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_1313]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1,plain,
% 2.90/1.06      ( m1_subset_1(X0,X1)
% 2.90/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.90/1.06      | ~ r2_hidden(X0,X2) ),
% 2.90/1.06      inference(cnf_transformation,[],[f52]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1329,plain,
% 2.90/1.06      ( m1_subset_1(X0_54,X1_54)
% 2.90/1.06      | ~ m1_subset_1(X2_54,k1_zfmisc_1(X1_54))
% 2.90/1.06      | ~ r2_hidden(X0_54,X2_54) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_1]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1874,plain,
% 2.90/1.06      ( m1_subset_1(X0_54,X1_54) = iProver_top
% 2.90/1.06      | m1_subset_1(X2_54,k1_zfmisc_1(X1_54)) != iProver_top
% 2.90/1.06      | r2_hidden(X0_54,X2_54) != iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_1329]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_2441,plain,
% 2.90/1.06      ( m1_subset_1(X0_54,u1_struct_0(sK2)) = iProver_top
% 2.90/1.06      | r2_hidden(X0_54,u1_struct_0(sK3)) != iProver_top ),
% 2.90/1.06      inference(superposition,[status(thm)],[c_1890,c_1874]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_3511,plain,
% 2.90/1.06      ( m1_subset_1(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK2)) = iProver_top ),
% 2.90/1.06      inference(superposition,[status(thm)],[c_3507,c_2441]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_9,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 2.90/1.06      | ~ m1_subset_1(X3,X1)
% 2.90/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.06      | ~ v1_funct_1(X0)
% 2.90/1.06      | v1_xboole_0(X1)
% 2.90/1.06      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.90/1.06      inference(cnf_transformation,[],[f60]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1324,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 2.90/1.06      | ~ m1_subset_1(X3_54,X1_54)
% 2.90/1.06      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 2.90/1.06      | ~ v1_funct_1(X0_54)
% 2.90/1.06      | v1_xboole_0(X1_54)
% 2.90/1.06      | k3_funct_2(X1_54,X2_54,X0_54,X3_54) = k1_funct_1(X0_54,X3_54) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_9]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1879,plain,
% 2.90/1.06      ( k3_funct_2(X0_54,X1_54,X2_54,X3_54) = k1_funct_1(X2_54,X3_54)
% 2.90/1.06      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 2.90/1.06      | m1_subset_1(X3_54,X0_54) != iProver_top
% 2.90/1.06      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.90/1.06      | v1_funct_1(X2_54) != iProver_top
% 2.90/1.06      | v1_xboole_0(X0_54) = iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_1324]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_2624,plain,
% 2.90/1.06      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK4,X0_54)
% 2.90/1.06      | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 2.90/1.06      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 2.90/1.06      | v1_funct_1(sK4) != iProver_top
% 2.90/1.06      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.90/1.06      inference(superposition,[status(thm)],[c_1887,c_1879]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_648,plain,
% 2.90/1.06      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 2.90/1.06      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_649,plain,
% 2.90/1.06      ( ~ l1_struct_0(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.90/1.06      inference(unflattening,[status(thm)],[c_648]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_650,plain,
% 2.90/1.06      ( l1_struct_0(sK2) != iProver_top
% 2.90/1.06      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_3238,plain,
% 2.90/1.06      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) = k1_funct_1(sK4,X0_54)
% 2.90/1.06      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 2.90/1.06      inference(global_propositional_subsumption,
% 2.90/1.06                [status(thm)],
% 2.90/1.06                [c_2624,c_42,c_43,c_612,c_650]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_5190,plain,
% 2.90/1.06      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
% 2.90/1.06      inference(superposition,[status(thm)],[c_3511,c_3238]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_19,negated_conjecture,
% 2.90/1.06      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.90/1.06      | ~ r2_hidden(X0,u1_struct_0(sK3))
% 2.90/1.06      | k1_funct_1(sK5,X0) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) ),
% 2.90/1.06      inference(cnf_transformation,[],[f83]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1320,negated_conjecture,
% 2.90/1.06      ( ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 2.90/1.06      | ~ r2_hidden(X0_54,u1_struct_0(sK3))
% 2.90/1.06      | k1_funct_1(sK5,X0_54) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_19]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1883,plain,
% 2.90/1.06      ( k1_funct_1(sK5,X0_54) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_54)
% 2.90/1.06      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 2.90/1.06      | r2_hidden(X0_54,u1_struct_0(sK3)) != iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_1320]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_5191,plain,
% 2.90/1.06      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
% 2.90/1.06      | r2_hidden(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK3)) != iProver_top ),
% 2.90/1.06      inference(superposition,[status(thm)],[c_3511,c_1883]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_5194,plain,
% 2.90/1.06      ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
% 2.90/1.06      | r2_hidden(sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5),u1_struct_0(sK3)) != iProver_top ),
% 2.90/1.06      inference(demodulation,[status(thm)],[c_5190,c_5191]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1314,negated_conjecture,
% 2.90/1.06      ( v1_funct_1(sK4) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_25]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1889,plain,
% 2.90/1.06      ( v1_funct_1(sK4) = iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_1314]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_4,plain,
% 2.90/1.06      ( ~ r2_hidden(X0,X1)
% 2.90/1.06      | ~ v1_funct_1(X2)
% 2.90/1.06      | ~ v1_relat_1(X2)
% 2.90/1.06      | k1_funct_1(k7_relat_1(X2,X1),X0) = k1_funct_1(X2,X0) ),
% 2.90/1.06      inference(cnf_transformation,[],[f55]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1326,plain,
% 2.90/1.06      ( ~ r2_hidden(X0_54,X1_54)
% 2.90/1.06      | ~ v1_funct_1(X2_54)
% 2.90/1.06      | ~ v1_relat_1(X2_54)
% 2.90/1.06      | k1_funct_1(k7_relat_1(X2_54,X1_54),X0_54) = k1_funct_1(X2_54,X0_54) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_4]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1877,plain,
% 2.90/1.06      ( k1_funct_1(k7_relat_1(X0_54,X1_54),X2_54) = k1_funct_1(X0_54,X2_54)
% 2.90/1.06      | r2_hidden(X2_54,X1_54) != iProver_top
% 2.90/1.06      | v1_funct_1(X0_54) != iProver_top
% 2.90/1.06      | v1_relat_1(X0_54) != iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_1326]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_3512,plain,
% 2.90/1.06      ( k1_funct_1(k7_relat_1(X0_54,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(X0_54,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
% 2.90/1.06      | v1_funct_1(X0_54) != iProver_top
% 2.90/1.06      | v1_relat_1(X0_54) != iProver_top ),
% 2.90/1.06      inference(superposition,[status(thm)],[c_3507,c_1877]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_4484,plain,
% 2.90/1.06      ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
% 2.90/1.06      | v1_relat_1(sK4) != iProver_top ),
% 2.90/1.06      inference(superposition,[status(thm)],[c_1889,c_3512]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_3,plain,
% 2.90/1.06      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.90/1.06      inference(cnf_transformation,[],[f54]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1327,plain,
% 2.90/1.06      ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_3]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1876,plain,
% 2.90/1.06      ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) = iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_1327]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_2,plain,
% 2.90/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.90/1.06      | ~ v1_relat_1(X1)
% 2.90/1.06      | v1_relat_1(X0) ),
% 2.90/1.06      inference(cnf_transformation,[],[f53]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1328,plain,
% 2.90/1.06      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 2.90/1.06      | ~ v1_relat_1(X1_54)
% 2.90/1.06      | v1_relat_1(X0_54) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_2]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1875,plain,
% 2.90/1.06      ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
% 2.90/1.06      | v1_relat_1(X1_54) != iProver_top
% 2.90/1.06      | v1_relat_1(X0_54) = iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_1328]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_2249,plain,
% 2.90/1.06      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) != iProver_top
% 2.90/1.06      | v1_relat_1(sK4) = iProver_top ),
% 2.90/1.06      inference(superposition,[status(thm)],[c_1887,c_1875]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_2526,plain,
% 2.90/1.06      ( v1_relat_1(sK4) = iProver_top ),
% 2.90/1.06      inference(superposition,[status(thm)],[c_1876,c_2249]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_3515,plain,
% 2.90/1.06      ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5))
% 2.90/1.06      | v1_funct_1(sK4) != iProver_top
% 2.90/1.06      | v1_relat_1(sK4) != iProver_top ),
% 2.90/1.06      inference(instantiation,[status(thm)],[c_3512]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_4550,plain,
% 2.90/1.06      ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
% 2.90/1.06      inference(global_propositional_subsumption,
% 2.90/1.06                [status(thm)],
% 2.90/1.06                [c_4484,c_42,c_2526,c_3515]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_5,plain,
% 2.90/1.06      ( r2_funct_2(X0,X1,X2,X3)
% 2.90/1.06      | ~ v1_funct_2(X3,X0,X1)
% 2.90/1.06      | ~ v1_funct_2(X2,X0,X1)
% 2.90/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.90/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.90/1.06      | ~ v1_funct_1(X2)
% 2.90/1.06      | ~ v1_funct_1(X3)
% 2.90/1.06      | k1_funct_1(X3,sK0(X0,X2,X3)) != k1_funct_1(X2,sK0(X0,X2,X3)) ),
% 2.90/1.06      inference(cnf_transformation,[],[f58]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_880,plain,
% 2.90/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 2.90/1.06      | ~ v1_funct_2(X3,X1,X2)
% 2.90/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.06      | ~ v1_funct_1(X3)
% 2.90/1.06      | ~ v1_funct_1(X0)
% 2.90/1.06      | k2_tmap_1(sK2,sK1,sK4,sK3) != X3
% 2.90/1.06      | k1_funct_1(X0,sK0(X1,X3,X0)) != k1_funct_1(X3,sK0(X1,X3,X0))
% 2.90/1.06      | u1_struct_0(sK1) != X2
% 2.90/1.06      | u1_struct_0(sK3) != X1
% 2.90/1.06      | sK5 != X0 ),
% 2.90/1.06      inference(resolution_lifted,[status(thm)],[c_5,c_18]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_881,plain,
% 2.90/1.06      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 2.90/1.06      | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
% 2.90/1.06      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.90/1.06      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.90/1.06      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 2.90/1.06      | ~ v1_funct_1(sK5)
% 2.90/1.06      | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 2.90/1.06      inference(unflattening,[status(thm)],[c_880]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_883,plain,
% 2.90/1.06      ( ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 2.90/1.06      | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 2.90/1.06      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.90/1.06      | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 2.90/1.06      inference(global_propositional_subsumption,
% 2.90/1.06                [status(thm)],
% 2.90/1.06                [c_881,c_22,c_21,c_20]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_884,plain,
% 2.90/1.06      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 2.90/1.06      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.90/1.06      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 2.90/1.06      | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 2.90/1.06      inference(renaming,[status(thm)],[c_883]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1301,plain,
% 2.90/1.06      ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 2.90/1.06      | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 2.90/1.06      | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
% 2.90/1.06      | k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 2.90/1.06      inference(subtyping,[status(esa)],[c_884]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_1902,plain,
% 2.90/1.06      ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5))
% 2.90/1.06      | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 2.90/1.06      | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 2.90/1.06      | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
% 2.90/1.06      inference(predicate_to_equality,[status(thm)],[c_1301]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_72,plain,
% 2.90/1.06      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.90/1.06      inference(instantiation,[status(thm)],[c_10]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_3120,plain,
% 2.90/1.06      ( k1_funct_1(sK5,sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) != k1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3),sK0(u1_struct_0(sK3),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)) ),
% 2.90/1.06      inference(global_propositional_subsumption,
% 2.90/1.06                [status(thm)],
% 2.90/1.06                [c_1902,c_31,c_25,c_24,c_23,c_72,c_611,c_625,c_1301,
% 2.90/1.06                 c_1961,c_2028,c_2057]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_3341,plain,
% 2.90/1.06      ( k1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3)),sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) != k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
% 2.90/1.06      inference(demodulation,[status(thm)],[c_3339,c_3120]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(c_4552,plain,
% 2.90/1.06      ( k1_funct_1(sK4,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) != k1_funct_1(sK5,sK0(u1_struct_0(sK3),k7_relat_1(sK4,u1_struct_0(sK3)),sK5)) ),
% 2.90/1.06      inference(demodulation,[status(thm)],[c_4550,c_3341]) ).
% 2.90/1.06  
% 2.90/1.06  cnf(contradiction,plain,
% 2.90/1.06      ( $false ),
% 2.90/1.06      inference(minisat,[status(thm)],[c_5194,c_4552,c_3351,c_639,c_626]) ).
% 2.90/1.06  
% 2.90/1.06  
% 2.90/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 2.90/1.06  
% 2.90/1.06  ------                               Statistics
% 2.90/1.06  
% 2.90/1.06  ------ General
% 2.90/1.06  
% 2.90/1.06  abstr_ref_over_cycles:                  0
% 2.90/1.06  abstr_ref_under_cycles:                 0
% 2.90/1.06  gc_basic_clause_elim:                   0
% 2.90/1.06  forced_gc_time:                         0
% 2.90/1.06  parsing_time:                           0.012
% 2.90/1.06  unif_index_cands_time:                  0.
% 2.90/1.06  unif_index_add_time:                    0.
% 2.90/1.06  orderings_time:                         0.
% 2.90/1.06  out_proof_time:                         0.021
% 2.90/1.06  total_time:                             0.293
% 2.90/1.06  num_of_symbols:                         60
% 2.90/1.06  num_of_terms:                           5821
% 2.90/1.06  
% 2.90/1.06  ------ Preprocessing
% 2.90/1.06  
% 2.90/1.06  num_of_splits:                          0
% 2.90/1.06  num_of_split_atoms:                     0
% 2.90/1.06  num_of_reused_defs:                     0
% 2.90/1.06  num_eq_ax_congr_red:                    24
% 2.90/1.06  num_of_sem_filtered_clauses:            1
% 2.90/1.06  num_of_subtypes:                        3
% 2.90/1.06  monotx_restored_types:                  0
% 2.90/1.06  sat_num_of_epr_types:                   0
% 2.90/1.06  sat_num_of_non_cyclic_types:            0
% 2.90/1.06  sat_guarded_non_collapsed_types:        0
% 2.90/1.06  num_pure_diseq_elim:                    0
% 2.90/1.06  simp_replaced_by:                       0
% 2.90/1.06  res_preprocessed:                       159
% 2.90/1.06  prep_upred:                             0
% 2.90/1.06  prep_unflattend:                        44
% 2.90/1.06  smt_new_axioms:                         0
% 2.90/1.06  pred_elim_cands:                        7
% 2.90/1.06  pred_elim:                              5
% 2.90/1.06  pred_elim_cl:                           4
% 2.90/1.06  pred_elim_cycles:                       11
% 2.90/1.06  merged_defs:                            0
% 2.90/1.06  merged_defs_ncl:                        0
% 2.90/1.06  bin_hyper_res:                          0
% 2.90/1.06  prep_cycles:                            4
% 2.90/1.06  pred_elim_time:                         0.018
% 2.90/1.06  splitting_time:                         0.
% 2.90/1.06  sem_filter_time:                        0.
% 2.90/1.06  monotx_time:                            0.
% 2.90/1.06  subtype_inf_time:                       0.
% 2.90/1.06  
% 2.90/1.06  ------ Problem properties
% 2.90/1.06  
% 2.90/1.06  clauses:                                30
% 2.90/1.06  conjectures:                            7
% 2.90/1.06  epr:                                    6
% 2.90/1.06  horn:                                   27
% 2.90/1.06  ground:                                 15
% 2.90/1.06  unary:                                  14
% 2.90/1.06  binary:                                 0
% 2.90/1.06  lits:                                   94
% 2.90/1.06  lits_eq:                                10
% 2.90/1.06  fd_pure:                                0
% 2.90/1.06  fd_pseudo:                              0
% 2.90/1.06  fd_cond:                                0
% 2.90/1.06  fd_pseudo_cond:                         0
% 2.90/1.06  ac_symbols:                             0
% 2.90/1.06  
% 2.90/1.06  ------ Propositional Solver
% 2.90/1.06  
% 2.90/1.06  prop_solver_calls:                      31
% 2.90/1.06  prop_fast_solver_calls:                 1586
% 2.90/1.06  smt_solver_calls:                       0
% 2.90/1.06  smt_fast_solver_calls:                  0
% 2.90/1.06  prop_num_of_clauses:                    2052
% 2.90/1.06  prop_preprocess_simplified:             6037
% 2.90/1.06  prop_fo_subsumed:                       77
% 2.90/1.06  prop_solver_time:                       0.
% 2.90/1.06  smt_solver_time:                        0.
% 2.90/1.06  smt_fast_solver_time:                   0.
% 2.90/1.06  prop_fast_solver_time:                  0.
% 2.90/1.06  prop_unsat_core_time:                   0.
% 2.90/1.06  
% 2.90/1.06  ------ QBF
% 2.90/1.06  
% 2.90/1.06  qbf_q_res:                              0
% 2.90/1.06  qbf_num_tautologies:                    0
% 2.90/1.06  qbf_prep_cycles:                        0
% 2.90/1.06  
% 2.90/1.06  ------ BMC1
% 2.90/1.06  
% 2.90/1.06  bmc1_current_bound:                     -1
% 2.90/1.06  bmc1_last_solved_bound:                 -1
% 2.90/1.06  bmc1_unsat_core_size:                   -1
% 2.90/1.06  bmc1_unsat_core_parents_size:           -1
% 2.90/1.06  bmc1_merge_next_fun:                    0
% 2.90/1.06  bmc1_unsat_core_clauses_time:           0.
% 2.90/1.06  
% 2.90/1.06  ------ Instantiation
% 2.90/1.06  
% 2.90/1.06  inst_num_of_clauses:                    563
% 2.90/1.06  inst_num_in_passive:                    16
% 2.90/1.06  inst_num_in_active:                     422
% 2.90/1.06  inst_num_in_unprocessed:                126
% 2.90/1.06  inst_num_of_loops:                      460
% 2.90/1.06  inst_num_of_learning_restarts:          0
% 2.90/1.06  inst_num_moves_active_passive:          33
% 2.90/1.06  inst_lit_activity:                      0
% 2.90/1.06  inst_lit_activity_moves:                0
% 2.90/1.06  inst_num_tautologies:                   0
% 2.90/1.06  inst_num_prop_implied:                  0
% 2.90/1.06  inst_num_existing_simplified:           0
% 2.90/1.06  inst_num_eq_res_simplified:             0
% 2.90/1.06  inst_num_child_elim:                    0
% 2.90/1.06  inst_num_of_dismatching_blockings:      179
% 2.90/1.06  inst_num_of_non_proper_insts:           736
% 2.90/1.06  inst_num_of_duplicates:                 0
% 2.90/1.06  inst_inst_num_from_inst_to_res:         0
% 2.90/1.06  inst_dismatching_checking_time:         0.
% 2.90/1.06  
% 2.90/1.06  ------ Resolution
% 2.90/1.06  
% 2.90/1.06  res_num_of_clauses:                     0
% 2.90/1.06  res_num_in_passive:                     0
% 2.90/1.06  res_num_in_active:                      0
% 2.90/1.06  res_num_of_loops:                       163
% 2.90/1.06  res_forward_subset_subsumed:            80
% 2.90/1.06  res_backward_subset_subsumed:           2
% 2.90/1.06  res_forward_subsumed:                   0
% 2.90/1.06  res_backward_subsumed:                  0
% 2.90/1.06  res_forward_subsumption_resolution:     0
% 2.90/1.06  res_backward_subsumption_resolution:    0
% 2.90/1.06  res_clause_to_clause_subsumption:       200
% 2.90/1.06  res_orphan_elimination:                 0
% 2.90/1.06  res_tautology_del:                      177
% 2.90/1.06  res_num_eq_res_simplified:              0
% 2.90/1.06  res_num_sel_changes:                    0
% 2.90/1.06  res_moves_from_active_to_pass:          0
% 2.90/1.06  
% 2.90/1.06  ------ Superposition
% 2.90/1.06  
% 2.90/1.06  sup_time_total:                         0.
% 2.90/1.06  sup_time_generating:                    0.
% 2.90/1.06  sup_time_sim_full:                      0.
% 2.90/1.06  sup_time_sim_immed:                     0.
% 2.90/1.06  
% 2.90/1.06  sup_num_of_clauses:                     121
% 2.90/1.06  sup_num_in_active:                      83
% 2.90/1.06  sup_num_in_passive:                     38
% 2.90/1.06  sup_num_of_loops:                       91
% 2.90/1.06  sup_fw_superposition:                   60
% 2.90/1.06  sup_bw_superposition:                   40
% 2.90/1.06  sup_immediate_simplified:               9
% 2.90/1.06  sup_given_eliminated:                   0
% 2.90/1.06  comparisons_done:                       0
% 2.90/1.06  comparisons_avoided:                    0
% 2.90/1.06  
% 2.90/1.06  ------ Simplifications
% 2.90/1.06  
% 2.90/1.06  
% 2.90/1.06  sim_fw_subset_subsumed:                 1
% 2.90/1.06  sim_bw_subset_subsumed:                 6
% 2.90/1.06  sim_fw_subsumed:                        0
% 2.90/1.06  sim_bw_subsumed:                        2
% 2.90/1.06  sim_fw_subsumption_res:                 0
% 2.90/1.06  sim_bw_subsumption_res:                 0
% 2.90/1.06  sim_tautology_del:                      0
% 2.90/1.06  sim_eq_tautology_del:                   3
% 2.90/1.06  sim_eq_res_simp:                        0
% 2.90/1.06  sim_fw_demodulated:                     1
% 2.90/1.06  sim_bw_demodulated:                     4
% 2.90/1.06  sim_light_normalised:                   6
% 2.90/1.06  sim_joinable_taut:                      0
% 2.90/1.06  sim_joinable_simp:                      0
% 2.90/1.06  sim_ac_normalised:                      0
% 2.90/1.06  sim_smt_subsumption:                    0
% 2.90/1.06  
%------------------------------------------------------------------------------
