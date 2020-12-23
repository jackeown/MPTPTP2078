%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:44 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  288 (1351 expanded)
%              Number of clauses        :  188 ( 263 expanded)
%              Number of leaves         :   27 ( 515 expanded)
%              Depth                    :   27
%              Number of atoms          : 1880 (20493 expanded)
%              Number of equality atoms :  205 (1497 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    4 (   1 average)

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
    inference(negated_conjecture,[],[f15])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | ~ r1_tmap_1(X1,X0,X2,X4) )
          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | r1_tmap_1(X1,X0,X2,X4) )
          & X4 = X5
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7)
          | ~ r1_tmap_1(X1,X0,X2,X4) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7)
          | r1_tmap_1(X1,X0,X2,X4) )
        & sK7 = X4
        & m1_subset_1(sK7,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                | ~ r1_tmap_1(X1,X0,X2,X4) )
              & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                | r1_tmap_1(X1,X0,X2,X4) )
              & X4 = X5
              & m1_subset_1(X5,u1_struct_0(X3)) )
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | ~ r1_tmap_1(X1,X0,X2,sK6) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | r1_tmap_1(X1,X0,X2,sK6) )
            & sK6 = X5
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                    | ~ r1_tmap_1(X1,X0,X2,X4) )
                  & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                    | r1_tmap_1(X1,X0,X2,X4) )
                  & X4 = X5
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_pre_topc(X3,X1)
          & v1_tsep_1(X3,X1)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5)
                  | ~ r1_tmap_1(X1,X0,X2,X4) )
                & ( r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5)
                  | r1_tmap_1(X1,X0,X2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(sK5)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_pre_topc(sK5,X1)
        & v1_tsep_1(sK5,X1)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                        | ~ r1_tmap_1(X1,X0,X2,X4) )
                      & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                        | r1_tmap_1(X1,X0,X2,X4) )
                      & X4 = X5
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_pre_topc(X3,X1)
              & v1_tsep_1(X3,X1)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5)
                      | ~ r1_tmap_1(X1,X0,sK4,X4) )
                    & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5)
                      | r1_tmap_1(X1,X0,sK4,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_pre_topc(X3,X1)
            & v1_tsep_1(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,X0,X2,X4) )
                          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                            | r1_tmap_1(X1,X0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5)
                          | ~ r1_tmap_1(sK3,X0,X2,X4) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5)
                          | r1_tmap_1(sK3,X0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(sK3)) )
                & m1_pre_topc(X3,sK3)
                & v1_tsep_1(X3,sK3)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | r1_tmap_1(X1,X0,X2,X4) )
                            & X4 = X5
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
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
                          ( ( ~ r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK2,X2,X4) )
                          & ( r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5)
                            | r1_tmap_1(X1,sK2,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
      | ~ r1_tmap_1(sK3,sK2,sK4,sK6) )
    & ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
      | r1_tmap_1(sK3,sK2,sK4,sK6) )
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_pre_topc(sK5,sK3)
    & v1_tsep_1(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f54,f60,f59,f58,f57,f56,f55])).

fof(f94,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f61])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & r1_tarski(X4,u1_struct_0(X3))
                                  & r2_hidden(X5,X4)
                                  & v3_pre_topc(X4,X1) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
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
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
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
    inference(flattening,[],[f40])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X1,X0,X2,X5)
                                  | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | ~ r1_tmap_1(X1,X0,X2,X5) ) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
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
    inference(nnf_transformation,[],[f41])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X5,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
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
    inference(cnf_transformation,[],[f52])).

fof(f104,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X6,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
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
    inference(equality_resolution,[],[f82])).

fof(f90,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f89,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f5,axiom,(
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

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f87,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f88,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f92,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f84,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f83,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f85,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f91,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f61])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK1(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

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

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK1(X0,X1,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | X5 != X6
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X5,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
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
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X6,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
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
    inference(equality_resolution,[],[f81])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
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
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
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
    inference(flattening,[],[f38])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
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
    inference(cnf_transformation,[],[f39])).

fof(f103,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
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
    inference(equality_resolution,[],[f80])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f44])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f99,plain,
    ( ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ r1_tmap_1(sK3,sK2,sK4,sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f97,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f61])).

fof(f98,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | r1_tmap_1(sK3,sK2,sK4,sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f35])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f93,plain,(
    v1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f96,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f61])).

fof(f95,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_11468,plain,
    ( ~ r1_tmap_1(X0_55,X1_55,X0_54,X1_54)
    | r1_tmap_1(X0_55,X1_55,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_13211,plain,
    ( r1_tmap_1(sK5,sK2,X0_54,X1_54)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | X1_54 != sK7 ),
    inference(instantiation,[status(thm)],[c_11468])).

cnf(c_13408,plain,
    ( r1_tmap_1(sK5,sK2,X0_54,sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_13211])).

cnf(c_15244,plain,
    ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_13408])).

cnf(c_15246,plain,
    ( k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK6 != sK7
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15244])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_19,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_699,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_700,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v3_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r2_hidden(X3,X4)
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_704,plain,
    ( ~ r2_hidden(X3,X4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ v3_pre_topc(X4,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_700,c_31])).

cnf(c_705,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v3_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r2_hidden(X3,X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_704])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_748,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v3_pre_topc(X4,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r2_hidden(X3,X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_705,c_4])).

cnf(c_966,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | r1_tmap_1(X2,X1,sK4,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v3_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r2_hidden(X3,X4)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_748])).

cnf(c_967,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_966])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_971,plain,
    ( ~ v2_pre_topc(X0)
    | r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_967,c_34,c_33,c_32,c_28])).

cnf(c_972,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_971])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2027,plain,
    ( r1_tmap_1(sK3,X0,sK4,X1)
    | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ r1_tarski(X2,u1_struct_0(sK5))
    | ~ v3_pre_topc(X2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | ~ r2_hidden(X1,X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_972,c_36])).

cnf(c_2028,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | ~ v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ r2_hidden(X0,X1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_2027])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2032,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ v3_pre_topc(X1,sK3)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r2_hidden(X0,X1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2028,c_37,c_35,c_29])).

cnf(c_2033,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tarski(X1,u1_struct_0(sK5))
    | ~ v3_pre_topc(X1,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,X1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_2032])).

cnf(c_11434,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_54)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
    | ~ r1_tarski(X1_54,u1_struct_0(sK5))
    | ~ v3_pre_topc(X1_54,sK3)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0_54,X1_54)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_2033])).

cnf(c_11678,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_54)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
    | ~ r1_tarski(X1_54,u1_struct_0(sK5))
    | ~ v3_pre_topc(X1_54,sK3)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0_54,X1_54) ),
    inference(equality_resolution_simp,[status(thm)],[c_11434])).

cnf(c_14087,plain,
    ( r1_tmap_1(sK3,sK2,sK4,X0_54)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
    | ~ r1_tarski(sK1(sK3,sK6,u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ v3_pre_topc(sK1(sK3,sK6,u1_struct_0(sK5)),sK3)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | ~ m1_subset_1(sK1(sK3,sK6,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0_54,sK1(sK3,sK6,u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_11678])).

cnf(c_15236,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6)
    | ~ r1_tarski(sK1(sK3,sK6,u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ v3_pre_topc(sK1(sK3,sK6,u1_struct_0(sK5)),sK3)
    | ~ m1_subset_1(sK1(sK3,sK6,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ r2_hidden(sK6,sK1(sK3,sK6,u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_14087])).

cnf(c_15237,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6) != iProver_top
    | r1_tarski(sK1(sK3,sK6,u1_struct_0(sK5)),u1_struct_0(sK5)) != iProver_top
    | v3_pre_topc(sK1(sK3,sK6,u1_struct_0(sK5)),sK3) != iProver_top
    | m1_subset_1(sK1(sK3,sK6,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK6,sK1(sK3,sK6,u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15236])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_11448,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ r2_hidden(X2_54,X0_54)
    | ~ v1_xboole_0(X1_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_13274,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1_54,X0_54)
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_11448])).

cnf(c_13573,plain,
    ( ~ m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0_54,sK0(sK5,sK7))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_13274])).

cnf(c_13930,plain,
    ( ~ m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK7,sK0(sK5,sK7))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_13573])).

cnf(c_13931,plain,
    ( m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK7,sK0(sK5,sK7)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13930])).

cnf(c_11467,plain,
    ( X0_54 != X1_54
    | k2_tmap_1(X0_55,X1_55,X0_54,X2_55) = k2_tmap_1(X0_55,X1_55,X1_54,X2_55) ),
    theory(equality)).

cnf(c_13795,plain,
    ( X0_54 != sK4
    | k2_tmap_1(sK3,sK2,X0_54,sK5) = k2_tmap_1(sK3,sK2,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_11467])).

cnf(c_13798,plain,
    ( k2_tmap_1(sK3,sK2,sK4,sK5) = k2_tmap_1(sK3,sK2,sK4,sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_13795])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_11449,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | r2_hidden(X0_54,X1_54)
    | v1_xboole_0(X1_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_13722,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK5))
    | r2_hidden(sK6,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_11449])).

cnf(c_13723,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK6,u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13722])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_5,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_5])).

cnf(c_237,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_236])).

cnf(c_2207,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK1(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_237,c_33])).

cnf(c_2208,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | r1_tarski(sK1(sK3,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2207])).

cnf(c_2212,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | r1_tarski(sK1(sK3,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2208,c_34,c_32])).

cnf(c_11427,plain,
    ( ~ m1_connsp_2(X0_54,sK3,X1_54)
    | r1_tarski(sK1(sK3,X1_54,X0_54),X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_2212])).

cnf(c_13049,plain,
    ( ~ m1_connsp_2(X0_54,sK3,sK6)
    | r1_tarski(sK1(sK3,sK6,X0_54),X0_54)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_11427])).

cnf(c_13658,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK6)
    | r1_tarski(sK1(sK3,sK6,u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_13049])).

cnf(c_13672,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK6) != iProver_top
    | r1_tarski(sK1(sK3,sK6,u1_struct_0(sK5)),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13658])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,sK1(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_243,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,sK1(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_5])).

cnf(c_244,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK1(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_243])).

cnf(c_2186,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,sK1(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_244,c_33])).

cnf(c_2187,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,sK1(sK3,X1,X0))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2186])).

cnf(c_2191,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,sK1(sK3,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2187,c_34,c_32])).

cnf(c_11428,plain,
    ( ~ m1_connsp_2(X0_54,sK3,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | r2_hidden(X1_54,sK1(sK3,X1_54,X0_54)) ),
    inference(subtyping,[status(esa)],[c_2191])).

cnf(c_13054,plain,
    ( ~ m1_connsp_2(X0_54,sK3,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | r2_hidden(sK6,sK1(sK3,sK6,X0_54)) ),
    inference(instantiation,[status(thm)],[c_11428])).

cnf(c_13659,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | r2_hidden(sK6,sK1(sK3,sK6,u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_13054])).

cnf(c_13670,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK6) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK6,sK1(sK3,sK6,u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13659])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_5])).

cnf(c_230,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_2228,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | v3_pre_topc(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_230,c_33])).

cnf(c_2229,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | v3_pre_topc(sK1(sK3,X1,X0),sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2228])).

cnf(c_2233,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | v3_pre_topc(sK1(sK3,X1,X0),sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2229,c_34,c_32])).

cnf(c_11426,plain,
    ( ~ m1_connsp_2(X0_54,sK3,X1_54)
    | v3_pre_topc(sK1(sK3,X1_54,X0_54),sK3)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_2233])).

cnf(c_13039,plain,
    ( ~ m1_connsp_2(X0_54,sK3,sK6)
    | v3_pre_topc(sK1(sK3,sK6,X0_54),sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_11426])).

cnf(c_13661,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK6)
    | v3_pre_topc(sK1(sK3,sK6,u1_struct_0(sK5)),sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_13039])).

cnf(c_13666,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK6) != iProver_top
    | v3_pre_topc(sK1(sK3,sK6,u1_struct_0(sK5)),sK3) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13661])).

cnf(c_13,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_5])).

cnf(c_223,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_222])).

cnf(c_2249,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_223,c_33])).

cnf(c_2250,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2249])).

cnf(c_2254,plain,
    ( ~ m1_connsp_2(X0,sK3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2250,c_34,c_32])).

cnf(c_11425,plain,
    ( ~ m1_connsp_2(X0_54,sK3,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X1_54,X0_54),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_2254])).

cnf(c_13030,plain,
    ( ~ m1_connsp_2(X0_54,sK3,sK6)
    | m1_subset_1(sK1(sK3,sK6,X0_54),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_11425])).

cnf(c_13662,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK6)
    | m1_subset_1(sK1(sK3,sK6,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_13030])).

cnf(c_13664,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK6) != iProver_top
    | m1_subset_1(sK1(sK3,sK6,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13662])).

cnf(c_7,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2303,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_33])).

cnf(c_2304,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_2303])).

cnf(c_2308,plain,
    ( m1_connsp_2(X0,sK3,X1)
    | ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2304,c_34,c_32])).

cnf(c_11423,plain,
    ( m1_connsp_2(X0_54,sK3,X1_54)
    | ~ v3_pre_topc(X0_54,sK3)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_2308])).

cnf(c_13059,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,X0_54)
    | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0_54,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_11423])).

cnf(c_13612,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK6)
    | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ r2_hidden(sK6,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_13059])).

cnf(c_13613,plain,
    ( m1_connsp_2(u1_struct_0(sK5),sK3,sK6) = iProver_top
    | v3_pre_topc(u1_struct_0(sK5),sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13612])).

cnf(c_11459,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_13403,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_11459])).

cnf(c_11462,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | m1_subset_1(X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_13191,plain,
    ( m1_subset_1(X0_54,X1_54)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | X1_54 != u1_struct_0(sK5)
    | X0_54 != sK7 ),
    inference(instantiation,[status(thm)],[c_11462])).

cnf(c_13334,plain,
    ( m1_subset_1(sK6,X0_54)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | X0_54 != u1_struct_0(sK5)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_13191])).

cnf(c_13402,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK5))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | sK6 != sK7 ),
    inference(instantiation,[status(thm)],[c_13334])).

cnf(c_13404,plain,
    ( u1_struct_0(sK5) != u1_struct_0(sK5)
    | sK6 != sK7
    | m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13402])).

cnf(c_8,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_251,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_5])).

cnf(c_252,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_251])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_955,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK3 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_26])).

cnf(c_956,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_955])).

cnf(c_958,plain,
    ( v2_pre_topc(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_956,c_33,c_32])).

cnf(c_2537,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_252,c_958])).

cnf(c_2538,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,X0)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_2537])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_944,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_945,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_944])).

cnf(c_2542,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2538,c_32,c_28,c_945])).

cnf(c_11413,plain,
    ( ~ m1_connsp_2(X0_54,sK5,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
    | r2_hidden(X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_2542])).

cnf(c_13102,plain,
    ( ~ m1_connsp_2(X0_54,sK5,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | r2_hidden(sK7,X0_54) ),
    inference(instantiation,[status(thm)],[c_11413])).

cnf(c_13322,plain,
    ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5))
    | r2_hidden(sK7,sK0(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_13102])).

cnf(c_13323,plain,
    ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) != iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK7,sK0(sK5,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13322])).

cnf(c_2702,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_958])).

cnf(c_2703,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_2702])).

cnf(c_2707,plain,
    ( ~ m1_connsp_2(X0,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2703,c_32,c_28,c_945])).

cnf(c_11406,plain,
    ( ~ m1_connsp_2(X0_54,sK5,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(subtyping,[status(esa)],[c_2707])).

cnf(c_13083,plain,
    ( ~ m1_connsp_2(X0_54,sK5,sK7)
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_11406])).

cnf(c_13313,plain,
    ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
    | m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_13083])).

cnf(c_13314,plain,
    ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) != iProver_top
    | m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13313])).

cnf(c_20,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,X5)
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_18,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f103])).

cnf(c_200,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_18])).

cnf(c_201,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_200])).

cnf(c_642,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_201,c_30])).

cnf(c_643,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_647,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_643,c_31])).

cnf(c_648,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_647])).

cnf(c_683,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_648,c_4])).

cnf(c_1017,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK4,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X2
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_683])).

cnf(c_1018,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1017])).

cnf(c_1022,plain,
    ( ~ v2_pre_topc(X0)
    | ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1018,c_34,c_33,c_32,c_28])).

cnf(c_1023,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_1022])).

cnf(c_2003,plain,
    ( ~ r1_tmap_1(sK3,X0,sK4,X1)
    | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1023,c_36])).

cnf(c_2004,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_2003])).

cnf(c_2008,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK5))
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2004,c_37,c_35,c_29])).

cnf(c_2009,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_2008])).

cnf(c_11435,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0_54)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_2009])).

cnf(c_11674,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,X0_54)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5)) ),
    inference(equality_resolution_simp,[status(thm)],[c_11435])).

cnf(c_13080,plain,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_11674])).

cnf(c_13081,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13080])).

cnf(c_6,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2147,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_958])).

cnf(c_2148,plain,
    ( m1_connsp_2(sK0(sK5,X0),sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_2147])).

cnf(c_2152,plain,
    ( m1_connsp_2(sK0(sK5,X0),sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2148,c_32,c_28,c_945])).

cnf(c_11430,plain,
    ( m1_connsp_2(sK0(sK5,X0_54),sK5,X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_2152])).

cnf(c_13077,plain,
    ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_11430])).

cnf(c_13078,plain,
    ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13077])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_11447,negated_conjecture,
    ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
    | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_12546,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11447])).

cnf(c_23,negated_conjecture,
    ( sK6 = sK7 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_11445,negated_conjecture,
    ( sK6 = sK7 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_12637,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12546,c_11445])).

cnf(c_22,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK6)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_11446,negated_conjecture,
    ( r1_tmap_1(sK3,sK2,sK4,sK6)
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_12547,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11446])).

cnf(c_12626,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12547,c_11445])).

cnf(c_11480,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_11459])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_915,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_916,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_915])).

cnf(c_917,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_916])).

cnf(c_16,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_208,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_17])).

cnf(c_209,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_27,negated_conjecture,
    ( v1_tsep_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_530,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK3 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_209,c_27])).

cnf(c_531,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK3)
    | ~ m1_pre_topc(sK5,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_532,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK3) = iProver_top
    | m1_pre_topc(sK5,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_53,plain,
    ( r1_tmap_1(sK3,sK2,sK4,sK6) != iProver_top
    | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_51,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_50,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_49,plain,
    ( m1_pre_topc(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_43,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15246,c_15237,c_13931,c_13798,c_13723,c_13672,c_13670,c_13666,c_13664,c_13613,c_13403,c_13404,c_13323,c_13314,c_13081,c_13078,c_12637,c_12626,c_11445,c_11480,c_917,c_532,c_53,c_51,c_50,c_49,c_43,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:22:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.04/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/0.97  
% 3.04/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.04/0.97  
% 3.04/0.97  ------  iProver source info
% 3.04/0.97  
% 3.04/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.04/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.04/0.97  git: non_committed_changes: false
% 3.04/0.97  git: last_make_outside_of_git: false
% 3.04/0.97  
% 3.04/0.97  ------ 
% 3.04/0.97  
% 3.04/0.97  ------ Input Options
% 3.04/0.97  
% 3.04/0.97  --out_options                           all
% 3.04/0.97  --tptp_safe_out                         true
% 3.04/0.97  --problem_path                          ""
% 3.04/0.97  --include_path                          ""
% 3.04/0.97  --clausifier                            res/vclausify_rel
% 3.04/0.97  --clausifier_options                    --mode clausify
% 3.04/0.97  --stdin                                 false
% 3.04/0.97  --stats_out                             all
% 3.04/0.97  
% 3.04/0.97  ------ General Options
% 3.04/0.97  
% 3.04/0.97  --fof                                   false
% 3.04/0.97  --time_out_real                         305.
% 3.04/0.97  --time_out_virtual                      -1.
% 3.04/0.97  --symbol_type_check                     false
% 3.04/0.97  --clausify_out                          false
% 3.04/0.97  --sig_cnt_out                           false
% 3.04/0.97  --trig_cnt_out                          false
% 3.04/0.97  --trig_cnt_out_tolerance                1.
% 3.04/0.97  --trig_cnt_out_sk_spl                   false
% 3.04/0.97  --abstr_cl_out                          false
% 3.04/0.97  
% 3.04/0.97  ------ Global Options
% 3.04/0.97  
% 3.04/0.97  --schedule                              default
% 3.04/0.97  --add_important_lit                     false
% 3.04/0.97  --prop_solver_per_cl                    1000
% 3.04/0.97  --min_unsat_core                        false
% 3.04/0.97  --soft_assumptions                      false
% 3.04/0.97  --soft_lemma_size                       3
% 3.04/0.97  --prop_impl_unit_size                   0
% 3.04/0.97  --prop_impl_unit                        []
% 3.04/0.97  --share_sel_clauses                     true
% 3.04/0.97  --reset_solvers                         false
% 3.04/0.97  --bc_imp_inh                            [conj_cone]
% 3.04/0.97  --conj_cone_tolerance                   3.
% 3.04/0.97  --extra_neg_conj                        none
% 3.04/0.97  --large_theory_mode                     true
% 3.04/0.97  --prolific_symb_bound                   200
% 3.04/0.97  --lt_threshold                          2000
% 3.04/0.97  --clause_weak_htbl                      true
% 3.04/0.97  --gc_record_bc_elim                     false
% 3.04/0.97  
% 3.04/0.97  ------ Preprocessing Options
% 3.04/0.97  
% 3.04/0.97  --preprocessing_flag                    true
% 3.04/0.97  --time_out_prep_mult                    0.1
% 3.04/0.97  --splitting_mode                        input
% 3.04/0.97  --splitting_grd                         true
% 3.04/0.97  --splitting_cvd                         false
% 3.04/0.97  --splitting_cvd_svl                     false
% 3.04/0.97  --splitting_nvd                         32
% 3.04/0.97  --sub_typing                            true
% 3.04/0.97  --prep_gs_sim                           true
% 3.04/0.97  --prep_unflatten                        true
% 3.04/0.97  --prep_res_sim                          true
% 3.04/0.97  --prep_upred                            true
% 3.04/0.97  --prep_sem_filter                       exhaustive
% 3.04/0.97  --prep_sem_filter_out                   false
% 3.04/0.97  --pred_elim                             true
% 3.04/0.97  --res_sim_input                         true
% 3.04/0.97  --eq_ax_congr_red                       true
% 3.04/0.97  --pure_diseq_elim                       true
% 3.04/0.97  --brand_transform                       false
% 3.04/0.97  --non_eq_to_eq                          false
% 3.04/0.97  --prep_def_merge                        true
% 3.04/0.97  --prep_def_merge_prop_impl              false
% 3.04/0.97  --prep_def_merge_mbd                    true
% 3.04/0.97  --prep_def_merge_tr_red                 false
% 3.04/0.97  --prep_def_merge_tr_cl                  false
% 3.04/0.97  --smt_preprocessing                     true
% 3.04/0.97  --smt_ac_axioms                         fast
% 3.04/0.97  --preprocessed_out                      false
% 3.04/0.97  --preprocessed_stats                    false
% 3.04/0.97  
% 3.04/0.97  ------ Abstraction refinement Options
% 3.04/0.97  
% 3.04/0.97  --abstr_ref                             []
% 3.04/0.97  --abstr_ref_prep                        false
% 3.04/0.97  --abstr_ref_until_sat                   false
% 3.04/0.97  --abstr_ref_sig_restrict                funpre
% 3.04/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.97  --abstr_ref_under                       []
% 3.04/0.97  
% 3.04/0.97  ------ SAT Options
% 3.04/0.97  
% 3.04/0.97  --sat_mode                              false
% 3.04/0.97  --sat_fm_restart_options                ""
% 3.04/0.97  --sat_gr_def                            false
% 3.04/0.97  --sat_epr_types                         true
% 3.04/0.97  --sat_non_cyclic_types                  false
% 3.04/0.97  --sat_finite_models                     false
% 3.04/0.97  --sat_fm_lemmas                         false
% 3.04/0.97  --sat_fm_prep                           false
% 3.04/0.97  --sat_fm_uc_incr                        true
% 3.04/0.97  --sat_out_model                         small
% 3.04/0.97  --sat_out_clauses                       false
% 3.04/0.97  
% 3.04/0.97  ------ QBF Options
% 3.04/0.97  
% 3.04/0.97  --qbf_mode                              false
% 3.04/0.97  --qbf_elim_univ                         false
% 3.04/0.97  --qbf_dom_inst                          none
% 3.04/0.97  --qbf_dom_pre_inst                      false
% 3.04/0.97  --qbf_sk_in                             false
% 3.04/0.97  --qbf_pred_elim                         true
% 3.04/0.97  --qbf_split                             512
% 3.04/0.97  
% 3.04/0.97  ------ BMC1 Options
% 3.04/0.97  
% 3.04/0.97  --bmc1_incremental                      false
% 3.04/0.97  --bmc1_axioms                           reachable_all
% 3.04/0.97  --bmc1_min_bound                        0
% 3.04/0.97  --bmc1_max_bound                        -1
% 3.04/0.97  --bmc1_max_bound_default                -1
% 3.04/0.97  --bmc1_symbol_reachability              true
% 3.04/0.97  --bmc1_property_lemmas                  false
% 3.04/0.97  --bmc1_k_induction                      false
% 3.04/0.97  --bmc1_non_equiv_states                 false
% 3.04/0.97  --bmc1_deadlock                         false
% 3.04/0.97  --bmc1_ucm                              false
% 3.04/0.97  --bmc1_add_unsat_core                   none
% 3.04/0.97  --bmc1_unsat_core_children              false
% 3.04/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.97  --bmc1_out_stat                         full
% 3.04/0.97  --bmc1_ground_init                      false
% 3.04/0.97  --bmc1_pre_inst_next_state              false
% 3.04/0.97  --bmc1_pre_inst_state                   false
% 3.04/0.97  --bmc1_pre_inst_reach_state             false
% 3.04/0.97  --bmc1_out_unsat_core                   false
% 3.04/0.97  --bmc1_aig_witness_out                  false
% 3.04/0.97  --bmc1_verbose                          false
% 3.04/0.97  --bmc1_dump_clauses_tptp                false
% 3.04/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.97  --bmc1_dump_file                        -
% 3.04/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.97  --bmc1_ucm_extend_mode                  1
% 3.04/0.97  --bmc1_ucm_init_mode                    2
% 3.04/0.97  --bmc1_ucm_cone_mode                    none
% 3.04/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.97  --bmc1_ucm_relax_model                  4
% 3.04/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.97  --bmc1_ucm_layered_model                none
% 3.04/0.97  --bmc1_ucm_max_lemma_size               10
% 3.04/0.97  
% 3.04/0.97  ------ AIG Options
% 3.04/0.97  
% 3.04/0.97  --aig_mode                              false
% 3.04/0.97  
% 3.04/0.97  ------ Instantiation Options
% 3.04/0.97  
% 3.04/0.97  --instantiation_flag                    true
% 3.04/0.97  --inst_sos_flag                         false
% 3.04/0.97  --inst_sos_phase                        true
% 3.04/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.97  --inst_lit_sel_side                     num_symb
% 3.04/0.97  --inst_solver_per_active                1400
% 3.04/0.97  --inst_solver_calls_frac                1.
% 3.04/0.97  --inst_passive_queue_type               priority_queues
% 3.04/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.97  --inst_passive_queues_freq              [25;2]
% 3.04/0.97  --inst_dismatching                      true
% 3.04/0.97  --inst_eager_unprocessed_to_passive     true
% 3.04/0.97  --inst_prop_sim_given                   true
% 3.04/0.97  --inst_prop_sim_new                     false
% 3.04/0.97  --inst_subs_new                         false
% 3.04/0.97  --inst_eq_res_simp                      false
% 3.04/0.97  --inst_subs_given                       false
% 3.04/0.97  --inst_orphan_elimination               true
% 3.04/0.97  --inst_learning_loop_flag               true
% 3.04/0.97  --inst_learning_start                   3000
% 3.04/0.97  --inst_learning_factor                  2
% 3.04/0.97  --inst_start_prop_sim_after_learn       3
% 3.04/0.97  --inst_sel_renew                        solver
% 3.04/0.97  --inst_lit_activity_flag                true
% 3.04/0.97  --inst_restr_to_given                   false
% 3.04/0.97  --inst_activity_threshold               500
% 3.04/0.97  --inst_out_proof                        true
% 3.04/0.97  
% 3.04/0.97  ------ Resolution Options
% 3.04/0.97  
% 3.04/0.97  --resolution_flag                       true
% 3.04/0.97  --res_lit_sel                           adaptive
% 3.04/0.97  --res_lit_sel_side                      none
% 3.04/0.97  --res_ordering                          kbo
% 3.04/0.97  --res_to_prop_solver                    active
% 3.04/0.97  --res_prop_simpl_new                    false
% 3.04/0.97  --res_prop_simpl_given                  true
% 3.04/0.97  --res_passive_queue_type                priority_queues
% 3.04/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.97  --res_passive_queues_freq               [15;5]
% 3.04/0.97  --res_forward_subs                      full
% 3.04/0.97  --res_backward_subs                     full
% 3.04/0.97  --res_forward_subs_resolution           true
% 3.04/0.97  --res_backward_subs_resolution          true
% 3.04/0.97  --res_orphan_elimination                true
% 3.04/0.97  --res_time_limit                        2.
% 3.04/0.97  --res_out_proof                         true
% 3.04/0.97  
% 3.04/0.97  ------ Superposition Options
% 3.04/0.97  
% 3.04/0.97  --superposition_flag                    true
% 3.04/0.97  --sup_passive_queue_type                priority_queues
% 3.04/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.97  --demod_completeness_check              fast
% 3.04/0.97  --demod_use_ground                      true
% 3.04/0.97  --sup_to_prop_solver                    passive
% 3.04/0.97  --sup_prop_simpl_new                    true
% 3.04/0.97  --sup_prop_simpl_given                  true
% 3.04/0.97  --sup_fun_splitting                     false
% 3.04/0.97  --sup_smt_interval                      50000
% 3.04/0.97  
% 3.04/0.97  ------ Superposition Simplification Setup
% 3.04/0.97  
% 3.04/0.97  --sup_indices_passive                   []
% 3.04/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.97  --sup_full_bw                           [BwDemod]
% 3.04/0.97  --sup_immed_triv                        [TrivRules]
% 3.04/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.97  --sup_immed_bw_main                     []
% 3.04/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.97  
% 3.04/0.97  ------ Combination Options
% 3.04/0.97  
% 3.04/0.97  --comb_res_mult                         3
% 3.04/0.97  --comb_sup_mult                         2
% 3.04/0.97  --comb_inst_mult                        10
% 3.04/0.97  
% 3.04/0.97  ------ Debug Options
% 3.04/0.97  
% 3.04/0.97  --dbg_backtrace                         false
% 3.04/0.97  --dbg_dump_prop_clauses                 false
% 3.04/0.97  --dbg_dump_prop_clauses_file            -
% 3.04/0.97  --dbg_out_stat                          false
% 3.04/0.97  ------ Parsing...
% 3.04/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.04/0.97  
% 3.04/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 3.04/0.97  
% 3.04/0.97  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.04/0.97  
% 3.04/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.04/0.97  ------ Proving...
% 3.04/0.97  ------ Problem Properties 
% 3.04/0.97  
% 3.04/0.97  
% 3.04/0.97  clauses                                 48
% 3.04/0.97  conjectures                             6
% 3.04/0.97  EPR                                     2
% 3.04/0.97  Horn                                    46
% 3.04/0.97  unary                                   6
% 3.04/0.97  binary                                  6
% 3.04/0.97  lits                                    162
% 3.04/0.97  lits eq                                 7
% 3.04/0.97  fd_pure                                 0
% 3.04/0.97  fd_pseudo                               0
% 3.04/0.97  fd_cond                                 0
% 3.04/0.97  fd_pseudo_cond                          0
% 3.04/0.97  AC symbols                              0
% 3.04/0.97  
% 3.04/0.97  ------ Schedule dynamic 5 is on 
% 3.04/0.97  
% 3.04/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.04/0.97  
% 3.04/0.97  
% 3.04/0.97  ------ 
% 3.04/0.97  Current options:
% 3.04/0.97  ------ 
% 3.04/0.97  
% 3.04/0.97  ------ Input Options
% 3.04/0.97  
% 3.04/0.97  --out_options                           all
% 3.04/0.97  --tptp_safe_out                         true
% 3.04/0.97  --problem_path                          ""
% 3.04/0.97  --include_path                          ""
% 3.04/0.97  --clausifier                            res/vclausify_rel
% 3.04/0.97  --clausifier_options                    --mode clausify
% 3.04/0.97  --stdin                                 false
% 3.04/0.97  --stats_out                             all
% 3.04/0.97  
% 3.04/0.97  ------ General Options
% 3.04/0.97  
% 3.04/0.97  --fof                                   false
% 3.04/0.97  --time_out_real                         305.
% 3.04/0.97  --time_out_virtual                      -1.
% 3.04/0.97  --symbol_type_check                     false
% 3.04/0.97  --clausify_out                          false
% 3.04/0.97  --sig_cnt_out                           false
% 3.04/0.97  --trig_cnt_out                          false
% 3.04/0.97  --trig_cnt_out_tolerance                1.
% 3.04/0.97  --trig_cnt_out_sk_spl                   false
% 3.04/0.97  --abstr_cl_out                          false
% 3.04/0.97  
% 3.04/0.97  ------ Global Options
% 3.04/0.97  
% 3.04/0.97  --schedule                              default
% 3.04/0.97  --add_important_lit                     false
% 3.04/0.97  --prop_solver_per_cl                    1000
% 3.04/0.97  --min_unsat_core                        false
% 3.04/0.97  --soft_assumptions                      false
% 3.04/0.97  --soft_lemma_size                       3
% 3.04/0.97  --prop_impl_unit_size                   0
% 3.04/0.97  --prop_impl_unit                        []
% 3.04/0.97  --share_sel_clauses                     true
% 3.04/0.97  --reset_solvers                         false
% 3.04/0.97  --bc_imp_inh                            [conj_cone]
% 3.04/0.97  --conj_cone_tolerance                   3.
% 3.04/0.97  --extra_neg_conj                        none
% 3.04/0.97  --large_theory_mode                     true
% 3.04/0.97  --prolific_symb_bound                   200
% 3.04/0.97  --lt_threshold                          2000
% 3.04/0.97  --clause_weak_htbl                      true
% 3.04/0.97  --gc_record_bc_elim                     false
% 3.04/0.97  
% 3.04/0.97  ------ Preprocessing Options
% 3.04/0.97  
% 3.04/0.97  --preprocessing_flag                    true
% 3.04/0.97  --time_out_prep_mult                    0.1
% 3.04/0.97  --splitting_mode                        input
% 3.04/0.97  --splitting_grd                         true
% 3.04/0.97  --splitting_cvd                         false
% 3.04/0.97  --splitting_cvd_svl                     false
% 3.04/0.97  --splitting_nvd                         32
% 3.04/0.97  --sub_typing                            true
% 3.04/0.97  --prep_gs_sim                           true
% 3.04/0.97  --prep_unflatten                        true
% 3.04/0.97  --prep_res_sim                          true
% 3.04/0.97  --prep_upred                            true
% 3.04/0.97  --prep_sem_filter                       exhaustive
% 3.04/0.97  --prep_sem_filter_out                   false
% 3.04/0.97  --pred_elim                             true
% 3.04/0.97  --res_sim_input                         true
% 3.04/0.97  --eq_ax_congr_red                       true
% 3.04/0.97  --pure_diseq_elim                       true
% 3.04/0.97  --brand_transform                       false
% 3.04/0.97  --non_eq_to_eq                          false
% 3.04/0.97  --prep_def_merge                        true
% 3.04/0.97  --prep_def_merge_prop_impl              false
% 3.04/0.97  --prep_def_merge_mbd                    true
% 3.04/0.97  --prep_def_merge_tr_red                 false
% 3.04/0.97  --prep_def_merge_tr_cl                  false
% 3.04/0.97  --smt_preprocessing                     true
% 3.04/0.97  --smt_ac_axioms                         fast
% 3.04/0.97  --preprocessed_out                      false
% 3.04/0.97  --preprocessed_stats                    false
% 3.04/0.97  
% 3.04/0.97  ------ Abstraction refinement Options
% 3.04/0.97  
% 3.04/0.97  --abstr_ref                             []
% 3.04/0.97  --abstr_ref_prep                        false
% 3.04/0.97  --abstr_ref_until_sat                   false
% 3.04/0.97  --abstr_ref_sig_restrict                funpre
% 3.04/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.97  --abstr_ref_under                       []
% 3.04/0.97  
% 3.04/0.97  ------ SAT Options
% 3.04/0.97  
% 3.04/0.97  --sat_mode                              false
% 3.04/0.97  --sat_fm_restart_options                ""
% 3.04/0.97  --sat_gr_def                            false
% 3.04/0.97  --sat_epr_types                         true
% 3.04/0.97  --sat_non_cyclic_types                  false
% 3.04/0.97  --sat_finite_models                     false
% 3.04/0.97  --sat_fm_lemmas                         false
% 3.04/0.97  --sat_fm_prep                           false
% 3.04/0.97  --sat_fm_uc_incr                        true
% 3.04/0.97  --sat_out_model                         small
% 3.04/0.97  --sat_out_clauses                       false
% 3.04/0.97  
% 3.04/0.97  ------ QBF Options
% 3.04/0.97  
% 3.04/0.97  --qbf_mode                              false
% 3.04/0.97  --qbf_elim_univ                         false
% 3.04/0.97  --qbf_dom_inst                          none
% 3.04/0.97  --qbf_dom_pre_inst                      false
% 3.04/0.97  --qbf_sk_in                             false
% 3.04/0.97  --qbf_pred_elim                         true
% 3.04/0.97  --qbf_split                             512
% 3.04/0.97  
% 3.04/0.97  ------ BMC1 Options
% 3.04/0.97  
% 3.04/0.97  --bmc1_incremental                      false
% 3.04/0.97  --bmc1_axioms                           reachable_all
% 3.04/0.97  --bmc1_min_bound                        0
% 3.04/0.97  --bmc1_max_bound                        -1
% 3.04/0.97  --bmc1_max_bound_default                -1
% 3.04/0.97  --bmc1_symbol_reachability              true
% 3.04/0.97  --bmc1_property_lemmas                  false
% 3.04/0.97  --bmc1_k_induction                      false
% 3.04/0.97  --bmc1_non_equiv_states                 false
% 3.04/0.97  --bmc1_deadlock                         false
% 3.04/0.97  --bmc1_ucm                              false
% 3.04/0.97  --bmc1_add_unsat_core                   none
% 3.04/0.97  --bmc1_unsat_core_children              false
% 3.04/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.97  --bmc1_out_stat                         full
% 3.04/0.97  --bmc1_ground_init                      false
% 3.04/0.97  --bmc1_pre_inst_next_state              false
% 3.04/0.97  --bmc1_pre_inst_state                   false
% 3.04/0.97  --bmc1_pre_inst_reach_state             false
% 3.04/0.97  --bmc1_out_unsat_core                   false
% 3.04/0.97  --bmc1_aig_witness_out                  false
% 3.04/0.97  --bmc1_verbose                          false
% 3.04/0.97  --bmc1_dump_clauses_tptp                false
% 3.04/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.97  --bmc1_dump_file                        -
% 3.04/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.97  --bmc1_ucm_extend_mode                  1
% 3.04/0.97  --bmc1_ucm_init_mode                    2
% 3.04/0.97  --bmc1_ucm_cone_mode                    none
% 3.04/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.97  --bmc1_ucm_relax_model                  4
% 3.04/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.97  --bmc1_ucm_layered_model                none
% 3.04/0.97  --bmc1_ucm_max_lemma_size               10
% 3.04/0.97  
% 3.04/0.97  ------ AIG Options
% 3.04/0.97  
% 3.04/0.97  --aig_mode                              false
% 3.04/0.97  
% 3.04/0.97  ------ Instantiation Options
% 3.04/0.97  
% 3.04/0.97  --instantiation_flag                    true
% 3.04/0.97  --inst_sos_flag                         false
% 3.04/0.97  --inst_sos_phase                        true
% 3.04/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.97  --inst_lit_sel_side                     none
% 3.04/0.97  --inst_solver_per_active                1400
% 3.04/0.97  --inst_solver_calls_frac                1.
% 3.04/0.97  --inst_passive_queue_type               priority_queues
% 3.04/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.97  --inst_passive_queues_freq              [25;2]
% 3.04/0.97  --inst_dismatching                      true
% 3.04/0.97  --inst_eager_unprocessed_to_passive     true
% 3.04/0.97  --inst_prop_sim_given                   true
% 3.04/0.97  --inst_prop_sim_new                     false
% 3.04/0.97  --inst_subs_new                         false
% 3.04/0.97  --inst_eq_res_simp                      false
% 3.04/0.97  --inst_subs_given                       false
% 3.04/0.97  --inst_orphan_elimination               true
% 3.04/0.97  --inst_learning_loop_flag               true
% 3.04/0.97  --inst_learning_start                   3000
% 3.04/0.97  --inst_learning_factor                  2
% 3.04/0.97  --inst_start_prop_sim_after_learn       3
% 3.04/0.97  --inst_sel_renew                        solver
% 3.04/0.97  --inst_lit_activity_flag                true
% 3.04/0.97  --inst_restr_to_given                   false
% 3.04/0.97  --inst_activity_threshold               500
% 3.04/0.97  --inst_out_proof                        true
% 3.04/0.97  
% 3.04/0.97  ------ Resolution Options
% 3.04/0.97  
% 3.04/0.97  --resolution_flag                       false
% 3.04/0.97  --res_lit_sel                           adaptive
% 3.04/0.97  --res_lit_sel_side                      none
% 3.04/0.97  --res_ordering                          kbo
% 3.04/0.97  --res_to_prop_solver                    active
% 3.04/0.97  --res_prop_simpl_new                    false
% 3.04/0.97  --res_prop_simpl_given                  true
% 3.04/0.97  --res_passive_queue_type                priority_queues
% 3.04/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.97  --res_passive_queues_freq               [15;5]
% 3.04/0.97  --res_forward_subs                      full
% 3.04/0.97  --res_backward_subs                     full
% 3.04/0.97  --res_forward_subs_resolution           true
% 3.04/0.97  --res_backward_subs_resolution          true
% 3.04/0.97  --res_orphan_elimination                true
% 3.04/0.97  --res_time_limit                        2.
% 3.04/0.97  --res_out_proof                         true
% 3.04/0.97  
% 3.04/0.97  ------ Superposition Options
% 3.04/0.97  
% 3.04/0.97  --superposition_flag                    true
% 3.04/0.97  --sup_passive_queue_type                priority_queues
% 3.04/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.97  --demod_completeness_check              fast
% 3.04/0.97  --demod_use_ground                      true
% 3.04/0.97  --sup_to_prop_solver                    passive
% 3.04/0.97  --sup_prop_simpl_new                    true
% 3.04/0.97  --sup_prop_simpl_given                  true
% 3.04/0.97  --sup_fun_splitting                     false
% 3.04/0.97  --sup_smt_interval                      50000
% 3.04/0.97  
% 3.04/0.97  ------ Superposition Simplification Setup
% 3.04/0.97  
% 3.04/0.97  --sup_indices_passive                   []
% 3.04/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.97  --sup_full_bw                           [BwDemod]
% 3.04/0.97  --sup_immed_triv                        [TrivRules]
% 3.04/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.97  --sup_immed_bw_main                     []
% 3.04/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.97  
% 3.04/0.97  ------ Combination Options
% 3.04/0.97  
% 3.04/0.97  --comb_res_mult                         3
% 3.04/0.97  --comb_sup_mult                         2
% 3.04/0.97  --comb_inst_mult                        10
% 3.04/0.97  
% 3.04/0.97  ------ Debug Options
% 3.04/0.97  
% 3.04/0.97  --dbg_backtrace                         false
% 3.04/0.97  --dbg_dump_prop_clauses                 false
% 3.04/0.97  --dbg_dump_prop_clauses_file            -
% 3.04/0.97  --dbg_out_stat                          false
% 3.04/0.97  
% 3.04/0.97  
% 3.04/0.97  
% 3.04/0.97  
% 3.04/0.97  ------ Proving...
% 3.04/0.97  
% 3.04/0.97  
% 3.04/0.97  % SZS status Theorem for theBenchmark.p
% 3.04/0.97  
% 3.04/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.04/0.97  
% 3.04/0.97  fof(f15,conjecture,(
% 3.04/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 3.04/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.97  
% 3.04/0.97  fof(f16,negated_conjecture,(
% 3.04/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 3.04/0.97    inference(negated_conjecture,[],[f15])).
% 3.04/0.97  
% 3.04/0.97  fof(f42,plain,(
% 3.04/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.04/0.97    inference(ennf_transformation,[],[f16])).
% 3.04/0.97  
% 3.04/0.97  fof(f43,plain,(
% 3.04/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.04/0.97    inference(flattening,[],[f42])).
% 3.04/0.97  
% 3.04/0.97  fof(f53,plain,(
% 3.04/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.04/0.97    inference(nnf_transformation,[],[f43])).
% 3.04/0.97  
% 3.04/0.97  fof(f54,plain,(
% 3.04/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.04/0.97    inference(flattening,[],[f53])).
% 3.04/0.97  
% 3.04/0.97  fof(f60,plain,(
% 3.04/0.97    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK7) | r1_tmap_1(X1,X0,X2,X4)) & sK7 = X4 & m1_subset_1(sK7,u1_struct_0(X3)))) )),
% 3.04/0.97    introduced(choice_axiom,[])).
% 3.04/0.97  
% 3.04/0.97  fof(f59,plain,(
% 3.04/0.97    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK6)) & sK6 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK6,u1_struct_0(X1)))) )),
% 3.04/0.97    introduced(choice_axiom,[])).
% 3.04/0.97  
% 3.04/0.97  fof(f58,plain,(
% 3.04/0.97    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK5,X0,k2_tmap_1(X1,X0,X2,sK5),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK5))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK5,X1) & v1_tsep_1(sK5,X1) & ~v2_struct_0(sK5))) )),
% 3.04/0.97    introduced(choice_axiom,[])).
% 3.04/0.97  
% 3.04/0.97  fof(f57,plain,(
% 3.04/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5) | ~r1_tmap_1(X1,X0,sK4,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK4,X3),X5) | r1_tmap_1(X1,X0,sK4,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK4))) )),
% 3.04/0.97    introduced(choice_axiom,[])).
% 3.04/0.97  
% 3.04/0.97  fof(f56,plain,(
% 3.04/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5) | ~r1_tmap_1(sK3,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK3,X0,X2,X3),X5) | r1_tmap_1(sK3,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK3))) & m1_pre_topc(X3,sK3) & v1_tsep_1(X3,sK3) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 3.04/0.97    introduced(choice_axiom,[])).
% 3.04/0.97  
% 3.04/0.97  fof(f55,plain,(
% 3.04/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | ~r1_tmap_1(X1,sK2,X2,X4)) & (r1_tmap_1(X3,sK2,k2_tmap_1(X1,sK2,X2,X3),X5) | r1_tmap_1(X1,sK2,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.04/0.97    introduced(choice_axiom,[])).
% 3.04/0.97  
% 3.04/0.97  fof(f61,plain,(
% 3.04/0.97    ((((((~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK3,sK2,sK4,sK6)) & (r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | r1_tmap_1(sK3,sK2,sK4,sK6)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK5))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_pre_topc(sK5,sK3) & v1_tsep_1(sK5,sK3) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.04/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f54,f60,f59,f58,f57,f56,f55])).
% 3.04/0.97  
% 3.04/0.97  fof(f94,plain,(
% 3.04/0.97    m1_pre_topc(sK5,sK3)),
% 3.04/0.97    inference(cnf_transformation,[],[f61])).
% 3.04/0.97  
% 3.04/0.97  fof(f14,axiom,(
% 3.04/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 3.04/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.97  
% 3.04/0.97  fof(f40,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/0.97    inference(ennf_transformation,[],[f14])).
% 3.04/0.97  
% 3.04/0.97  fof(f41,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.97    inference(flattening,[],[f40])).
% 3.04/0.97  
% 3.04/0.97  fof(f52,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.97    inference(nnf_transformation,[],[f41])).
% 3.04/0.97  
% 3.04/0.97  fof(f82,plain,(
% 3.04/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.97    inference(cnf_transformation,[],[f52])).
% 3.04/0.97  
% 3.04/0.97  fof(f104,plain,(
% 3.04/0.97    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.97    inference(equality_resolution,[],[f82])).
% 3.04/0.97  
% 3.04/0.97  fof(f90,plain,(
% 3.04/0.97    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2))),
% 3.04/0.97    inference(cnf_transformation,[],[f61])).
% 3.04/0.97  
% 3.04/0.97  fof(f89,plain,(
% 3.04/0.97    v1_funct_1(sK4)),
% 3.04/0.97    inference(cnf_transformation,[],[f61])).
% 3.04/0.97  
% 3.04/0.97  fof(f5,axiom,(
% 3.04/0.97    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.04/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.97  
% 3.04/0.97  fof(f23,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/0.97    inference(ennf_transformation,[],[f5])).
% 3.04/0.97  
% 3.04/0.97  fof(f24,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.97    inference(flattening,[],[f23])).
% 3.04/0.97  
% 3.04/0.97  fof(f66,plain,(
% 3.04/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.97    inference(cnf_transformation,[],[f24])).
% 3.04/0.97  
% 3.04/0.97  fof(f86,plain,(
% 3.04/0.97    ~v2_struct_0(sK3)),
% 3.04/0.97    inference(cnf_transformation,[],[f61])).
% 3.04/0.97  
% 3.04/0.97  fof(f87,plain,(
% 3.04/0.97    v2_pre_topc(sK3)),
% 3.04/0.97    inference(cnf_transformation,[],[f61])).
% 3.04/0.97  
% 3.04/0.97  fof(f88,plain,(
% 3.04/0.97    l1_pre_topc(sK3)),
% 3.04/0.97    inference(cnf_transformation,[],[f61])).
% 3.04/0.97  
% 3.04/0.97  fof(f92,plain,(
% 3.04/0.97    ~v2_struct_0(sK5)),
% 3.04/0.97    inference(cnf_transformation,[],[f61])).
% 3.04/0.97  
% 3.04/0.97  fof(f84,plain,(
% 3.04/0.97    v2_pre_topc(sK2)),
% 3.04/0.97    inference(cnf_transformation,[],[f61])).
% 3.04/0.97  
% 3.04/0.97  fof(f83,plain,(
% 3.04/0.97    ~v2_struct_0(sK2)),
% 3.04/0.97    inference(cnf_transformation,[],[f61])).
% 3.04/0.97  
% 3.04/0.97  fof(f85,plain,(
% 3.04/0.97    l1_pre_topc(sK2)),
% 3.04/0.97    inference(cnf_transformation,[],[f61])).
% 3.04/0.97  
% 3.04/0.97  fof(f91,plain,(
% 3.04/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 3.04/0.97    inference(cnf_transformation,[],[f61])).
% 3.04/0.97  
% 3.04/0.97  fof(f2,axiom,(
% 3.04/0.97    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.04/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.97  
% 3.04/0.97  fof(f19,plain,(
% 3.04/0.97    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.04/0.97    inference(ennf_transformation,[],[f2])).
% 3.04/0.97  
% 3.04/0.97  fof(f63,plain,(
% 3.04/0.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.04/0.97    inference(cnf_transformation,[],[f19])).
% 3.04/0.97  
% 3.04/0.97  fof(f1,axiom,(
% 3.04/0.97    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.04/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.97  
% 3.04/0.97  fof(f17,plain,(
% 3.04/0.97    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.04/0.97    inference(ennf_transformation,[],[f1])).
% 3.04/0.97  
% 3.04/0.97  fof(f18,plain,(
% 3.04/0.97    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.04/0.97    inference(flattening,[],[f17])).
% 3.04/0.97  
% 3.04/0.97  fof(f62,plain,(
% 3.04/0.97    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.04/0.97    inference(cnf_transformation,[],[f18])).
% 3.04/0.97  
% 3.04/0.97  fof(f10,axiom,(
% 3.04/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 3.04/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.97  
% 3.04/0.97  fof(f33,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/0.97    inference(ennf_transformation,[],[f10])).
% 3.04/0.97  
% 3.04/0.97  fof(f34,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.97    inference(flattening,[],[f33])).
% 3.04/0.97  
% 3.04/0.97  fof(f46,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.97    inference(nnf_transformation,[],[f34])).
% 3.04/0.97  
% 3.04/0.97  fof(f47,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.97    inference(rectify,[],[f46])).
% 3.04/0.97  
% 3.04/0.97  fof(f48,plain,(
% 3.04/0.97    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.04/0.97    introduced(choice_axiom,[])).
% 3.04/0.97  
% 3.04/0.97  fof(f49,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK1(X0,X1,X2)) & r1_tarski(sK1(X0,X1,X2),X2) & v3_pre_topc(sK1(X0,X1,X2),X0) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 3.04/0.97  
% 3.04/0.97  fof(f73,plain,(
% 3.04/0.97    ( ! [X2,X0,X1] : (r1_tarski(sK1(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.97    inference(cnf_transformation,[],[f49])).
% 3.04/0.97  
% 3.04/0.97  fof(f6,axiom,(
% 3.04/0.97    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.04/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.97  
% 3.04/0.97  fof(f25,plain,(
% 3.04/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/0.97    inference(ennf_transformation,[],[f6])).
% 3.04/0.97  
% 3.04/0.97  fof(f26,plain,(
% 3.04/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.97    inference(flattening,[],[f25])).
% 3.04/0.97  
% 3.04/0.97  fof(f67,plain,(
% 3.04/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.97    inference(cnf_transformation,[],[f26])).
% 3.04/0.97  
% 3.04/0.97  fof(f74,plain,(
% 3.04/0.97    ( ! [X2,X0,X1] : (r2_hidden(X1,sK1(X0,X1,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.97    inference(cnf_transformation,[],[f49])).
% 3.04/0.97  
% 3.04/0.97  fof(f72,plain,(
% 3.04/0.97    ( ! [X2,X0,X1] : (v3_pre_topc(sK1(X0,X1,X2),X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.97    inference(cnf_transformation,[],[f49])).
% 3.04/0.97  
% 3.04/0.97  fof(f71,plain,(
% 3.04/0.97    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.97    inference(cnf_transformation,[],[f49])).
% 3.04/0.97  
% 3.04/0.97  fof(f8,axiom,(
% 3.04/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 3.04/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.97  
% 3.04/0.97  fof(f29,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/0.97    inference(ennf_transformation,[],[f8])).
% 3.04/0.97  
% 3.04/0.97  fof(f30,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.97    inference(flattening,[],[f29])).
% 3.04/0.97  
% 3.04/0.97  fof(f69,plain,(
% 3.04/0.97    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.97    inference(cnf_transformation,[],[f30])).
% 3.04/0.97  
% 3.04/0.97  fof(f9,axiom,(
% 3.04/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 3.04/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.97  
% 3.04/0.97  fof(f31,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/0.97    inference(ennf_transformation,[],[f9])).
% 3.04/0.97  
% 3.04/0.97  fof(f32,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.97    inference(flattening,[],[f31])).
% 3.04/0.97  
% 3.04/0.97  fof(f70,plain,(
% 3.04/0.97    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.97    inference(cnf_transformation,[],[f32])).
% 3.04/0.97  
% 3.04/0.97  fof(f3,axiom,(
% 3.04/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.04/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.97  
% 3.04/0.97  fof(f20,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.04/0.97    inference(ennf_transformation,[],[f3])).
% 3.04/0.97  
% 3.04/0.97  fof(f21,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.04/0.97    inference(flattening,[],[f20])).
% 3.04/0.97  
% 3.04/0.97  fof(f64,plain,(
% 3.04/0.97    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.04/0.97    inference(cnf_transformation,[],[f21])).
% 3.04/0.97  
% 3.04/0.97  fof(f4,axiom,(
% 3.04/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.04/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.97  
% 3.04/0.97  fof(f22,plain,(
% 3.04/0.97    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.04/0.97    inference(ennf_transformation,[],[f4])).
% 3.04/0.97  
% 3.04/0.97  fof(f65,plain,(
% 3.04/0.97    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.04/0.97    inference(cnf_transformation,[],[f22])).
% 3.04/0.98  
% 3.04/0.98  fof(f81,plain,(
% 3.04/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f52])).
% 3.04/0.98  
% 3.04/0.98  fof(f105,plain,(
% 3.04/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.98    inference(equality_resolution,[],[f81])).
% 3.04/0.98  
% 3.04/0.98  fof(f13,axiom,(
% 3.04/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 3.04/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f38,plain,(
% 3.04/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/0.98    inference(ennf_transformation,[],[f13])).
% 3.04/0.98  
% 3.04/0.98  fof(f39,plain,(
% 3.04/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.98    inference(flattening,[],[f38])).
% 3.04/0.98  
% 3.04/0.98  fof(f80,plain,(
% 3.04/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f39])).
% 3.04/0.98  
% 3.04/0.98  fof(f103,plain,(
% 3.04/0.98    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.98    inference(equality_resolution,[],[f80])).
% 3.04/0.98  
% 3.04/0.98  fof(f7,axiom,(
% 3.04/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 3.04/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f27,plain,(
% 3.04/0.98    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.04/0.98    inference(ennf_transformation,[],[f7])).
% 3.04/0.98  
% 3.04/0.98  fof(f28,plain,(
% 3.04/0.98    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.98    inference(flattening,[],[f27])).
% 3.04/0.98  
% 3.04/0.98  fof(f44,plain,(
% 3.04/0.98    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 3.04/0.98    introduced(choice_axiom,[])).
% 3.04/0.98  
% 3.04/0.98  fof(f45,plain,(
% 3.04/0.98    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.04/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f44])).
% 3.04/0.98  
% 3.04/0.98  fof(f68,plain,(
% 3.04/0.98    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f45])).
% 3.04/0.98  
% 3.04/0.98  fof(f99,plain,(
% 3.04/0.98    ~r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | ~r1_tmap_1(sK3,sK2,sK4,sK6)),
% 3.04/0.98    inference(cnf_transformation,[],[f61])).
% 3.04/0.98  
% 3.04/0.98  fof(f97,plain,(
% 3.04/0.98    sK6 = sK7),
% 3.04/0.98    inference(cnf_transformation,[],[f61])).
% 3.04/0.98  
% 3.04/0.98  fof(f98,plain,(
% 3.04/0.98    r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) | r1_tmap_1(sK3,sK2,sK4,sK6)),
% 3.04/0.98    inference(cnf_transformation,[],[f61])).
% 3.04/0.98  
% 3.04/0.98  fof(f12,axiom,(
% 3.04/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.04/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f37,plain,(
% 3.04/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.04/0.98    inference(ennf_transformation,[],[f12])).
% 3.04/0.98  
% 3.04/0.98  fof(f79,plain,(
% 3.04/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f37])).
% 3.04/0.98  
% 3.04/0.98  fof(f11,axiom,(
% 3.04/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.04/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.98  
% 3.04/0.98  fof(f35,plain,(
% 3.04/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.04/0.98    inference(ennf_transformation,[],[f11])).
% 3.04/0.98  
% 3.04/0.98  fof(f36,plain,(
% 3.04/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.04/0.98    inference(flattening,[],[f35])).
% 3.04/0.98  
% 3.04/0.98  fof(f50,plain,(
% 3.04/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.04/0.98    inference(nnf_transformation,[],[f36])).
% 3.04/0.98  
% 3.04/0.98  fof(f51,plain,(
% 3.04/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.04/0.98    inference(flattening,[],[f50])).
% 3.04/0.98  
% 3.04/0.98  fof(f76,plain,(
% 3.04/0.98    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.04/0.98    inference(cnf_transformation,[],[f51])).
% 3.04/0.98  
% 3.04/0.98  fof(f102,plain,(
% 3.04/0.98    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.04/0.98    inference(equality_resolution,[],[f76])).
% 3.04/0.98  
% 3.04/0.98  fof(f93,plain,(
% 3.04/0.98    v1_tsep_1(sK5,sK3)),
% 3.04/0.98    inference(cnf_transformation,[],[f61])).
% 3.04/0.98  
% 3.04/0.98  fof(f96,plain,(
% 3.04/0.98    m1_subset_1(sK7,u1_struct_0(sK5))),
% 3.04/0.98    inference(cnf_transformation,[],[f61])).
% 3.04/0.98  
% 3.04/0.98  fof(f95,plain,(
% 3.04/0.98    m1_subset_1(sK6,u1_struct_0(sK3))),
% 3.04/0.98    inference(cnf_transformation,[],[f61])).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11468,plain,
% 3.04/0.98      ( ~ r1_tmap_1(X0_55,X1_55,X0_54,X1_54)
% 3.04/0.98      | r1_tmap_1(X0_55,X1_55,X2_54,X3_54)
% 3.04/0.98      | X2_54 != X0_54
% 3.04/0.98      | X3_54 != X1_54 ),
% 3.04/0.98      theory(equality) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13211,plain,
% 3.04/0.98      ( r1_tmap_1(sK5,sK2,X0_54,X1_54)
% 3.04/0.98      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 3.04/0.98      | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 3.04/0.98      | X1_54 != sK7 ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11468]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13408,plain,
% 3.04/0.98      ( r1_tmap_1(sK5,sK2,X0_54,sK6)
% 3.04/0.98      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 3.04/0.98      | X0_54 != k2_tmap_1(sK3,sK2,sK4,sK5)
% 3.04/0.98      | sK6 != sK7 ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_13211]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_15244,plain,
% 3.04/0.98      ( r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6)
% 3.04/0.98      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 3.04/0.98      | k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
% 3.04/0.98      | sK6 != sK7 ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_13408]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_15246,plain,
% 3.04/0.98      ( k2_tmap_1(sK3,sK2,sK4,sK5) != k2_tmap_1(sK3,sK2,sK4,sK5)
% 3.04/0.98      | sK6 != sK7
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6) = iProver_top
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_15244]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_26,negated_conjecture,
% 3.04/0.98      ( m1_pre_topc(sK5,sK3) ),
% 3.04/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_19,plain,
% 3.04/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 3.04/0.98      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.04/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.04/0.98      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.04/0.98      | ~ v3_pre_topc(X5,X0)
% 3.04/0.98      | ~ m1_pre_topc(X4,X0)
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.04/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.04/0.98      | ~ r2_hidden(X3,X5)
% 3.04/0.98      | ~ v1_funct_1(X2)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | v2_struct_0(X4)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X0) ),
% 3.04/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_30,negated_conjecture,
% 3.04/0.98      ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK2)) ),
% 3.04/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_699,plain,
% 3.04/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 3.04/0.98      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.04/0.98      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.04/0.98      | ~ v3_pre_topc(X5,X0)
% 3.04/0.98      | ~ m1_pre_topc(X4,X0)
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.04/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.04/0.98      | ~ r2_hidden(X3,X5)
% 3.04/0.98      | ~ v1_funct_1(X2)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X4)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X0)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.04/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 3.04/0.98      | sK4 != X2 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_700,plain,
% 3.04/0.98      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.04/0.98      | r1_tmap_1(X2,X1,sK4,X3)
% 3.04/0.98      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.04/0.98      | ~ v3_pre_topc(X4,X2)
% 3.04/0.98      | ~ m1_pre_topc(X0,X2)
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.04/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.04/0.98      | ~ r2_hidden(X3,X4)
% 3.04/0.98      | ~ v1_funct_1(sK4)
% 3.04/0.98      | v2_struct_0(X2)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | ~ l1_pre_topc(X2)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X2)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.04/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_699]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_31,negated_conjecture,
% 3.04/0.98      ( v1_funct_1(sK4) ),
% 3.04/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_704,plain,
% 3.04/0.98      ( ~ r2_hidden(X3,X4)
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.04/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_pre_topc(X0,X2)
% 3.04/0.98      | ~ v3_pre_topc(X4,X2)
% 3.04/0.98      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.04/0.98      | r1_tmap_1(X2,X1,sK4,X3)
% 3.04/0.98      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.04/0.98      | v2_struct_0(X2)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | ~ l1_pre_topc(X2)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X2)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.04/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_700,c_31]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_705,plain,
% 3.04/0.98      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.04/0.98      | r1_tmap_1(X2,X1,sK4,X3)
% 3.04/0.98      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.04/0.98      | ~ v3_pre_topc(X4,X2)
% 3.04/0.98      | ~ m1_pre_topc(X0,X2)
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.04/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.04/0.98      | ~ r2_hidden(X3,X4)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X2)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ l1_pre_topc(X2)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X2)
% 3.04/0.98      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.04/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_704]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_4,plain,
% 3.04/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.04/0.98      | m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | ~ l1_pre_topc(X1) ),
% 3.04/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_748,plain,
% 3.04/0.98      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.04/0.98      | r1_tmap_1(X2,X1,sK4,X3)
% 3.04/0.98      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.04/0.98      | ~ v3_pre_topc(X4,X2)
% 3.04/0.98      | ~ m1_pre_topc(X0,X2)
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.04/0.98      | ~ r2_hidden(X3,X4)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X2)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ l1_pre_topc(X2)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X2)
% 3.04/0.98      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.04/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_705,c_4]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_966,plain,
% 3.04/0.98      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.04/0.98      | r1_tmap_1(X2,X1,sK4,X3)
% 3.04/0.98      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.04/0.98      | ~ v3_pre_topc(X4,X2)
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.04/0.98      | ~ r2_hidden(X3,X4)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | v2_struct_0(X2)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X2)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X2)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.04/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 3.04/0.98      | sK3 != X2
% 3.04/0.98      | sK5 != X0 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_26,c_748]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_967,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,X0,sK4,X1)
% 3.04/0.98      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.04/0.98      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 3.04/0.98      | ~ v3_pre_topc(X2,sK3)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.04/0.98      | ~ r2_hidden(X1,X2)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | v2_struct_0(sK3)
% 3.04/0.98      | v2_struct_0(sK5)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | ~ l1_pre_topc(sK3)
% 3.04/0.98      | ~ v2_pre_topc(X0)
% 3.04/0.98      | ~ v2_pre_topc(sK3)
% 3.04/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.04/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_966]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_34,negated_conjecture,
% 3.04/0.98      ( ~ v2_struct_0(sK3) ),
% 3.04/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_33,negated_conjecture,
% 3.04/0.98      ( v2_pre_topc(sK3) ),
% 3.04/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_32,negated_conjecture,
% 3.04/0.98      ( l1_pre_topc(sK3) ),
% 3.04/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_28,negated_conjecture,
% 3.04/0.98      ( ~ v2_struct_0(sK5) ),
% 3.04/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_971,plain,
% 3.04/0.98      ( ~ v2_pre_topc(X0)
% 3.04/0.98      | r1_tmap_1(sK3,X0,sK4,X1)
% 3.04/0.98      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.04/0.98      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 3.04/0.98      | ~ v3_pre_topc(X2,sK3)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.04/0.98      | ~ r2_hidden(X1,X2)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.04/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_967,c_34,c_33,c_32,c_28]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_972,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,X0,sK4,X1)
% 3.04/0.98      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.04/0.98      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 3.04/0.98      | ~ v3_pre_topc(X2,sK3)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.04/0.98      | ~ r2_hidden(X1,X2)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | ~ v2_pre_topc(X0)
% 3.04/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.04/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_971]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_36,negated_conjecture,
% 3.04/0.98      ( v2_pre_topc(sK2) ),
% 3.04/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2027,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,X0,sK4,X1)
% 3.04/0.98      | ~ r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.04/0.98      | ~ r1_tarski(X2,u1_struct_0(sK5))
% 3.04/0.98      | ~ v3_pre_topc(X2,sK3)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.04/0.98      | ~ r2_hidden(X1,X2)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.04/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.04/0.98      | sK2 != X0 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_972,c_36]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2028,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 3.04/0.98      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 3.04/0.98      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 3.04/0.98      | ~ v3_pre_topc(X1,sK3)
% 3.04/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 3.04/0.98      | ~ r2_hidden(X0,X1)
% 3.04/0.98      | v2_struct_0(sK2)
% 3.04/0.98      | ~ l1_pre_topc(sK2)
% 3.04/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_2027]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_37,negated_conjecture,
% 3.04/0.98      ( ~ v2_struct_0(sK2) ),
% 3.04/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_35,negated_conjecture,
% 3.04/0.98      ( l1_pre_topc(sK2) ),
% 3.04/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_29,negated_conjecture,
% 3.04/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
% 3.04/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2032,plain,
% 3.04/0.98      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.04/0.98      | ~ v3_pre_topc(X1,sK3)
% 3.04/0.98      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 3.04/0.98      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 3.04/0.98      | r1_tmap_1(sK3,sK2,sK4,X0)
% 3.04/0.98      | ~ r2_hidden(X0,X1)
% 3.04/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_2028,c_37,c_35,c_29]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2033,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,sK2,sK4,X0)
% 3.04/0.98      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 3.04/0.98      | ~ r1_tarski(X1,u1_struct_0(sK5))
% 3.04/0.98      | ~ v3_pre_topc(X1,sK3)
% 3.04/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ r2_hidden(X0,X1)
% 3.04/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_2032]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11434,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,sK2,sK4,X0_54)
% 3.04/0.98      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
% 3.04/0.98      | ~ r1_tarski(X1_54,u1_struct_0(sK5))
% 3.04/0.98      | ~ v3_pre_topc(X1_54,sK3)
% 3.04/0.98      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ r2_hidden(X0_54,X1_54)
% 3.04/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(subtyping,[status(esa)],[c_2033]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11678,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,sK2,sK4,X0_54)
% 3.04/0.98      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
% 3.04/0.98      | ~ r1_tarski(X1_54,u1_struct_0(sK5))
% 3.04/0.98      | ~ v3_pre_topc(X1_54,sK3)
% 3.04/0.98      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ r2_hidden(X0_54,X1_54) ),
% 3.04/0.98      inference(equality_resolution_simp,[status(thm)],[c_11434]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_14087,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,sK2,sK4,X0_54)
% 3.04/0.98      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
% 3.04/0.98      | ~ r1_tarski(sK1(sK3,sK6,u1_struct_0(sK5)),u1_struct_0(sK5))
% 3.04/0.98      | ~ v3_pre_topc(sK1(sK3,sK6,u1_struct_0(sK5)),sK3)
% 3.04/0.98      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(sK1(sK3,sK6,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ r2_hidden(X0_54,sK1(sK3,sK6,u1_struct_0(sK5))) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11678]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_15236,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,sK2,sK4,sK6)
% 3.04/0.98      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6)
% 3.04/0.98      | ~ r1_tarski(sK1(sK3,sK6,u1_struct_0(sK5)),u1_struct_0(sK5))
% 3.04/0.98      | ~ v3_pre_topc(sK1(sK3,sK6,u1_struct_0(sK5)),sK3)
% 3.04/0.98      | ~ m1_subset_1(sK1(sK3,sK6,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 3.04/0.98      | ~ r2_hidden(sK6,sK1(sK3,sK6,u1_struct_0(sK5))) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_14087]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_15237,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,sK2,sK4,sK6) = iProver_top
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK6) != iProver_top
% 3.04/0.98      | r1_tarski(sK1(sK3,sK6,u1_struct_0(sK5)),u1_struct_0(sK5)) != iProver_top
% 3.04/0.98      | v3_pre_topc(sK1(sK3,sK6,u1_struct_0(sK5)),sK3) != iProver_top
% 3.04/0.98      | m1_subset_1(sK1(sK3,sK6,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.04/0.98      | m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 3.04/0.98      | r2_hidden(sK6,sK1(sK3,sK6,u1_struct_0(sK5))) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_15236]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_1,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.04/0.98      | ~ r2_hidden(X2,X0)
% 3.04/0.98      | ~ v1_xboole_0(X1) ),
% 3.04/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11448,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 3.04/0.98      | ~ r2_hidden(X2_54,X0_54)
% 3.04/0.98      | ~ v1_xboole_0(X1_54) ),
% 3.04/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13274,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.04/0.98      | ~ r2_hidden(X1_54,X0_54)
% 3.04/0.98      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11448]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13573,plain,
% 3.04/0.98      ( ~ m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.04/0.98      | ~ r2_hidden(X0_54,sK0(sK5,sK7))
% 3.04/0.98      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_13274]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13930,plain,
% 3.04/0.98      ( ~ m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.04/0.98      | ~ r2_hidden(sK7,sK0(sK5,sK7))
% 3.04/0.98      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_13573]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13931,plain,
% 3.04/0.98      ( m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.04/0.98      | r2_hidden(sK7,sK0(sK5,sK7)) != iProver_top
% 3.04/0.98      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_13930]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11467,plain,
% 3.04/0.98      ( X0_54 != X1_54
% 3.04/0.98      | k2_tmap_1(X0_55,X1_55,X0_54,X2_55) = k2_tmap_1(X0_55,X1_55,X1_54,X2_55) ),
% 3.04/0.98      theory(equality) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13795,plain,
% 3.04/0.98      ( X0_54 != sK4
% 3.04/0.98      | k2_tmap_1(sK3,sK2,X0_54,sK5) = k2_tmap_1(sK3,sK2,sK4,sK5) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11467]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13798,plain,
% 3.04/0.98      ( k2_tmap_1(sK3,sK2,sK4,sK5) = k2_tmap_1(sK3,sK2,sK4,sK5)
% 3.04/0.98      | sK4 != sK4 ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_13795]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_0,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.04/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11449,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0_54,X1_54)
% 3.04/0.98      | r2_hidden(X0_54,X1_54)
% 3.04/0.98      | v1_xboole_0(X1_54) ),
% 3.04/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13722,plain,
% 3.04/0.98      ( ~ m1_subset_1(sK6,u1_struct_0(sK5))
% 3.04/0.98      | r2_hidden(sK6,u1_struct_0(sK5))
% 3.04/0.98      | v1_xboole_0(u1_struct_0(sK5)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11449]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13723,plain,
% 3.04/0.98      ( m1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top
% 3.04/0.98      | r2_hidden(sK6,u1_struct_0(sK5)) = iProver_top
% 3.04/0.98      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_13722]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | r1_tarski(sK1(X1,X2,X0),X0)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_5,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_236,plain,
% 3.04/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | r1_tarski(sK1(X1,X2,X0),X0)
% 3.04/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_11,c_5]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_237,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | r1_tarski(sK1(X1,X2,X0),X0)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_236]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2207,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | r1_tarski(sK1(X1,X2,X0),X0)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | sK3 != X1 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_237,c_33]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2208,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,sK3,X1)
% 3.04/0.98      | r1_tarski(sK1(sK3,X1,X0),X0)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.04/0.98      | v2_struct_0(sK3)
% 3.04/0.98      | ~ l1_pre_topc(sK3) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_2207]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2212,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,sK3,X1)
% 3.04/0.98      | r1_tarski(sK1(sK3,X1,X0),X0)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_2208,c_34,c_32]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11427,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0_54,sK3,X1_54)
% 3.04/0.98      | r1_tarski(sK1(sK3,X1_54,X0_54),X0_54)
% 3.04/0.98      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 3.04/0.98      inference(subtyping,[status(esa)],[c_2212]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13049,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0_54,sK3,sK6)
% 3.04/0.98      | r1_tarski(sK1(sK3,sK6,X0_54),X0_54)
% 3.04/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11427]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13658,plain,
% 3.04/0.98      ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK6)
% 3.04/0.98      | r1_tarski(sK1(sK3,sK6,u1_struct_0(sK5)),u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_13049]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13672,plain,
% 3.04/0.98      ( m1_connsp_2(u1_struct_0(sK5),sK3,sK6) != iProver_top
% 3.04/0.98      | r1_tarski(sK1(sK3,sK6,u1_struct_0(sK5)),u1_struct_0(sK5)) = iProver_top
% 3.04/0.98      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_13658]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_10,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | r2_hidden(X2,sK1(X1,X2,X0))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_243,plain,
% 3.04/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | r2_hidden(X2,sK1(X1,X2,X0))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_10,c_5]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_244,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | r2_hidden(X2,sK1(X1,X2,X0))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_243]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2186,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | r2_hidden(X2,sK1(X1,X2,X0))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | sK3 != X1 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_244,c_33]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2187,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,sK3,X1)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.04/0.98      | r2_hidden(X1,sK1(sK3,X1,X0))
% 3.04/0.98      | v2_struct_0(sK3)
% 3.04/0.98      | ~ l1_pre_topc(sK3) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_2186]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2191,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,sK3,X1)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.04/0.98      | r2_hidden(X1,sK1(sK3,X1,X0)) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_2187,c_34,c_32]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11428,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0_54,sK3,X1_54)
% 3.04/0.98      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 3.04/0.98      | r2_hidden(X1_54,sK1(sK3,X1_54,X0_54)) ),
% 3.04/0.98      inference(subtyping,[status(esa)],[c_2191]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13054,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0_54,sK3,sK6)
% 3.04/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 3.04/0.98      | r2_hidden(sK6,sK1(sK3,sK6,X0_54)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11428]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13659,plain,
% 3.04/0.98      ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK6)
% 3.04/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 3.04/0.98      | r2_hidden(sK6,sK1(sK3,sK6,u1_struct_0(sK5))) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_13054]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13670,plain,
% 3.04/0.98      ( m1_connsp_2(u1_struct_0(sK5),sK3,sK6) != iProver_top
% 3.04/0.98      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 3.04/0.98      | r2_hidden(sK6,sK1(sK3,sK6,u1_struct_0(sK5))) = iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_13659]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_12,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_229,plain,
% 3.04/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 3.04/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_12,c_5]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_230,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_229]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2228,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | v3_pre_topc(sK1(X1,X2,X0),X1)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | sK3 != X1 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_230,c_33]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2229,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,sK3,X1)
% 3.04/0.98      | v3_pre_topc(sK1(sK3,X1,X0),sK3)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.04/0.98      | v2_struct_0(sK3)
% 3.04/0.98      | ~ l1_pre_topc(sK3) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_2228]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2233,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,sK3,X1)
% 3.04/0.98      | v3_pre_topc(sK1(sK3,X1,X0),sK3)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_2229,c_34,c_32]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11426,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0_54,sK3,X1_54)
% 3.04/0.98      | v3_pre_topc(sK1(sK3,X1_54,X0_54),sK3)
% 3.04/0.98      | ~ m1_subset_1(X1_54,u1_struct_0(sK3)) ),
% 3.04/0.98      inference(subtyping,[status(esa)],[c_2233]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13039,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0_54,sK3,sK6)
% 3.04/0.98      | v3_pre_topc(sK1(sK3,sK6,X0_54),sK3)
% 3.04/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11426]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13661,plain,
% 3.04/0.98      ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK6)
% 3.04/0.98      | v3_pre_topc(sK1(sK3,sK6,u1_struct_0(sK5)),sK3)
% 3.04/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_13039]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13666,plain,
% 3.04/0.98      ( m1_connsp_2(u1_struct_0(sK5),sK3,sK6) != iProver_top
% 3.04/0.98      | v3_pre_topc(sK1(sK3,sK6,u1_struct_0(sK5)),sK3) = iProver_top
% 3.04/0.98      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_13661]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_222,plain,
% 3.04/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_13,c_5]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_223,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_222]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2249,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | sK3 != X1 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_223,c_33]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2250,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,sK3,X1)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.04/0.98      | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | v2_struct_0(sK3)
% 3.04/0.98      | ~ l1_pre_topc(sK3) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_2249]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2254,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,sK3,X1)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.04/0.98      | m1_subset_1(sK1(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_2250,c_34,c_32]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11425,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0_54,sK3,X1_54)
% 3.04/0.98      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 3.04/0.98      | m1_subset_1(sK1(sK3,X1_54,X0_54),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.04/0.98      inference(subtyping,[status(esa)],[c_2254]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13030,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0_54,sK3,sK6)
% 3.04/0.98      | m1_subset_1(sK1(sK3,sK6,X0_54),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11425]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13662,plain,
% 3.04/0.98      ( ~ m1_connsp_2(u1_struct_0(sK5),sK3,sK6)
% 3.04/0.98      | m1_subset_1(sK1(sK3,sK6,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_13030]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13664,plain,
% 3.04/0.98      ( m1_connsp_2(u1_struct_0(sK5),sK3,sK6) != iProver_top
% 3.04/0.98      | m1_subset_1(sK1(sK3,sK6,u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.04/0.98      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_13662]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_7,plain,
% 3.04/0.98      ( m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | ~ v3_pre_topc(X0,X1)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | ~ r2_hidden(X2,X0)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2303,plain,
% 3.04/0.98      ( m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | ~ v3_pre_topc(X0,X1)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | ~ r2_hidden(X2,X0)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | sK3 != X1 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_33]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2304,plain,
% 3.04/0.98      ( m1_connsp_2(X0,sK3,X1)
% 3.04/0.98      | ~ v3_pre_topc(X0,sK3)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.04/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ r2_hidden(X1,X0)
% 3.04/0.98      | v2_struct_0(sK3)
% 3.04/0.98      | ~ l1_pre_topc(sK3) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_2303]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2308,plain,
% 3.04/0.98      ( m1_connsp_2(X0,sK3,X1)
% 3.04/0.98      | ~ v3_pre_topc(X0,sK3)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.04/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ r2_hidden(X1,X0) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_2304,c_34,c_32]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11423,plain,
% 3.04/0.98      ( m1_connsp_2(X0_54,sK3,X1_54)
% 3.04/0.98      | ~ v3_pre_topc(X0_54,sK3)
% 3.04/0.98      | ~ m1_subset_1(X1_54,u1_struct_0(sK3))
% 3.04/0.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ r2_hidden(X1_54,X0_54) ),
% 3.04/0.98      inference(subtyping,[status(esa)],[c_2308]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13059,plain,
% 3.04/0.98      ( m1_connsp_2(u1_struct_0(sK5),sK3,X0_54)
% 3.04/0.98      | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 3.04/0.98      | ~ m1_subset_1(X0_54,u1_struct_0(sK3))
% 3.04/0.98      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ r2_hidden(X0_54,u1_struct_0(sK5)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11423]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13612,plain,
% 3.04/0.98      ( m1_connsp_2(u1_struct_0(sK5),sK3,sK6)
% 3.04/0.98      | ~ v3_pre_topc(u1_struct_0(sK5),sK3)
% 3.04/0.98      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 3.04/0.98      | ~ r2_hidden(sK6,u1_struct_0(sK5)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_13059]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13613,plain,
% 3.04/0.98      ( m1_connsp_2(u1_struct_0(sK5),sK3,sK6) = iProver_top
% 3.04/0.98      | v3_pre_topc(u1_struct_0(sK5),sK3) != iProver_top
% 3.04/0.98      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.04/0.98      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 3.04/0.98      | r2_hidden(sK6,u1_struct_0(sK5)) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_13612]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11459,plain,( X0_54 = X0_54 ),theory(equality) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13403,plain,
% 3.04/0.98      ( u1_struct_0(sK5) = u1_struct_0(sK5) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11459]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11462,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0_54,X1_54)
% 3.04/0.98      | m1_subset_1(X2_54,X3_54)
% 3.04/0.98      | X2_54 != X0_54
% 3.04/0.98      | X3_54 != X1_54 ),
% 3.04/0.98      theory(equality) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13191,plain,
% 3.04/0.98      ( m1_subset_1(X0_54,X1_54)
% 3.04/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 3.04/0.98      | X1_54 != u1_struct_0(sK5)
% 3.04/0.98      | X0_54 != sK7 ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11462]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13334,plain,
% 3.04/0.98      ( m1_subset_1(sK6,X0_54)
% 3.04/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 3.04/0.98      | X0_54 != u1_struct_0(sK5)
% 3.04/0.98      | sK6 != sK7 ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_13191]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13402,plain,
% 3.04/0.98      ( m1_subset_1(sK6,u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 3.04/0.98      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 3.04/0.98      | sK6 != sK7 ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_13334]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13404,plain,
% 3.04/0.98      ( u1_struct_0(sK5) != u1_struct_0(sK5)
% 3.04/0.98      | sK6 != sK7
% 3.04/0.98      | m1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top
% 3.04/0.98      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_13402]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_8,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | r2_hidden(X2,X0)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_251,plain,
% 3.04/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | r2_hidden(X2,X0)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(global_propositional_subsumption,[status(thm)],[c_8,c_5]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_252,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | r2_hidden(X2,X0)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_251]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2,plain,
% 3.04/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | v2_pre_topc(X0) ),
% 3.04/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_955,plain,
% 3.04/0.98      ( ~ l1_pre_topc(X0)
% 3.04/0.98      | ~ v2_pre_topc(X0)
% 3.04/0.98      | v2_pre_topc(X1)
% 3.04/0.98      | sK3 != X0
% 3.04/0.98      | sK5 != X1 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_26]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_956,plain,
% 3.04/0.98      ( ~ l1_pre_topc(sK3) | ~ v2_pre_topc(sK3) | v2_pre_topc(sK5) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_955]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_958,plain,
% 3.04/0.98      ( v2_pre_topc(sK5) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_956,c_33,c_32]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2537,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | r2_hidden(X2,X0)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | sK5 != X1 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_252,c_958]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2538,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,sK5,X1)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.98      | r2_hidden(X1,X0)
% 3.04/0.98      | v2_struct_0(sK5)
% 3.04/0.98      | ~ l1_pre_topc(sK5) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_2537]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_3,plain,
% 3.04/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.04/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_944,plain,
% 3.04/0.98      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK3 != X0 | sK5 != X1 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_26]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_945,plain,
% 3.04/0.98      ( ~ l1_pre_topc(sK3) | l1_pre_topc(sK5) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_944]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2542,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,sK5,X1)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.98      | r2_hidden(X1,X0) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_2538,c_32,c_28,c_945]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11413,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0_54,sK5,X1_54)
% 3.04/0.98      | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
% 3.04/0.98      | r2_hidden(X1_54,X0_54) ),
% 3.04/0.98      inference(subtyping,[status(esa)],[c_2542]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13102,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0_54,sK5,sK7)
% 3.04/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 3.04/0.98      | r2_hidden(sK7,X0_54) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11413]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13322,plain,
% 3.04/0.98      ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
% 3.04/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK5))
% 3.04/0.98      | r2_hidden(sK7,sK0(sK5,sK7)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_13102]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13323,plain,
% 3.04/0.98      ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) != iProver_top
% 3.04/0.98      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top
% 3.04/0.98      | r2_hidden(sK7,sK0(sK5,sK7)) = iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_13322]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2702,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 3.04/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | sK5 != X1 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_958]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2703,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,sK5,X1)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.04/0.98      | v2_struct_0(sK5)
% 3.04/0.98      | ~ l1_pre_topc(sK5) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_2702]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2707,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0,sK5,X1)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_2703,c_32,c_28,c_945]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11406,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0_54,sK5,X1_54)
% 3.04/0.98      | ~ m1_subset_1(X1_54,u1_struct_0(sK5))
% 3.04/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 3.04/0.98      inference(subtyping,[status(esa)],[c_2707]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13083,plain,
% 3.04/0.98      ( ~ m1_connsp_2(X0_54,sK5,sK7)
% 3.04/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.04/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11406]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13313,plain,
% 3.04/0.98      ( ~ m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
% 3.04/0.98      | m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.04/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_13083]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13314,plain,
% 3.04/0.98      ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) != iProver_top
% 3.04/0.98      | m1_subset_1(sK0(sK5,sK7),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.04/0.98      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_13313]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_20,plain,
% 3.04/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.04/0.98      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.04/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.04/0.98      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.04/0.98      | ~ v3_pre_topc(X5,X0)
% 3.04/0.98      | ~ m1_pre_topc(X4,X0)
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.04/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.04/0.98      | ~ r2_hidden(X3,X5)
% 3.04/0.98      | ~ v1_funct_1(X2)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | v2_struct_0(X4)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X0) ),
% 3.04/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_18,plain,
% 3.04/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.04/0.98      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.04/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.04/0.98      | ~ m1_pre_topc(X4,X0)
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.04/0.98      | ~ v1_funct_1(X2)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | v2_struct_0(X4)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X0) ),
% 3.04/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_200,plain,
% 3.04/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.04/0.98      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.04/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.04/0.98      | ~ m1_pre_topc(X4,X0)
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.04/0.98      | ~ v1_funct_1(X2)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | v2_struct_0(X4)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X0) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_20,c_18]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_201,plain,
% 3.04/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.04/0.98      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.04/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.04/0.98      | ~ m1_pre_topc(X4,X0)
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.04/0.98      | ~ v1_funct_1(X2)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X4)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X0)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_200]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_642,plain,
% 3.04/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.04/0.98      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.04/0.98      | ~ m1_pre_topc(X4,X0)
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.04/0.98      | ~ v1_funct_1(X2)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X4)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X0)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.04/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 3.04/0.98      | sK4 != X2 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_201,c_30]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_643,plain,
% 3.04/0.98      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.04/0.98      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 3.04/0.98      | ~ m1_pre_topc(X0,X2)
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.04/0.98      | ~ v1_funct_1(sK4)
% 3.04/0.98      | v2_struct_0(X2)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | ~ l1_pre_topc(X2)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X2)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.04/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_642]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_647,plain,
% 3.04/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_pre_topc(X0,X2)
% 3.04/0.98      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 3.04/0.98      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.04/0.98      | v2_struct_0(X2)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | ~ l1_pre_topc(X2)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X2)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.04/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_643,c_31]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_648,plain,
% 3.04/0.98      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.04/0.98      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 3.04/0.98      | ~ m1_pre_topc(X0,X2)
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X2)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ l1_pre_topc(X2)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X2)
% 3.04/0.98      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.04/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_647]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_683,plain,
% 3.04/0.98      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.04/0.98      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 3.04/0.98      | ~ m1_pre_topc(X0,X2)
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | v2_struct_0(X2)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ l1_pre_topc(X2)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X2)
% 3.04/0.98      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.04/0.98      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_648,c_4]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_1017,plain,
% 3.04/0.98      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK4,X0),X3)
% 3.04/0.98      | ~ r1_tmap_1(X2,X1,sK4,X3)
% 3.04/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | v2_struct_0(X2)
% 3.04/0.98      | v2_struct_0(X1)
% 3.04/0.98      | ~ l1_pre_topc(X2)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X2)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | u1_struct_0(X2) != u1_struct_0(sK3)
% 3.04/0.98      | u1_struct_0(X1) != u1_struct_0(sK2)
% 3.04/0.98      | sK3 != X2
% 3.04/0.98      | sK5 != X0 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_26,c_683]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_1018,plain,
% 3.04/0.98      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 3.04/0.98      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | v2_struct_0(sK3)
% 3.04/0.98      | v2_struct_0(sK5)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | ~ l1_pre_topc(sK3)
% 3.04/0.98      | ~ v2_pre_topc(X0)
% 3.04/0.98      | ~ v2_pre_topc(sK3)
% 3.04/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.04/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_1017]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_1022,plain,
% 3.04/0.98      ( ~ v2_pre_topc(X0)
% 3.04/0.98      | ~ r1_tmap_1(sK3,X0,sK4,X1)
% 3.04/0.98      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.04/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_1018,c_34,c_33,c_32,c_28]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_1023,plain,
% 3.04/0.98      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 3.04/0.98      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | ~ v2_pre_topc(X0)
% 3.04/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.04/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_1022]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2003,plain,
% 3.04/0.98      ( ~ r1_tmap_1(sK3,X0,sK4,X1)
% 3.04/0.98      | r1_tmap_1(sK5,X0,k2_tmap_1(sK3,X0,sK4,sK5),X1)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 3.04/0.98      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.04/0.98      | sK2 != X0 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_1023,c_36]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2004,plain,
% 3.04/0.98      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 3.04/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.04/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
% 3.04/0.98      | v2_struct_0(sK2)
% 3.04/0.98      | ~ l1_pre_topc(sK2)
% 3.04/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_2003]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2008,plain,
% 3.04/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 3.04/0.98      | ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 3.04/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_2004,c_37,c_35,c_29]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2009,plain,
% 3.04/0.98      ( ~ r1_tmap_1(sK3,sK2,sK4,X0)
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0)
% 3.04/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.04/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_2008]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11435,plain,
% 3.04/0.98      ( ~ r1_tmap_1(sK3,sK2,sK4,X0_54)
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
% 3.04/0.98      | ~ m1_subset_1(X0_54,u1_struct_0(sK5))
% 3.04/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 3.04/0.98      inference(subtyping,[status(esa)],[c_2009]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11674,plain,
% 3.04/0.98      ( ~ r1_tmap_1(sK3,sK2,sK4,X0_54)
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),X0_54)
% 3.04/0.98      | ~ m1_subset_1(X0_54,u1_struct_0(sK5)) ),
% 3.04/0.98      inference(equality_resolution_simp,[status(thm)],[c_11435]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13080,plain,
% 3.04/0.98      ( ~ r1_tmap_1(sK3,sK2,sK4,sK7)
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7)
% 3.04/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11674]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13081,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top
% 3.04/0.98      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_13080]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_6,plain,
% 3.04/0.98      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | ~ v2_pre_topc(X0) ),
% 3.04/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2147,plain,
% 3.04/0.98      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 3.04/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.04/0.98      | v2_struct_0(X0)
% 3.04/0.98      | ~ l1_pre_topc(X0)
% 3.04/0.98      | sK5 != X0 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_958]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2148,plain,
% 3.04/0.98      ( m1_connsp_2(sK0(sK5,X0),sK5,X0)
% 3.04/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.04/0.98      | v2_struct_0(sK5)
% 3.04/0.98      | ~ l1_pre_topc(sK5) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_2147]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_2152,plain,
% 3.04/0.98      ( m1_connsp_2(sK0(sK5,X0),sK5,X0)
% 3.04/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_2148,c_32,c_28,c_945]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11430,plain,
% 3.04/0.98      ( m1_connsp_2(sK0(sK5,X0_54),sK5,X0_54)
% 3.04/0.98      | ~ m1_subset_1(X0_54,u1_struct_0(sK5)) ),
% 3.04/0.98      inference(subtyping,[status(esa)],[c_2152]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13077,plain,
% 3.04/0.98      ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7)
% 3.04/0.98      | ~ m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11430]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_13078,plain,
% 3.04/0.98      ( m1_connsp_2(sK0(sK5,sK7),sK5,sK7) = iProver_top
% 3.04/0.98      | m1_subset_1(sK7,u1_struct_0(sK5)) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_13077]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_21,negated_conjecture,
% 3.04/0.98      ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
% 3.04/0.98      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 3.04/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11447,negated_conjecture,
% 3.04/0.98      ( ~ r1_tmap_1(sK3,sK2,sK4,sK6)
% 3.04/0.98      | ~ r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 3.04/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_12546,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,sK2,sK4,sK6) != iProver_top
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_11447]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_23,negated_conjecture,
% 3.04/0.98      ( sK6 = sK7 ),
% 3.04/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11445,negated_conjecture,
% 3.04/0.98      ( sK6 = sK7 ),
% 3.04/0.98      inference(subtyping,[status(esa)],[c_23]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_12637,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,sK2,sK4,sK7) != iProver_top
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
% 3.04/0.98      inference(light_normalisation,[status(thm)],[c_12546,c_11445]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_22,negated_conjecture,
% 3.04/0.98      ( r1_tmap_1(sK3,sK2,sK4,sK6)
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 3.04/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11446,negated_conjecture,
% 3.04/0.98      ( r1_tmap_1(sK3,sK2,sK4,sK6)
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) ),
% 3.04/0.98      inference(subtyping,[status(esa)],[c_22]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_12547,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,sK2,sK4,sK6) = iProver_top
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_11446]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_12626,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,sK2,sK4,sK7) = iProver_top
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) = iProver_top ),
% 3.04/0.98      inference(light_normalisation,[status(thm)],[c_12547,c_11445]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_11480,plain,
% 3.04/0.98      ( sK4 = sK4 ),
% 3.04/0.98      inference(instantiation,[status(thm)],[c_11459]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_17,plain,
% 3.04/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.04/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | ~ l1_pre_topc(X1) ),
% 3.04/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_915,plain,
% 3.04/0.98      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | sK3 != X1
% 3.04/0.98      | sK5 != X0 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_916,plain,
% 3.04/0.98      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.04/0.98      | ~ l1_pre_topc(sK3) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_915]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_917,plain,
% 3.04/0.98      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.04/0.98      | l1_pre_topc(sK3) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_916]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_16,plain,
% 3.04/0.98      ( ~ v1_tsep_1(X0,X1)
% 3.04/0.98      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.04/0.98      | ~ m1_pre_topc(X0,X1)
% 3.04/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_208,plain,
% 3.04/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.04/0.98      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.04/0.98      | ~ v1_tsep_1(X0,X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(global_propositional_subsumption,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_16,c_17]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_209,plain,
% 3.04/0.98      ( ~ v1_tsep_1(X0,X1)
% 3.04/0.98      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.04/0.98      | ~ m1_pre_topc(X0,X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1) ),
% 3.04/0.98      inference(renaming,[status(thm)],[c_208]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_27,negated_conjecture,
% 3.04/0.98      ( v1_tsep_1(sK5,sK3) ),
% 3.04/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_530,plain,
% 3.04/0.98      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.04/0.98      | ~ m1_pre_topc(X0,X1)
% 3.04/0.98      | ~ l1_pre_topc(X1)
% 3.04/0.98      | ~ v2_pre_topc(X1)
% 3.04/0.98      | sK3 != X1
% 3.04/0.98      | sK5 != X0 ),
% 3.04/0.98      inference(resolution_lifted,[status(thm)],[c_209,c_27]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_531,plain,
% 3.04/0.98      ( v3_pre_topc(u1_struct_0(sK5),sK3)
% 3.04/0.98      | ~ m1_pre_topc(sK5,sK3)
% 3.04/0.98      | ~ l1_pre_topc(sK3)
% 3.04/0.98      | ~ v2_pre_topc(sK3) ),
% 3.04/0.98      inference(unflattening,[status(thm)],[c_530]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_532,plain,
% 3.04/0.98      ( v3_pre_topc(u1_struct_0(sK5),sK3) = iProver_top
% 3.04/0.98      | m1_pre_topc(sK5,sK3) != iProver_top
% 3.04/0.98      | l1_pre_topc(sK3) != iProver_top
% 3.04/0.98      | v2_pre_topc(sK3) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_53,plain,
% 3.04/0.98      ( r1_tmap_1(sK3,sK2,sK4,sK6) != iProver_top
% 3.04/0.98      | r1_tmap_1(sK5,sK2,k2_tmap_1(sK3,sK2,sK4,sK5),sK7) != iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_24,negated_conjecture,
% 3.04/0.98      ( m1_subset_1(sK7,u1_struct_0(sK5)) ),
% 3.04/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_51,plain,
% 3.04/0.98      ( m1_subset_1(sK7,u1_struct_0(sK5)) = iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_25,negated_conjecture,
% 3.04/0.98      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 3.04/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_50,plain,
% 3.04/0.98      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_49,plain,
% 3.04/0.98      ( m1_pre_topc(sK5,sK3) = iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_43,plain,
% 3.04/0.98      ( l1_pre_topc(sK3) = iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(c_42,plain,
% 3.04/0.98      ( v2_pre_topc(sK3) = iProver_top ),
% 3.04/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.04/0.98  
% 3.04/0.98  cnf(contradiction,plain,
% 3.04/0.98      ( $false ),
% 3.04/0.98      inference(minisat,
% 3.04/0.98                [status(thm)],
% 3.04/0.98                [c_15246,c_15237,c_13931,c_13798,c_13723,c_13672,c_13670,
% 3.04/0.98                 c_13666,c_13664,c_13613,c_13403,c_13404,c_13323,c_13314,
% 3.04/0.98                 c_13081,c_13078,c_12637,c_12626,c_11445,c_11480,c_917,
% 3.04/0.98                 c_532,c_53,c_51,c_50,c_49,c_43,c_42]) ).
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.04/0.98  
% 3.04/0.98  ------                               Statistics
% 3.04/0.98  
% 3.04/0.98  ------ General
% 3.04/0.98  
% 3.04/0.98  abstr_ref_over_cycles:                  0
% 3.04/0.98  abstr_ref_under_cycles:                 0
% 3.04/0.98  gc_basic_clause_elim:                   0
% 3.04/0.98  forced_gc_time:                         0
% 3.04/0.98  parsing_time:                           0.011
% 3.04/0.98  unif_index_cands_time:                  0.
% 3.04/0.98  unif_index_add_time:                    0.
% 3.04/0.98  orderings_time:                         0.
% 3.04/0.98  out_proof_time:                         0.016
% 3.04/0.98  total_time:                             0.35
% 3.04/0.98  num_of_symbols:                         63
% 3.04/0.98  num_of_terms:                           6999
% 3.04/0.98  
% 3.04/0.98  ------ Preprocessing
% 3.04/0.98  
% 3.04/0.98  num_of_splits:                          4
% 3.04/0.98  num_of_split_atoms:                     4
% 3.04/0.98  num_of_reused_defs:                     0
% 3.04/0.98  num_eq_ax_congr_red:                    26
% 3.04/0.98  num_of_sem_filtered_clauses:            1
% 3.04/0.98  num_of_subtypes:                        2
% 3.04/0.98  monotx_restored_types:                  0
% 3.04/0.98  sat_num_of_epr_types:                   0
% 3.04/0.98  sat_num_of_non_cyclic_types:            0
% 3.04/0.98  sat_guarded_non_collapsed_types:        0
% 3.04/0.98  num_pure_diseq_elim:                    0
% 3.04/0.98  simp_replaced_by:                       0
% 3.04/0.98  res_preprocessed:                       156
% 3.04/0.98  prep_upred:                             0
% 3.04/0.98  prep_unflattend:                        533
% 3.04/0.98  smt_new_axioms:                         0
% 3.04/0.98  pred_elim_cands:                        14
% 3.04/0.98  pred_elim:                              7
% 3.04/0.98  pred_elim_cl:                           -7
% 3.04/0.98  pred_elim_cycles:                       17
% 3.04/0.98  merged_defs:                            6
% 3.04/0.98  merged_defs_ncl:                        0
% 3.04/0.98  bin_hyper_res:                          6
% 3.04/0.98  prep_cycles:                            3
% 3.04/0.98  pred_elim_time:                         0.203
% 3.04/0.98  splitting_time:                         0.
% 3.04/0.98  sem_filter_time:                        0.
% 3.04/0.98  monotx_time:                            0.
% 3.04/0.98  subtype_inf_time:                       0.
% 3.04/0.98  
% 3.04/0.98  ------ Problem properties
% 3.04/0.98  
% 3.04/0.98  clauses:                                48
% 3.04/0.98  conjectures:                            6
% 3.04/0.98  epr:                                    2
% 3.04/0.98  horn:                                   46
% 3.04/0.98  ground:                                 12
% 3.04/0.98  unary:                                  6
% 3.04/0.98  binary:                                 6
% 3.04/0.98  lits:                                   162
% 3.04/0.98  lits_eq:                                7
% 3.04/0.98  fd_pure:                                0
% 3.04/0.98  fd_pseudo:                              0
% 3.04/0.98  fd_cond:                                0
% 3.04/0.98  fd_pseudo_cond:                         0
% 3.04/0.98  ac_symbols:                             0
% 3.04/0.98  
% 3.04/0.98  ------ Propositional Solver
% 3.04/0.98  
% 3.04/0.98  prop_solver_calls:                      23
% 3.04/0.98  prop_fast_solver_calls:                 4297
% 3.04/0.98  smt_solver_calls:                       0
% 3.04/0.98  smt_fast_solver_calls:                  0
% 3.04/0.98  prop_num_of_clauses:                    3297
% 3.04/0.98  prop_preprocess_simplified:             7597
% 3.04/0.98  prop_fo_subsumed:                       193
% 3.04/0.98  prop_solver_time:                       0.
% 3.04/0.98  smt_solver_time:                        0.
% 3.04/0.98  smt_fast_solver_time:                   0.
% 3.04/0.98  prop_fast_solver_time:                  0.
% 3.04/0.98  prop_unsat_core_time:                   0.
% 3.04/0.98  
% 3.04/0.98  ------ QBF
% 3.04/0.98  
% 3.04/0.98  qbf_q_res:                              0
% 3.04/0.98  qbf_num_tautologies:                    0
% 3.04/0.98  qbf_prep_cycles:                        0
% 3.04/0.98  
% 3.04/0.98  ------ BMC1
% 3.04/0.98  
% 3.04/0.98  bmc1_current_bound:                     -1
% 3.04/0.98  bmc1_last_solved_bound:                 -1
% 3.04/0.98  bmc1_unsat_core_size:                   -1
% 3.04/0.98  bmc1_unsat_core_parents_size:           -1
% 3.04/0.98  bmc1_merge_next_fun:                    0
% 3.04/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.04/0.98  
% 3.04/0.98  ------ Instantiation
% 3.04/0.98  
% 3.04/0.98  inst_num_of_clauses:                    491
% 3.04/0.98  inst_num_in_passive:                    9
% 3.04/0.98  inst_num_in_active:                     331
% 3.04/0.98  inst_num_in_unprocessed:                151
% 3.04/0.98  inst_num_of_loops:                      340
% 3.04/0.98  inst_num_of_learning_restarts:          0
% 3.04/0.98  inst_num_moves_active_passive:          6
% 3.04/0.98  inst_lit_activity:                      0
% 3.04/0.98  inst_lit_activity_moves:                0
% 3.04/0.98  inst_num_tautologies:                   0
% 3.04/0.98  inst_num_prop_implied:                  0
% 3.04/0.98  inst_num_existing_simplified:           0
% 3.04/0.98  inst_num_eq_res_simplified:             0
% 3.04/0.98  inst_num_child_elim:                    0
% 3.04/0.98  inst_num_of_dismatching_blockings:      7
% 3.04/0.98  inst_num_of_non_proper_insts:           409
% 3.04/0.98  inst_num_of_duplicates:                 0
% 3.04/0.98  inst_inst_num_from_inst_to_res:         0
% 3.04/0.98  inst_dismatching_checking_time:         0.
% 3.04/0.98  
% 3.04/0.98  ------ Resolution
% 3.04/0.98  
% 3.04/0.98  res_num_of_clauses:                     0
% 3.04/0.98  res_num_in_passive:                     0
% 3.04/0.98  res_num_in_active:                      0
% 3.04/0.98  res_num_of_loops:                       159
% 3.04/0.98  res_forward_subset_subsumed:            40
% 3.04/0.98  res_backward_subset_subsumed:           1
% 3.04/0.98  res_forward_subsumed:                   8
% 3.04/0.98  res_backward_subsumed:                  2
% 3.04/0.98  res_forward_subsumption_resolution:     37
% 3.04/0.98  res_backward_subsumption_resolution:    0
% 3.04/0.98  res_clause_to_clause_subsumption:       1160
% 3.04/0.98  res_orphan_elimination:                 0
% 3.04/0.98  res_tautology_del:                      113
% 3.04/0.98  res_num_eq_res_simplified:              2
% 3.04/0.98  res_num_sel_changes:                    0
% 3.04/0.98  res_moves_from_active_to_pass:          0
% 3.04/0.98  
% 3.04/0.98  ------ Superposition
% 3.04/0.98  
% 3.04/0.98  sup_time_total:                         0.
% 3.04/0.98  sup_time_generating:                    0.
% 3.04/0.98  sup_time_sim_full:                      0.
% 3.04/0.98  sup_time_sim_immed:                     0.
% 3.04/0.98  
% 3.04/0.98  sup_num_of_clauses:                     88
% 3.04/0.98  sup_num_in_active:                      66
% 3.04/0.98  sup_num_in_passive:                     22
% 3.04/0.98  sup_num_of_loops:                       66
% 3.04/0.98  sup_fw_superposition:                   24
% 3.04/0.98  sup_bw_superposition:                   20
% 3.04/0.98  sup_immediate_simplified:               1
% 3.04/0.98  sup_given_eliminated:                   0
% 3.04/0.98  comparisons_done:                       0
% 3.04/0.98  comparisons_avoided:                    0
% 3.04/0.98  
% 3.04/0.98  ------ Simplifications
% 3.04/0.98  
% 3.04/0.98  
% 3.04/0.98  sim_fw_subset_subsumed:                 1
% 3.04/0.98  sim_bw_subset_subsumed:                 1
% 3.04/0.98  sim_fw_subsumed:                        0
% 3.04/0.98  sim_bw_subsumed:                        0
% 3.04/0.98  sim_fw_subsumption_res:                 0
% 3.04/0.98  sim_bw_subsumption_res:                 0
% 3.04/0.98  sim_tautology_del:                      1
% 3.04/0.98  sim_eq_tautology_del:                   0
% 3.04/0.98  sim_eq_res_simp:                        2
% 3.04/0.98  sim_fw_demodulated:                     0
% 3.04/0.98  sim_bw_demodulated:                     0
% 3.04/0.98  sim_light_normalised:                   3
% 3.04/0.98  sim_joinable_taut:                      0
% 3.04/0.98  sim_joinable_simp:                      0
% 3.04/0.98  sim_ac_normalised:                      0
% 3.04/0.98  sim_smt_subsumption:                    0
% 3.04/0.98  
%------------------------------------------------------------------------------
