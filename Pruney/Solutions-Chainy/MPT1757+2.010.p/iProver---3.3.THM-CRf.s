%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:42 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  244 (1117 expanded)
%              Number of clauses        :  150 ( 207 expanded)
%              Number of leaves         :   26 ( 438 expanded)
%              Depth                    :   26
%              Number of atoms          : 1584 (17160 expanded)
%              Number of equality atoms :  151 (1248 expanded)
%              Maximal formula depth    :   27 (   7 average)
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
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | ~ r1_tmap_1(X1,X0,X2,X4) )
          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | r1_tmap_1(X1,X0,X2,X4) )
          & X4 = X5
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6)
          | ~ r1_tmap_1(X1,X0,X2,X4) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6)
          | r1_tmap_1(X1,X0,X2,X4) )
        & sK6 = X4
        & m1_subset_1(sK6,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
              | ~ r1_tmap_1(X1,X0,X2,sK5) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | r1_tmap_1(X1,X0,X2,sK5) )
            & sK5 = X5
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_subset_1(sK5,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
                ( ( ~ r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5)
                  | ~ r1_tmap_1(X1,X0,X2,X4) )
                & ( r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5)
                  | r1_tmap_1(X1,X0,X2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(sK4)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_pre_topc(sK4,X1)
        & v1_tsep_1(sK4,X1)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
                    ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5)
                      | ~ r1_tmap_1(X1,X0,sK3,X4) )
                    & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5)
                      | r1_tmap_1(X1,X0,sK3,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_pre_topc(X3,X1)
            & v1_tsep_1(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5)
                          | ~ r1_tmap_1(sK2,X0,X2,X4) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5)
                          | r1_tmap_1(sK2,X0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(sK2)) )
                & m1_pre_topc(X3,sK2)
                & v1_tsep_1(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
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
                          ( ( ~ r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK1,X2,X4) )
                          & ( r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5)
                            | r1_tmap_1(X1,sK1,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
      | ~ r1_tmap_1(sK2,sK1,sK3,sK5) )
    & ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
      | r1_tmap_1(sK2,sK1,sK3,sK5) )
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_pre_topc(sK4,sK2)
    & v1_tsep_1(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f51,f57,f56,f55,f54,f53,f52])).

fof(f90,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f58])).

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
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
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

fof(f42,plain,(
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
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
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
    inference(flattening,[],[f41])).

fof(f49,plain,(
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
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
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
    inference(nnf_transformation,[],[f42])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ m1_connsp_2(X4,X1,X5)
      | ~ r1_tarski(X4,u1_struct_0(X3))
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
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ m1_connsp_2(X4,X1,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
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
    inference(equality_resolution,[],[f78])).

fof(f86,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

fof(f85,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

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
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f83,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f84,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f88,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f80,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f58])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_connsp_2(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK0(X0,X1,X2),X2)
        & v3_pre_topc(sK0(X0,X1,X2),X0)
        & m1_connsp_2(sK0(X0,X1,X2),X0,X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(sK0(X0,X1,X2),X2)
                & v3_pre_topc(sK0(X0,X1,X2),X0)
                & m1_connsp_2(sK0(X0,X1,X2),X0,X1)
                & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f45])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK0(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK0(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
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
    inference(equality_resolution,[],[f76])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f93,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f58])).

fof(f95,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ r1_tmap_1(sK2,sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f47,plain,(
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

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f89,plain,(
    v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f94,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | r1_tmap_1(sK2,sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f92,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_18,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_618,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_619,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_623,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_619,c_30])).

cnf(c_624,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_623])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_665,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_624,c_4])).

cnf(c_881,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_665])).

cnf(c_882,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_881])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_886,plain,
    ( ~ v2_pre_topc(X0)
    | r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_882,c_33,c_32,c_31,c_27])).

cnf(c_887,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_886])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1573,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_887,c_35])).

cnf(c_1574,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_connsp_2(X1,sK2,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1573])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1578,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | ~ m1_connsp_2(X1,sK2,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | r1_tmap_1(sK2,sK1,sK3,X0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1574,c_36,c_34,c_28])).

cnf(c_1579,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_connsp_2(X1,sK2,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1578])).

cnf(c_2505,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0_54)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
    | ~ m1_connsp_2(X1_54,sK2,X0_54)
    | ~ r1_tarski(X1_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_1579])).

cnf(c_2776,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0_54)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
    | ~ m1_connsp_2(X1_54,sK2,X0_54)
    | ~ r1_tarski(X1_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(equality_resolution_simp,[status(thm)],[c_2505])).

cnf(c_5033,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0_54)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
    | ~ m1_connsp_2(sK0(sK2,sK6,u1_struct_0(sK4)),sK2,X0_54)
    | ~ r1_tarski(sK0(sK2,sK6,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK2,sK6,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_2776])).

cnf(c_5555,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ m1_connsp_2(sK0(sK2,sK6,u1_struct_0(sK4)),sK2,sK6)
    | ~ r1_tarski(sK0(sK2,sK6,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK2,sK6,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5033])).

cnf(c_2561,plain,
    ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
    | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_4599,plain,
    ( r1_tmap_1(sK4,sK1,X0_54,X1_54)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
    | X0_54 != k2_tmap_1(sK2,sK1,sK3,sK4)
    | X1_54 != sK5 ),
    inference(instantiation,[status(thm)],[c_2561])).

cnf(c_5143,plain,
    ( r1_tmap_1(sK4,sK1,X0_54,sK6)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
    | X0_54 != k2_tmap_1(sK2,sK1,sK3,sK4)
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_4599])).

cnf(c_5539,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | k2_tmap_1(sK2,sK1,sK3,sK4) != k2_tmap_1(sK2,sK1,sK3,sK4)
    | sK6 != sK5 ),
    inference(instantiation,[status(thm)],[c_5143])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_6,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_235,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_6])).

cnf(c_236,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_235])).

cnf(c_1000,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_236,c_32])).

cnf(c_1001,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | r1_tarski(sK0(sK2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1000])).

cnf(c_1005,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | r1_tarski(sK0(sK2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1001,c_33,c_31])).

cnf(c_2531,plain,
    ( ~ m1_connsp_2(X0_54,sK2,X1_54)
    | r1_tarski(sK0(sK2,X1_54,X0_54),X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1005])).

cnf(c_4163,plain,
    ( ~ m1_connsp_2(X0_54,sK2,sK6)
    | r1_tarski(sK0(sK2,sK6,X0_54),X0_54)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2531])).

cnf(c_4860,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK6)
    | r1_tarski(sK0(sK2,sK6,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4163])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_6])).

cnf(c_215,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_1063,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_215,c_32])).

cnf(c_1064,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1063])).

cnf(c_1068,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1064,c_33,c_31])).

cnf(c_2528,plain,
    ( ~ m1_connsp_2(X0_54,sK2,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X1_54,X0_54),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_1068])).

cnf(c_4166,plain,
    ( ~ m1_connsp_2(X0_54,sK2,sK6)
    | m1_subset_1(sK0(sK2,sK6,X0_54),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2528])).

cnf(c_4862,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK6)
    | m1_subset_1(sK0(sK2,sK6,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4166])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_221,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_6])).

cnf(c_222,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_221])).

cnf(c_1042,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_222,c_32])).

cnf(c_1043,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | m1_connsp_2(sK0(sK2,X1,X0),sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1042])).

cnf(c_1047,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | m1_connsp_2(sK0(sK2,X1,X0),sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1043,c_33,c_31])).

cnf(c_2529,plain,
    ( ~ m1_connsp_2(X0_54,sK2,X1_54)
    | m1_connsp_2(sK0(sK2,X1_54,X0_54),sK2,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1047])).

cnf(c_4164,plain,
    ( ~ m1_connsp_2(X0_54,sK2,sK6)
    | m1_connsp_2(sK0(sK2,sK6,X0_54),sK2,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2529])).

cnf(c_4864,plain,
    ( m1_connsp_2(sK0(sK2,sK6,u1_struct_0(sK4)),sK2,sK6)
    | ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4164])).

cnf(c_8,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1084,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_32])).

cnf(c_1085,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1084])).

cnf(c_1089,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1085,c_33,c_31])).

cnf(c_1,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1105,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1089,c_1])).

cnf(c_2527,plain,
    ( m1_connsp_2(X0_54,sK2,X1_54)
    | ~ v3_pre_topc(X0_54,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_1105])).

cnf(c_4073,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK2,X0_54)
    | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0_54,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_4630,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK2,sK6)
    | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4073])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f99])).

cnf(c_684,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
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
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_685,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_689,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_685,c_30])).

cnf(c_690,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_689])).

cnf(c_725,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_690,c_4])).

cnf(c_842,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_725])).

cnf(c_843,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_842])).

cnf(c_847,plain,
    ( ~ v2_pre_topc(X0)
    | ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_843,c_33,c_32,c_31,c_27])).

cnf(c_848,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_847])).

cnf(c_1606,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_848,c_35])).

cnf(c_1607,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1606])).

cnf(c_1611,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1607,c_36,c_34,c_28])).

cnf(c_1612,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1611])).

cnf(c_2504,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0_54)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_1612])).

cnf(c_2780,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0_54)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2504])).

cnf(c_4536,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2780])).

cnf(c_2553,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_4261,plain,
    ( X0_54 != X1_54
    | X0_54 = sK5
    | sK5 != X1_54 ),
    inference(instantiation,[status(thm)],[c_2553])).

cnf(c_4490,plain,
    ( X0_54 = sK5
    | X0_54 != sK6
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_4261])).

cnf(c_4535,plain,
    ( sK5 != sK6
    | sK6 = sK5
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4490])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2542,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ r2_hidden(X2_54,X0_54)
    | r2_hidden(X2_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_4224,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(X0_54))
    | r2_hidden(sK6,X0_54)
    | ~ r2_hidden(sK6,k1_connsp_2(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_2542])).

cnf(c_4393,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK6,k1_connsp_2(sK4,sK6))
    | r2_hidden(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4224])).

cnf(c_2552,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_4331,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK4) = k2_tmap_1(sK2,sK1,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2552])).

cnf(c_4147,plain,
    ( r1_tmap_1(sK4,sK1,X0_54,X1_54)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | X0_54 != k2_tmap_1(sK2,sK1,sK3,sK4)
    | X1_54 != sK6 ),
    inference(instantiation,[status(thm)],[c_2561])).

cnf(c_4276,plain,
    ( r1_tmap_1(sK4,sK1,X0_54,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | X0_54 != k2_tmap_1(sK2,sK1,sK3,sK4)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_4147])).

cnf(c_4330,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | k2_tmap_1(sK2,sK1,sK3,sK4) != k2_tmap_1(sK2,sK1,sK3,sK4)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_4276])).

cnf(c_4326,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2552])).

cnf(c_2556,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | m1_subset_1(X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_4127,plain,
    ( m1_subset_1(X0_54,X1_54)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | X1_54 != u1_struct_0(sK4)
    | X0_54 != sK6 ),
    inference(instantiation,[status(thm)],[c_2556])).

cnf(c_4242,plain,
    ( m1_subset_1(sK5,X0_54)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | X0_54 != u1_struct_0(sK4)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_4127])).

cnf(c_4325,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_4242])).

cnf(c_4248,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_2552])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_831,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_25])).

cnf(c_832,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_831])).

cnf(c_834,plain,
    ( v2_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_832,c_32,c_31])).

cnf(c_1453,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_834])).

cnf(c_1454,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k1_connsp_2(sK4,X0))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1453])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_820,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_821,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_820])).

cnf(c_1458,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k1_connsp_2(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1454,c_31,c_27,c_821])).

cnf(c_2510,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | r2_hidden(X0_54,k1_connsp_2(sK4,X0_54)) ),
    inference(subtyping,[status(esa)],[c_1458])).

cnf(c_4038,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | r2_hidden(sK6,k1_connsp_2(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_2510])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1492,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_834])).

cnf(c_1493,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1492])).

cnf(c_1497,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1493,c_31,c_27,c_821])).

cnf(c_2508,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | m1_subset_1(k1_connsp_2(sK4,X0_54),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_1497])).

cnf(c_4035,plain,
    ( m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2508])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2536,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3588,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2536])).

cnf(c_22,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2538,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_3631,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3588,c_2538])).

cnf(c_3928,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3631])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2540,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_3585,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2540])).

cnf(c_3685,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3585,c_2538])).

cnf(c_3896,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3685])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_791,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_792,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_791])).

cnf(c_15,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_200,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_16])).

cnf(c_201,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_200])).

cnf(c_26,negated_conjecture,
    ( v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_483,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_201,c_26])).

cnf(c_484,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_21,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,sK3,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f92])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5555,c_5539,c_4860,c_4862,c_4864,c_4630,c_4536,c_4535,c_4393,c_4331,c_4330,c_4326,c_4325,c_4248,c_4038,c_4035,c_3928,c_3896,c_2538,c_792,c_484,c_21,c_23,c_25,c_31,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n008.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 20:00:30 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.05/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.05/0.98  
% 2.05/0.98  ------  iProver source info
% 2.05/0.98  
% 2.05/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.05/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.05/0.98  git: non_committed_changes: false
% 2.05/0.98  git: last_make_outside_of_git: false
% 2.05/0.98  
% 2.05/0.98  ------ 
% 2.05/0.98  
% 2.05/0.98  ------ Input Options
% 2.05/0.98  
% 2.05/0.98  --out_options                           all
% 2.05/0.98  --tptp_safe_out                         true
% 2.05/0.98  --problem_path                          ""
% 2.05/0.98  --include_path                          ""
% 2.05/0.98  --clausifier                            res/vclausify_rel
% 2.05/0.98  --clausifier_options                    --mode clausify
% 2.05/0.98  --stdin                                 false
% 2.05/0.98  --stats_out                             all
% 2.05/0.98  
% 2.05/0.98  ------ General Options
% 2.05/0.98  
% 2.05/0.98  --fof                                   false
% 2.05/0.98  --time_out_real                         305.
% 2.05/0.98  --time_out_virtual                      -1.
% 2.05/0.98  --symbol_type_check                     false
% 2.05/0.98  --clausify_out                          false
% 2.05/0.98  --sig_cnt_out                           false
% 2.05/0.98  --trig_cnt_out                          false
% 2.05/0.98  --trig_cnt_out_tolerance                1.
% 2.05/0.98  --trig_cnt_out_sk_spl                   false
% 2.05/0.98  --abstr_cl_out                          false
% 2.05/0.98  
% 2.05/0.98  ------ Global Options
% 2.05/0.98  
% 2.05/0.98  --schedule                              default
% 2.05/0.98  --add_important_lit                     false
% 2.05/0.98  --prop_solver_per_cl                    1000
% 2.05/0.98  --min_unsat_core                        false
% 2.05/0.98  --soft_assumptions                      false
% 2.05/0.98  --soft_lemma_size                       3
% 2.05/0.98  --prop_impl_unit_size                   0
% 2.05/0.98  --prop_impl_unit                        []
% 2.05/0.98  --share_sel_clauses                     true
% 2.05/0.98  --reset_solvers                         false
% 2.05/0.98  --bc_imp_inh                            [conj_cone]
% 2.05/0.98  --conj_cone_tolerance                   3.
% 2.05/0.98  --extra_neg_conj                        none
% 2.05/0.98  --large_theory_mode                     true
% 2.05/0.98  --prolific_symb_bound                   200
% 2.05/0.98  --lt_threshold                          2000
% 2.05/0.98  --clause_weak_htbl                      true
% 2.05/0.98  --gc_record_bc_elim                     false
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing Options
% 2.05/0.98  
% 2.05/0.98  --preprocessing_flag                    true
% 2.05/0.98  --time_out_prep_mult                    0.1
% 2.05/0.98  --splitting_mode                        input
% 2.05/0.98  --splitting_grd                         true
% 2.05/0.98  --splitting_cvd                         false
% 2.05/0.98  --splitting_cvd_svl                     false
% 2.05/0.98  --splitting_nvd                         32
% 2.05/0.98  --sub_typing                            true
% 2.05/0.98  --prep_gs_sim                           true
% 2.05/0.98  --prep_unflatten                        true
% 2.05/0.98  --prep_res_sim                          true
% 2.05/0.98  --prep_upred                            true
% 2.05/0.98  --prep_sem_filter                       exhaustive
% 2.05/0.98  --prep_sem_filter_out                   false
% 2.05/0.98  --pred_elim                             true
% 2.05/0.98  --res_sim_input                         true
% 2.05/0.98  --eq_ax_congr_red                       true
% 2.05/0.98  --pure_diseq_elim                       true
% 2.05/0.98  --brand_transform                       false
% 2.05/0.98  --non_eq_to_eq                          false
% 2.05/0.98  --prep_def_merge                        true
% 2.05/0.98  --prep_def_merge_prop_impl              false
% 2.05/0.98  --prep_def_merge_mbd                    true
% 2.05/0.98  --prep_def_merge_tr_red                 false
% 2.05/0.98  --prep_def_merge_tr_cl                  false
% 2.05/0.98  --smt_preprocessing                     true
% 2.05/0.98  --smt_ac_axioms                         fast
% 2.05/0.98  --preprocessed_out                      false
% 2.05/0.98  --preprocessed_stats                    false
% 2.05/0.98  
% 2.05/0.98  ------ Abstraction refinement Options
% 2.05/0.98  
% 2.05/0.98  --abstr_ref                             []
% 2.05/0.98  --abstr_ref_prep                        false
% 2.05/0.98  --abstr_ref_until_sat                   false
% 2.05/0.98  --abstr_ref_sig_restrict                funpre
% 2.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.98  --abstr_ref_under                       []
% 2.05/0.98  
% 2.05/0.98  ------ SAT Options
% 2.05/0.98  
% 2.05/0.98  --sat_mode                              false
% 2.05/0.98  --sat_fm_restart_options                ""
% 2.05/0.98  --sat_gr_def                            false
% 2.05/0.98  --sat_epr_types                         true
% 2.05/0.98  --sat_non_cyclic_types                  false
% 2.05/0.98  --sat_finite_models                     false
% 2.05/0.98  --sat_fm_lemmas                         false
% 2.05/0.98  --sat_fm_prep                           false
% 2.05/0.98  --sat_fm_uc_incr                        true
% 2.05/0.98  --sat_out_model                         small
% 2.05/0.98  --sat_out_clauses                       false
% 2.05/0.98  
% 2.05/0.98  ------ QBF Options
% 2.05/0.98  
% 2.05/0.98  --qbf_mode                              false
% 2.05/0.98  --qbf_elim_univ                         false
% 2.05/0.98  --qbf_dom_inst                          none
% 2.05/0.98  --qbf_dom_pre_inst                      false
% 2.05/0.98  --qbf_sk_in                             false
% 2.05/0.98  --qbf_pred_elim                         true
% 2.05/0.98  --qbf_split                             512
% 2.05/0.98  
% 2.05/0.98  ------ BMC1 Options
% 2.05/0.98  
% 2.05/0.98  --bmc1_incremental                      false
% 2.05/0.98  --bmc1_axioms                           reachable_all
% 2.05/0.98  --bmc1_min_bound                        0
% 2.05/0.98  --bmc1_max_bound                        -1
% 2.05/0.98  --bmc1_max_bound_default                -1
% 2.05/0.98  --bmc1_symbol_reachability              true
% 2.05/0.98  --bmc1_property_lemmas                  false
% 2.05/0.98  --bmc1_k_induction                      false
% 2.05/0.98  --bmc1_non_equiv_states                 false
% 2.05/0.98  --bmc1_deadlock                         false
% 2.05/0.98  --bmc1_ucm                              false
% 2.05/0.98  --bmc1_add_unsat_core                   none
% 2.05/0.98  --bmc1_unsat_core_children              false
% 2.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.98  --bmc1_out_stat                         full
% 2.05/0.98  --bmc1_ground_init                      false
% 2.05/0.98  --bmc1_pre_inst_next_state              false
% 2.05/0.98  --bmc1_pre_inst_state                   false
% 2.05/0.98  --bmc1_pre_inst_reach_state             false
% 2.05/0.98  --bmc1_out_unsat_core                   false
% 2.05/0.98  --bmc1_aig_witness_out                  false
% 2.05/0.98  --bmc1_verbose                          false
% 2.05/0.98  --bmc1_dump_clauses_tptp                false
% 2.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.98  --bmc1_dump_file                        -
% 2.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.98  --bmc1_ucm_extend_mode                  1
% 2.05/0.98  --bmc1_ucm_init_mode                    2
% 2.05/0.98  --bmc1_ucm_cone_mode                    none
% 2.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.98  --bmc1_ucm_relax_model                  4
% 2.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.98  --bmc1_ucm_layered_model                none
% 2.05/0.98  --bmc1_ucm_max_lemma_size               10
% 2.05/0.98  
% 2.05/0.98  ------ AIG Options
% 2.05/0.98  
% 2.05/0.98  --aig_mode                              false
% 2.05/0.98  
% 2.05/0.98  ------ Instantiation Options
% 2.05/0.98  
% 2.05/0.98  --instantiation_flag                    true
% 2.05/0.98  --inst_sos_flag                         false
% 2.05/0.98  --inst_sos_phase                        true
% 2.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel_side                     num_symb
% 2.05/0.98  --inst_solver_per_active                1400
% 2.05/0.98  --inst_solver_calls_frac                1.
% 2.05/0.98  --inst_passive_queue_type               priority_queues
% 2.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.98  --inst_passive_queues_freq              [25;2]
% 2.05/0.98  --inst_dismatching                      true
% 2.05/0.98  --inst_eager_unprocessed_to_passive     true
% 2.05/0.98  --inst_prop_sim_given                   true
% 2.05/0.98  --inst_prop_sim_new                     false
% 2.05/0.98  --inst_subs_new                         false
% 2.05/0.98  --inst_eq_res_simp                      false
% 2.05/0.98  --inst_subs_given                       false
% 2.05/0.98  --inst_orphan_elimination               true
% 2.05/0.98  --inst_learning_loop_flag               true
% 2.05/0.98  --inst_learning_start                   3000
% 2.05/0.98  --inst_learning_factor                  2
% 2.05/0.98  --inst_start_prop_sim_after_learn       3
% 2.05/0.98  --inst_sel_renew                        solver
% 2.05/0.98  --inst_lit_activity_flag                true
% 2.05/0.98  --inst_restr_to_given                   false
% 2.05/0.98  --inst_activity_threshold               500
% 2.05/0.98  --inst_out_proof                        true
% 2.05/0.98  
% 2.05/0.98  ------ Resolution Options
% 2.05/0.98  
% 2.05/0.98  --resolution_flag                       true
% 2.05/0.98  --res_lit_sel                           adaptive
% 2.05/0.98  --res_lit_sel_side                      none
% 2.05/0.98  --res_ordering                          kbo
% 2.05/0.98  --res_to_prop_solver                    active
% 2.05/0.98  --res_prop_simpl_new                    false
% 2.05/0.98  --res_prop_simpl_given                  true
% 2.05/0.98  --res_passive_queue_type                priority_queues
% 2.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.98  --res_passive_queues_freq               [15;5]
% 2.05/0.98  --res_forward_subs                      full
% 2.05/0.98  --res_backward_subs                     full
% 2.05/0.98  --res_forward_subs_resolution           true
% 2.05/0.98  --res_backward_subs_resolution          true
% 2.05/0.98  --res_orphan_elimination                true
% 2.05/0.98  --res_time_limit                        2.
% 2.05/0.98  --res_out_proof                         true
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Options
% 2.05/0.98  
% 2.05/0.98  --superposition_flag                    true
% 2.05/0.98  --sup_passive_queue_type                priority_queues
% 2.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.98  --demod_completeness_check              fast
% 2.05/0.98  --demod_use_ground                      true
% 2.05/0.98  --sup_to_prop_solver                    passive
% 2.05/0.98  --sup_prop_simpl_new                    true
% 2.05/0.98  --sup_prop_simpl_given                  true
% 2.05/0.98  --sup_fun_splitting                     false
% 2.05/0.98  --sup_smt_interval                      50000
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Simplification Setup
% 2.05/0.98  
% 2.05/0.98  --sup_indices_passive                   []
% 2.05/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_full_bw                           [BwDemod]
% 2.05/0.98  --sup_immed_triv                        [TrivRules]
% 2.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_immed_bw_main                     []
% 2.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  
% 2.05/0.98  ------ Combination Options
% 2.05/0.98  
% 2.05/0.98  --comb_res_mult                         3
% 2.05/0.98  --comb_sup_mult                         2
% 2.05/0.98  --comb_inst_mult                        10
% 2.05/0.98  
% 2.05/0.98  ------ Debug Options
% 2.05/0.98  
% 2.05/0.98  --dbg_backtrace                         false
% 2.05/0.98  --dbg_dump_prop_clauses                 false
% 2.05/0.98  --dbg_dump_prop_clauses_file            -
% 2.05/0.98  --dbg_out_stat                          false
% 2.05/0.98  ------ Parsing...
% 2.05/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.05/0.98  ------ Proving...
% 2.05/0.98  ------ Problem Properties 
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  clauses                                 45
% 2.05/0.98  conjectures                             6
% 2.05/0.98  EPR                                     1
% 2.05/0.98  Horn                                    44
% 2.05/0.98  unary                                   6
% 2.05/0.98  binary                                  9
% 2.05/0.98  lits                                    132
% 2.05/0.98  lits eq                                 7
% 2.05/0.98  fd_pure                                 0
% 2.05/0.98  fd_pseudo                               0
% 2.05/0.98  fd_cond                                 0
% 2.05/0.98  fd_pseudo_cond                          0
% 2.05/0.98  AC symbols                              0
% 2.05/0.98  
% 2.05/0.98  ------ Schedule dynamic 5 is on 
% 2.05/0.98  
% 2.05/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  ------ 
% 2.05/0.98  Current options:
% 2.05/0.98  ------ 
% 2.05/0.98  
% 2.05/0.98  ------ Input Options
% 2.05/0.98  
% 2.05/0.98  --out_options                           all
% 2.05/0.98  --tptp_safe_out                         true
% 2.05/0.98  --problem_path                          ""
% 2.05/0.98  --include_path                          ""
% 2.05/0.98  --clausifier                            res/vclausify_rel
% 2.05/0.98  --clausifier_options                    --mode clausify
% 2.05/0.98  --stdin                                 false
% 2.05/0.98  --stats_out                             all
% 2.05/0.98  
% 2.05/0.98  ------ General Options
% 2.05/0.98  
% 2.05/0.98  --fof                                   false
% 2.05/0.98  --time_out_real                         305.
% 2.05/0.98  --time_out_virtual                      -1.
% 2.05/0.98  --symbol_type_check                     false
% 2.05/0.98  --clausify_out                          false
% 2.05/0.98  --sig_cnt_out                           false
% 2.05/0.98  --trig_cnt_out                          false
% 2.05/0.98  --trig_cnt_out_tolerance                1.
% 2.05/0.98  --trig_cnt_out_sk_spl                   false
% 2.05/0.98  --abstr_cl_out                          false
% 2.05/0.98  
% 2.05/0.98  ------ Global Options
% 2.05/0.98  
% 2.05/0.98  --schedule                              default
% 2.05/0.98  --add_important_lit                     false
% 2.05/0.98  --prop_solver_per_cl                    1000
% 2.05/0.98  --min_unsat_core                        false
% 2.05/0.98  --soft_assumptions                      false
% 2.05/0.98  --soft_lemma_size                       3
% 2.05/0.98  --prop_impl_unit_size                   0
% 2.05/0.98  --prop_impl_unit                        []
% 2.05/0.98  --share_sel_clauses                     true
% 2.05/0.98  --reset_solvers                         false
% 2.05/0.98  --bc_imp_inh                            [conj_cone]
% 2.05/0.98  --conj_cone_tolerance                   3.
% 2.05/0.98  --extra_neg_conj                        none
% 2.05/0.98  --large_theory_mode                     true
% 2.05/0.98  --prolific_symb_bound                   200
% 2.05/0.98  --lt_threshold                          2000
% 2.05/0.98  --clause_weak_htbl                      true
% 2.05/0.98  --gc_record_bc_elim                     false
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing Options
% 2.05/0.98  
% 2.05/0.98  --preprocessing_flag                    true
% 2.05/0.98  --time_out_prep_mult                    0.1
% 2.05/0.98  --splitting_mode                        input
% 2.05/0.98  --splitting_grd                         true
% 2.05/0.98  --splitting_cvd                         false
% 2.05/0.98  --splitting_cvd_svl                     false
% 2.05/0.98  --splitting_nvd                         32
% 2.05/0.98  --sub_typing                            true
% 2.05/0.98  --prep_gs_sim                           true
% 2.05/0.98  --prep_unflatten                        true
% 2.05/0.98  --prep_res_sim                          true
% 2.05/0.98  --prep_upred                            true
% 2.05/0.98  --prep_sem_filter                       exhaustive
% 2.05/0.98  --prep_sem_filter_out                   false
% 2.05/0.98  --pred_elim                             true
% 2.05/0.98  --res_sim_input                         true
% 2.05/0.98  --eq_ax_congr_red                       true
% 2.05/0.98  --pure_diseq_elim                       true
% 2.05/0.98  --brand_transform                       false
% 2.05/0.98  --non_eq_to_eq                          false
% 2.05/0.98  --prep_def_merge                        true
% 2.05/0.98  --prep_def_merge_prop_impl              false
% 2.05/0.98  --prep_def_merge_mbd                    true
% 2.05/0.98  --prep_def_merge_tr_red                 false
% 2.05/0.98  --prep_def_merge_tr_cl                  false
% 2.05/0.98  --smt_preprocessing                     true
% 2.05/0.98  --smt_ac_axioms                         fast
% 2.05/0.98  --preprocessed_out                      false
% 2.05/0.98  --preprocessed_stats                    false
% 2.05/0.98  
% 2.05/0.98  ------ Abstraction refinement Options
% 2.05/0.98  
% 2.05/0.98  --abstr_ref                             []
% 2.05/0.98  --abstr_ref_prep                        false
% 2.05/0.98  --abstr_ref_until_sat                   false
% 2.05/0.98  --abstr_ref_sig_restrict                funpre
% 2.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.98  --abstr_ref_under                       []
% 2.05/0.98  
% 2.05/0.98  ------ SAT Options
% 2.05/0.98  
% 2.05/0.98  --sat_mode                              false
% 2.05/0.98  --sat_fm_restart_options                ""
% 2.05/0.98  --sat_gr_def                            false
% 2.05/0.98  --sat_epr_types                         true
% 2.05/0.98  --sat_non_cyclic_types                  false
% 2.05/0.98  --sat_finite_models                     false
% 2.05/0.98  --sat_fm_lemmas                         false
% 2.05/0.98  --sat_fm_prep                           false
% 2.05/0.98  --sat_fm_uc_incr                        true
% 2.05/0.98  --sat_out_model                         small
% 2.05/0.98  --sat_out_clauses                       false
% 2.05/0.98  
% 2.05/0.98  ------ QBF Options
% 2.05/0.98  
% 2.05/0.98  --qbf_mode                              false
% 2.05/0.98  --qbf_elim_univ                         false
% 2.05/0.98  --qbf_dom_inst                          none
% 2.05/0.98  --qbf_dom_pre_inst                      false
% 2.05/0.98  --qbf_sk_in                             false
% 2.05/0.98  --qbf_pred_elim                         true
% 2.05/0.98  --qbf_split                             512
% 2.05/0.98  
% 2.05/0.98  ------ BMC1 Options
% 2.05/0.98  
% 2.05/0.98  --bmc1_incremental                      false
% 2.05/0.98  --bmc1_axioms                           reachable_all
% 2.05/0.98  --bmc1_min_bound                        0
% 2.05/0.98  --bmc1_max_bound                        -1
% 2.05/0.98  --bmc1_max_bound_default                -1
% 2.05/0.98  --bmc1_symbol_reachability              true
% 2.05/0.98  --bmc1_property_lemmas                  false
% 2.05/0.98  --bmc1_k_induction                      false
% 2.05/0.98  --bmc1_non_equiv_states                 false
% 2.05/0.98  --bmc1_deadlock                         false
% 2.05/0.98  --bmc1_ucm                              false
% 2.05/0.98  --bmc1_add_unsat_core                   none
% 2.05/0.98  --bmc1_unsat_core_children              false
% 2.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.98  --bmc1_out_stat                         full
% 2.05/0.98  --bmc1_ground_init                      false
% 2.05/0.98  --bmc1_pre_inst_next_state              false
% 2.05/0.98  --bmc1_pre_inst_state                   false
% 2.05/0.98  --bmc1_pre_inst_reach_state             false
% 2.05/0.98  --bmc1_out_unsat_core                   false
% 2.05/0.98  --bmc1_aig_witness_out                  false
% 2.05/0.98  --bmc1_verbose                          false
% 2.05/0.98  --bmc1_dump_clauses_tptp                false
% 2.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.98  --bmc1_dump_file                        -
% 2.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.98  --bmc1_ucm_extend_mode                  1
% 2.05/0.98  --bmc1_ucm_init_mode                    2
% 2.05/0.98  --bmc1_ucm_cone_mode                    none
% 2.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.98  --bmc1_ucm_relax_model                  4
% 2.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.98  --bmc1_ucm_layered_model                none
% 2.05/0.98  --bmc1_ucm_max_lemma_size               10
% 2.05/0.98  
% 2.05/0.98  ------ AIG Options
% 2.05/0.98  
% 2.05/0.98  --aig_mode                              false
% 2.05/0.98  
% 2.05/0.98  ------ Instantiation Options
% 2.05/0.98  
% 2.05/0.98  --instantiation_flag                    true
% 2.05/0.98  --inst_sos_flag                         false
% 2.05/0.98  --inst_sos_phase                        true
% 2.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel_side                     none
% 2.05/0.98  --inst_solver_per_active                1400
% 2.05/0.98  --inst_solver_calls_frac                1.
% 2.05/0.98  --inst_passive_queue_type               priority_queues
% 2.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.98  --inst_passive_queues_freq              [25;2]
% 2.05/0.98  --inst_dismatching                      true
% 2.05/0.98  --inst_eager_unprocessed_to_passive     true
% 2.05/0.98  --inst_prop_sim_given                   true
% 2.05/0.98  --inst_prop_sim_new                     false
% 2.05/0.98  --inst_subs_new                         false
% 2.05/0.98  --inst_eq_res_simp                      false
% 2.05/0.98  --inst_subs_given                       false
% 2.05/0.98  --inst_orphan_elimination               true
% 2.05/0.98  --inst_learning_loop_flag               true
% 2.05/0.98  --inst_learning_start                   3000
% 2.05/0.98  --inst_learning_factor                  2
% 2.05/0.98  --inst_start_prop_sim_after_learn       3
% 2.05/0.98  --inst_sel_renew                        solver
% 2.05/0.98  --inst_lit_activity_flag                true
% 2.05/0.98  --inst_restr_to_given                   false
% 2.05/0.98  --inst_activity_threshold               500
% 2.05/0.98  --inst_out_proof                        true
% 2.05/0.98  
% 2.05/0.98  ------ Resolution Options
% 2.05/0.98  
% 2.05/0.98  --resolution_flag                       false
% 2.05/0.98  --res_lit_sel                           adaptive
% 2.05/0.98  --res_lit_sel_side                      none
% 2.05/0.98  --res_ordering                          kbo
% 2.05/0.98  --res_to_prop_solver                    active
% 2.05/0.98  --res_prop_simpl_new                    false
% 2.05/0.98  --res_prop_simpl_given                  true
% 2.05/0.98  --res_passive_queue_type                priority_queues
% 2.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.98  --res_passive_queues_freq               [15;5]
% 2.05/0.98  --res_forward_subs                      full
% 2.05/0.98  --res_backward_subs                     full
% 2.05/0.98  --res_forward_subs_resolution           true
% 2.05/0.98  --res_backward_subs_resolution          true
% 2.05/0.98  --res_orphan_elimination                true
% 2.05/0.98  --res_time_limit                        2.
% 2.05/0.98  --res_out_proof                         true
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Options
% 2.05/0.98  
% 2.05/0.98  --superposition_flag                    true
% 2.05/0.98  --sup_passive_queue_type                priority_queues
% 2.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.98  --demod_completeness_check              fast
% 2.05/0.98  --demod_use_ground                      true
% 2.05/0.98  --sup_to_prop_solver                    passive
% 2.05/0.98  --sup_prop_simpl_new                    true
% 2.05/0.98  --sup_prop_simpl_given                  true
% 2.05/0.98  --sup_fun_splitting                     false
% 2.05/0.98  --sup_smt_interval                      50000
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Simplification Setup
% 2.05/0.98  
% 2.05/0.98  --sup_indices_passive                   []
% 2.05/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_full_bw                           [BwDemod]
% 2.05/0.98  --sup_immed_triv                        [TrivRules]
% 2.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_immed_bw_main                     []
% 2.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  
% 2.05/0.98  ------ Combination Options
% 2.05/0.98  
% 2.05/0.98  --comb_res_mult                         3
% 2.05/0.98  --comb_sup_mult                         2
% 2.05/0.98  --comb_inst_mult                        10
% 2.05/0.98  
% 2.05/0.98  ------ Debug Options
% 2.05/0.98  
% 2.05/0.98  --dbg_backtrace                         false
% 2.05/0.98  --dbg_dump_prop_clauses                 false
% 2.05/0.98  --dbg_dump_prop_clauses_file            -
% 2.05/0.98  --dbg_out_stat                          false
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  ------ Proving...
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  % SZS status Theorem for theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  fof(f15,conjecture,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f16,negated_conjecture,(
% 2.05/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.05/0.98    inference(negated_conjecture,[],[f15])).
% 2.05/0.98  
% 2.05/0.98  fof(f43,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f16])).
% 2.05/0.98  
% 2.05/0.98  fof(f44,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f43])).
% 2.05/0.98  
% 2.05/0.98  fof(f50,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.98    inference(nnf_transformation,[],[f44])).
% 2.05/0.98  
% 2.05/0.98  fof(f51,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f50])).
% 2.05/0.98  
% 2.05/0.98  fof(f57,plain,(
% 2.05/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | r1_tmap_1(X1,X0,X2,X4)) & sK6 = X4 & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f56,plain,(
% 2.05/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK5)) & sK5 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f55,plain,(
% 2.05/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK4,X1) & v1_tsep_1(sK4,X1) & ~v2_struct_0(sK4))) )),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f54,plain,(
% 2.05/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5) | ~r1_tmap_1(X1,X0,sK3,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5) | r1_tmap_1(X1,X0,sK3,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f53,plain,(
% 2.05/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5) | ~r1_tmap_1(sK2,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5) | r1_tmap_1(sK2,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK2))) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f52,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5) | ~r1_tmap_1(X1,sK1,X2,X4)) & (r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5) | r1_tmap_1(X1,sK1,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f58,plain,(
% 2.05/0.98    ((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | ~r1_tmap_1(sK2,sK1,sK3,sK5)) & (r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | r1_tmap_1(sK2,sK1,sK3,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_pre_topc(sK4,sK2) & v1_tsep_1(sK4,sK2) & ~v2_struct_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f51,f57,f56,f55,f54,f53,f52])).
% 2.05/0.98  
% 2.05/0.98  fof(f90,plain,(
% 2.05/0.98    m1_pre_topc(sK4,sK2)),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f14,axiom,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f41,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f14])).
% 2.05/0.98  
% 2.05/0.98  fof(f42,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f41])).
% 2.05/0.98  
% 2.05/0.98  fof(f49,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(nnf_transformation,[],[f42])).
% 2.05/0.98  
% 2.05/0.98  fof(f78,plain,(
% 2.05/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f49])).
% 2.05/0.98  
% 2.05/0.98  fof(f100,plain,(
% 2.05/0.98    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(equality_resolution,[],[f78])).
% 2.05/0.98  
% 2.05/0.98  fof(f86,plain,(
% 2.05/0.98    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f85,plain,(
% 2.05/0.98    v1_funct_1(sK3)),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f5,axiom,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f24,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f5])).
% 2.05/0.98  
% 2.05/0.98  fof(f25,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f24])).
% 2.05/0.98  
% 2.05/0.98  fof(f63,plain,(
% 2.05/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f25])).
% 2.05/0.98  
% 2.05/0.98  fof(f82,plain,(
% 2.05/0.98    ~v2_struct_0(sK2)),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f83,plain,(
% 2.05/0.98    v2_pre_topc(sK2)),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f84,plain,(
% 2.05/0.98    l1_pre_topc(sK2)),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f88,plain,(
% 2.05/0.98    ~v2_struct_0(sK4)),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f80,plain,(
% 2.05/0.98    v2_pre_topc(sK1)),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f79,plain,(
% 2.05/0.98    ~v2_struct_0(sK1)),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f81,plain,(
% 2.05/0.98    l1_pre_topc(sK1)),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f87,plain,(
% 2.05/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f10,axiom,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f17,plain,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.05/0.98    inference(pure_predicate_removal,[],[f10])).
% 2.05/0.98  
% 2.05/0.98  fof(f34,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f17])).
% 2.05/0.98  
% 2.05/0.98  fof(f35,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f34])).
% 2.05/0.98  
% 2.05/0.98  fof(f45,plain,(
% 2.05/0.98    ! [X2,X1,X0] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_connsp_2(sK0(X0,X1,X2),X0,X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f46,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_connsp_2(sK0(X0,X1,X2),X0,X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f45])).
% 2.05/0.98  
% 2.05/0.98  fof(f71,plain,(
% 2.05/0.98    ( ! [X2,X0,X1] : (r1_tarski(sK0(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f46])).
% 2.05/0.98  
% 2.05/0.98  fof(f7,axiom,(
% 2.05/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f28,plain,(
% 2.05/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f7])).
% 2.05/0.98  
% 2.05/0.98  fof(f29,plain,(
% 2.05/0.98    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f28])).
% 2.05/0.98  
% 2.05/0.98  fof(f65,plain,(
% 2.05/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f29])).
% 2.05/0.98  
% 2.05/0.98  fof(f68,plain,(
% 2.05/0.98    ( ! [X2,X0,X1] : (m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f46])).
% 2.05/0.98  
% 2.05/0.98  fof(f69,plain,(
% 2.05/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(sK0(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f46])).
% 2.05/0.98  
% 2.05/0.98  fof(f9,axiom,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f32,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f9])).
% 2.05/0.98  
% 2.05/0.98  fof(f33,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f32])).
% 2.05/0.98  
% 2.05/0.98  fof(f67,plain,(
% 2.05/0.98    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f33])).
% 2.05/0.98  
% 2.05/0.98  fof(f2,axiom,(
% 2.05/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f19,plain,(
% 2.05/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.05/0.98    inference(ennf_transformation,[],[f2])).
% 2.05/0.98  
% 2.05/0.98  fof(f20,plain,(
% 2.05/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.05/0.98    inference(flattening,[],[f19])).
% 2.05/0.98  
% 2.05/0.98  fof(f60,plain,(
% 2.05/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f20])).
% 2.05/0.98  
% 2.05/0.98  fof(f13,axiom,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f39,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f13])).
% 2.05/0.98  
% 2.05/0.98  fof(f40,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f39])).
% 2.05/0.98  
% 2.05/0.98  fof(f76,plain,(
% 2.05/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f40])).
% 2.05/0.98  
% 2.05/0.98  fof(f99,plain,(
% 2.05/0.98    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(equality_resolution,[],[f76])).
% 2.05/0.98  
% 2.05/0.98  fof(f1,axiom,(
% 2.05/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f18,plain,(
% 2.05/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f1])).
% 2.05/0.98  
% 2.05/0.98  fof(f59,plain,(
% 2.05/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/0.98    inference(cnf_transformation,[],[f18])).
% 2.05/0.98  
% 2.05/0.98  fof(f8,axiom,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f30,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f8])).
% 2.05/0.98  
% 2.05/0.98  fof(f31,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f30])).
% 2.05/0.98  
% 2.05/0.98  fof(f66,plain,(
% 2.05/0.98    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f31])).
% 2.05/0.98  
% 2.05/0.98  fof(f3,axiom,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f21,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f3])).
% 2.05/0.98  
% 2.05/0.98  fof(f22,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.05/0.98    inference(flattening,[],[f21])).
% 2.05/0.98  
% 2.05/0.98  fof(f61,plain,(
% 2.05/0.98    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f22])).
% 2.05/0.98  
% 2.05/0.98  fof(f4,axiom,(
% 2.05/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f23,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.05/0.98    inference(ennf_transformation,[],[f4])).
% 2.05/0.98  
% 2.05/0.98  fof(f62,plain,(
% 2.05/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f23])).
% 2.05/0.98  
% 2.05/0.98  fof(f6,axiom,(
% 2.05/0.98    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f26,plain,(
% 2.05/0.98    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f6])).
% 2.05/0.98  
% 2.05/0.98  fof(f27,plain,(
% 2.05/0.98    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f26])).
% 2.05/0.98  
% 2.05/0.98  fof(f64,plain,(
% 2.05/0.98    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f27])).
% 2.05/0.98  
% 2.05/0.98  fof(f91,plain,(
% 2.05/0.98    m1_subset_1(sK5,u1_struct_0(sK2))),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f93,plain,(
% 2.05/0.98    sK5 = sK6),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f95,plain,(
% 2.05/0.98    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | ~r1_tmap_1(sK2,sK1,sK3,sK5)),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f12,axiom,(
% 2.05/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f38,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.05/0.98    inference(ennf_transformation,[],[f12])).
% 2.05/0.98  
% 2.05/0.98  fof(f75,plain,(
% 2.05/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f38])).
% 2.05/0.98  
% 2.05/0.98  fof(f11,axiom,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.05/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f36,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f11])).
% 2.05/0.98  
% 2.05/0.98  fof(f37,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.05/0.98    inference(flattening,[],[f36])).
% 2.05/0.98  
% 2.05/0.98  fof(f47,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.05/0.98    inference(nnf_transformation,[],[f37])).
% 2.05/0.98  
% 2.05/0.98  fof(f48,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.05/0.98    inference(flattening,[],[f47])).
% 2.05/0.98  
% 2.05/0.98  fof(f72,plain,(
% 2.05/0.98    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f48])).
% 2.05/0.98  
% 2.05/0.98  fof(f98,plain,(
% 2.05/0.98    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.05/0.98    inference(equality_resolution,[],[f72])).
% 2.05/0.98  
% 2.05/0.98  fof(f89,plain,(
% 2.05/0.98    v1_tsep_1(sK4,sK2)),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f94,plain,(
% 2.05/0.98    r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | r1_tmap_1(sK2,sK1,sK3,sK5)),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  fof(f92,plain,(
% 2.05/0.98    m1_subset_1(sK6,u1_struct_0(sK4))),
% 2.05/0.98    inference(cnf_transformation,[],[f58])).
% 2.05/0.98  
% 2.05/0.98  cnf(c_25,negated_conjecture,
% 2.05/0.98      ( m1_pre_topc(sK4,sK2) ),
% 2.05/0.98      inference(cnf_transformation,[],[f90]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_18,plain,
% 2.05/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.05/0.98      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.05/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.05/0.98      | ~ m1_connsp_2(X5,X0,X3)
% 2.05/0.98      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.05/0.98      | ~ m1_pre_topc(X4,X0)
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.05/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.05/0.98      | ~ v1_funct_1(X2)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | v2_struct_0(X4)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ l1_pre_topc(X0)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X0) ),
% 2.05/0.98      inference(cnf_transformation,[],[f100]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_29,negated_conjecture,
% 2.05/0.98      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 2.05/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_618,plain,
% 2.05/0.98      ( r1_tmap_1(X0,X1,X2,X3)
% 2.05/0.98      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.05/0.98      | ~ m1_connsp_2(X5,X0,X3)
% 2.05/0.98      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.05/0.98      | ~ m1_pre_topc(X4,X0)
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.05/0.98      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.05/0.98      | ~ v1_funct_1(X2)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | v2_struct_0(X4)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ l1_pre_topc(X0)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X0)
% 2.05/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.05/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.05/0.98      | sK3 != X2 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_619,plain,
% 2.05/0.98      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.05/0.98      | r1_tmap_1(X2,X1,sK3,X3)
% 2.05/0.98      | ~ m1_connsp_2(X4,X2,X3)
% 2.05/0.98      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_pre_topc(X0,X2)
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.05/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.05/0.98      | ~ v1_funct_1(sK3)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | v2_struct_0(X2)
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ l1_pre_topc(X2)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X2)
% 2.05/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.05/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_618]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_30,negated_conjecture,
% 2.05/0.98      ( v1_funct_1(sK3) ),
% 2.05/0.98      inference(cnf_transformation,[],[f85]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_623,plain,
% 2.05/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.05/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_pre_topc(X0,X2)
% 2.05/0.98      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_connsp_2(X4,X2,X3)
% 2.05/0.98      | r1_tmap_1(X2,X1,sK3,X3)
% 2.05/0.98      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | v2_struct_0(X2)
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ l1_pre_topc(X2)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X2)
% 2.05/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.05/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_619,c_30]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_624,plain,
% 2.05/0.98      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.05/0.98      | r1_tmap_1(X2,X1,sK3,X3)
% 2.05/0.98      | ~ m1_connsp_2(X4,X2,X3)
% 2.05/0.98      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_pre_topc(X0,X2)
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.05/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | v2_struct_0(X2)
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ l1_pre_topc(X2)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X2)
% 2.05/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.05/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_623]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4,plain,
% 2.05/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.05/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.05/0.98      | m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_665,plain,
% 2.05/0.98      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.05/0.98      | r1_tmap_1(X2,X1,sK3,X3)
% 2.05/0.98      | ~ m1_connsp_2(X4,X2,X3)
% 2.05/0.98      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_pre_topc(X0,X2)
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | v2_struct_0(X2)
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ l1_pre_topc(X2)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X2)
% 2.05/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.05/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_624,c_4]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_881,plain,
% 2.05/0.98      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.05/0.98      | r1_tmap_1(X2,X1,sK3,X3)
% 2.05/0.98      | ~ m1_connsp_2(X4,X2,X3)
% 2.05/0.98      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.05/0.98      | v2_struct_0(X2)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X2)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X2)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.05/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.05/0.98      | sK2 != X2
% 2.05/0.98      | sK4 != X0 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_665]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_882,plain,
% 2.05/0.98      ( r1_tmap_1(sK2,X0,sK3,X1)
% 2.05/0.98      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.05/0.98      | ~ m1_connsp_2(X2,sK2,X1)
% 2.05/0.98      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | v2_struct_0(sK2)
% 2.05/0.98      | v2_struct_0(sK4)
% 2.05/0.98      | ~ l1_pre_topc(X0)
% 2.05/0.98      | ~ l1_pre_topc(sK2)
% 2.05/0.98      | ~ v2_pre_topc(X0)
% 2.05/0.98      | ~ v2_pre_topc(sK2)
% 2.05/0.98      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.05/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_881]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_33,negated_conjecture,
% 2.05/0.98      ( ~ v2_struct_0(sK2) ),
% 2.05/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_32,negated_conjecture,
% 2.05/0.98      ( v2_pre_topc(sK2) ),
% 2.05/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_31,negated_conjecture,
% 2.05/0.98      ( l1_pre_topc(sK2) ),
% 2.05/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_27,negated_conjecture,
% 2.05/0.98      ( ~ v2_struct_0(sK4) ),
% 2.05/0.98      inference(cnf_transformation,[],[f88]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_886,plain,
% 2.05/0.98      ( ~ v2_pre_topc(X0)
% 2.05/0.98      | r1_tmap_1(sK2,X0,sK3,X1)
% 2.05/0.98      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.05/0.98      | ~ m1_connsp_2(X2,sK2,X1)
% 2.05/0.98      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X0)
% 2.05/0.98      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.05/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_882,c_33,c_32,c_31,c_27]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_887,plain,
% 2.05/0.98      ( r1_tmap_1(sK2,X0,sK3,X1)
% 2.05/0.98      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.05/0.98      | ~ m1_connsp_2(X2,sK2,X1)
% 2.05/0.98      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X0)
% 2.05/0.98      | ~ v2_pre_topc(X0)
% 2.05/0.98      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.05/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_886]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_35,negated_conjecture,
% 2.05/0.98      ( v2_pre_topc(sK1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1573,plain,
% 2.05/0.98      ( r1_tmap_1(sK2,X0,sK3,X1)
% 2.05/0.98      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.05/0.98      | ~ m1_connsp_2(X2,sK2,X1)
% 2.05/0.98      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X0)
% 2.05/0.98      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.05/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.05/0.98      | sK1 != X0 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_887,c_35]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1574,plain,
% 2.05/0.98      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 2.05/0.98      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.05/0.98      | ~ m1_connsp_2(X1,sK2,X0)
% 2.05/0.98      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.05/0.98      | v2_struct_0(sK1)
% 2.05/0.98      | ~ l1_pre_topc(sK1)
% 2.05/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_1573]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_36,negated_conjecture,
% 2.05/0.98      ( ~ v2_struct_0(sK1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_34,negated_conjecture,
% 2.05/0.98      ( l1_pre_topc(sK1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_28,negated_conjecture,
% 2.05/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 2.05/0.98      inference(cnf_transformation,[],[f87]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1578,plain,
% 2.05/0.98      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.05/0.98      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_connsp_2(X1,sK2,X0)
% 2.05/0.98      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.05/0.98      | r1_tmap_1(sK2,sK1,sK3,X0)
% 2.05/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_1574,c_36,c_34,c_28]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1579,plain,
% 2.05/0.98      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 2.05/0.98      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.05/0.98      | ~ m1_connsp_2(X1,sK2,X0)
% 2.05/0.98      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_1578]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2505,plain,
% 2.05/0.98      ( r1_tmap_1(sK2,sK1,sK3,X0_54)
% 2.05/0.98      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
% 2.05/0.98      | ~ m1_connsp_2(X1_54,sK2,X0_54)
% 2.05/0.98      | ~ r1_tarski(X1_54,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_1579]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2776,plain,
% 2.05/0.98      ( r1_tmap_1(sK2,sK1,sK3,X0_54)
% 2.05/0.98      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
% 2.05/0.98      | ~ m1_connsp_2(X1_54,sK2,X0_54)
% 2.05/0.98      | ~ r1_tarski(X1_54,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.05/0.98      inference(equality_resolution_simp,[status(thm)],[c_2505]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_5033,plain,
% 2.05/0.98      ( r1_tmap_1(sK2,sK1,sK3,X0_54)
% 2.05/0.98      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
% 2.05/0.98      | ~ m1_connsp_2(sK0(sK2,sK6,u1_struct_0(sK4)),sK2,X0_54)
% 2.05/0.98      | ~ r1_tarski(sK0(sK2,sK6,u1_struct_0(sK4)),u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(sK0(sK2,sK6,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2776]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_5555,plain,
% 2.05/0.98      ( r1_tmap_1(sK2,sK1,sK3,sK6)
% 2.05/0.98      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 2.05/0.98      | ~ m1_connsp_2(sK0(sK2,sK6,u1_struct_0(sK4)),sK2,sK6)
% 2.05/0.98      | ~ r1_tarski(sK0(sK2,sK6,u1_struct_0(sK4)),u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(sK0(sK2,sK6,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_5033]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2561,plain,
% 2.05/0.98      ( ~ r1_tmap_1(X0_53,X1_53,X0_54,X1_54)
% 2.05/0.98      | r1_tmap_1(X0_53,X1_53,X2_54,X3_54)
% 2.05/0.98      | X2_54 != X0_54
% 2.05/0.98      | X3_54 != X1_54 ),
% 2.05/0.98      theory(equality) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4599,plain,
% 2.05/0.98      ( r1_tmap_1(sK4,sK1,X0_54,X1_54)
% 2.05/0.98      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
% 2.05/0.98      | X0_54 != k2_tmap_1(sK2,sK1,sK3,sK4)
% 2.05/0.98      | X1_54 != sK5 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2561]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_5143,plain,
% 2.05/0.98      ( r1_tmap_1(sK4,sK1,X0_54,sK6)
% 2.05/0.98      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
% 2.05/0.98      | X0_54 != k2_tmap_1(sK2,sK1,sK3,sK4)
% 2.05/0.98      | sK6 != sK5 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_4599]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_5539,plain,
% 2.05/0.98      ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
% 2.05/0.98      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 2.05/0.98      | k2_tmap_1(sK2,sK1,sK3,sK4) != k2_tmap_1(sK2,sK1,sK3,sK4)
% 2.05/0.98      | sK6 != sK5 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_5143]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_9,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.98      | r1_tarski(sK0(X1,X2,X0),X0)
% 2.05/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_6,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_235,plain,
% 2.05/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | r1_tarski(sK0(X1,X2,X0),X0)
% 2.05/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(global_propositional_subsumption,[status(thm)],[c_9,c_6]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_236,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.98      | r1_tarski(sK0(X1,X2,X0),X0)
% 2.05/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_235]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1000,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.98      | r1_tarski(sK0(X1,X2,X0),X0)
% 2.05/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | sK2 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_236,c_32]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1001,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.05/0.98      | r1_tarski(sK0(sK2,X1,X0),X0)
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.05/0.98      | v2_struct_0(sK2)
% 2.05/0.98      | ~ l1_pre_topc(sK2) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_1000]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1005,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.05/0.98      | r1_tarski(sK0(sK2,X1,X0),X0)
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_1001,c_33,c_31]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2531,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0_54,sK2,X1_54)
% 2.05/0.98      | r1_tarski(sK0(sK2,X1_54,X0_54),X0_54)
% 2.05/0.98      | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_1005]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4163,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0_54,sK2,sK6)
% 2.05/0.98      | r1_tarski(sK0(sK2,sK6,X0_54),X0_54)
% 2.05/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2531]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4860,plain,
% 2.05/0.98      ( ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK6)
% 2.05/0.98      | r1_tarski(sK0(sK2,sK6,u1_struct_0(sK4)),u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_4163]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_12,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_214,plain,
% 2.05/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.98      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_12,c_6]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_215,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_214]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1063,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | sK2 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_215,c_32]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1064,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.05/0.98      | m1_subset_1(sK0(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | v2_struct_0(sK2)
% 2.05/0.98      | ~ l1_pre_topc(sK2) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_1063]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1068,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.05/0.98      | m1_subset_1(sK0(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_1064,c_33,c_31]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2528,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0_54,sK2,X1_54)
% 2.05/0.98      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 2.05/0.98      | m1_subset_1(sK0(sK2,X1_54,X0_54),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_1068]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4166,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0_54,sK2,sK6)
% 2.05/0.98      | m1_subset_1(sK0(sK2,sK6,X0_54),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2528]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4862,plain,
% 2.05/0.98      ( ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK6)
% 2.05/0.98      | m1_subset_1(sK0(sK2,sK6,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_4166]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_11,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.98      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.05/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_221,plain,
% 2.05/0.98      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.05/0.98      | ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_11,c_6]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_222,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.98      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.05/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_221]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1042,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,X1,X2)
% 2.05/0.98      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.05/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | sK2 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_222,c_32]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1043,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.05/0.98      | m1_connsp_2(sK0(sK2,X1,X0),sK2,X1)
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.05/0.98      | v2_struct_0(sK2)
% 2.05/0.98      | ~ l1_pre_topc(sK2) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_1042]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1047,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.05/0.98      | m1_connsp_2(sK0(sK2,X1,X0),sK2,X1)
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_1043,c_33,c_31]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2529,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0_54,sK2,X1_54)
% 2.05/0.98      | m1_connsp_2(sK0(sK2,X1_54,X0_54),sK2,X1_54)
% 2.05/0.98      | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_1047]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4164,plain,
% 2.05/0.98      ( ~ m1_connsp_2(X0_54,sK2,sK6)
% 2.05/0.98      | m1_connsp_2(sK0(sK2,sK6,X0_54),sK2,sK6)
% 2.05/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2529]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4864,plain,
% 2.05/0.98      ( m1_connsp_2(sK0(sK2,sK6,u1_struct_0(sK4)),sK2,sK6)
% 2.05/0.98      | ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK6)
% 2.05/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_4164]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_8,plain,
% 2.05/0.98      ( m1_connsp_2(X0,X1,X2)
% 2.05/0.98      | ~ v3_pre_topc(X0,X1)
% 2.05/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ r2_hidden(X2,X0)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1084,plain,
% 2.05/0.98      ( m1_connsp_2(X0,X1,X2)
% 2.05/0.98      | ~ v3_pre_topc(X0,X1)
% 2.05/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.05/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ r2_hidden(X2,X0)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | sK2 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_32]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1085,plain,
% 2.05/0.98      ( m1_connsp_2(X0,sK2,X1)
% 2.05/0.98      | ~ v3_pre_topc(X0,sK2)
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.05/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ r2_hidden(X1,X0)
% 2.05/0.98      | v2_struct_0(sK2)
% 2.05/0.98      | ~ l1_pre_topc(sK2) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_1084]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1089,plain,
% 2.05/0.98      ( m1_connsp_2(X0,sK2,X1)
% 2.05/0.98      | ~ v3_pre_topc(X0,sK2)
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.05/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ r2_hidden(X1,X0) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_1085,c_33,c_31]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1,plain,
% 2.05/0.98      ( m1_subset_1(X0,X1)
% 2.05/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.05/0.98      | ~ r2_hidden(X0,X2) ),
% 2.05/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1105,plain,
% 2.05/0.98      ( m1_connsp_2(X0,sK2,X1)
% 2.05/0.98      | ~ v3_pre_topc(X0,sK2)
% 2.05/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ r2_hidden(X1,X0) ),
% 2.05/0.98      inference(forward_subsumption_resolution,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_1089,c_1]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2527,plain,
% 2.05/0.98      ( m1_connsp_2(X0_54,sK2,X1_54)
% 2.05/0.98      | ~ v3_pre_topc(X0_54,sK2)
% 2.05/0.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ r2_hidden(X1_54,X0_54) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_1105]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4073,plain,
% 2.05/0.98      ( m1_connsp_2(u1_struct_0(sK4),sK2,X0_54)
% 2.05/0.98      | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
% 2.05/0.98      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ r2_hidden(X0_54,u1_struct_0(sK4)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2527]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4630,plain,
% 2.05/0.98      ( m1_connsp_2(u1_struct_0(sK4),sK2,sK6)
% 2.05/0.98      | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
% 2.05/0.98      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ r2_hidden(sK6,u1_struct_0(sK4)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_4073]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_17,plain,
% 2.05/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.05/0.98      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.05/0.98      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.05/0.98      | ~ m1_pre_topc(X4,X0)
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.05/0.98      | ~ v1_funct_1(X2)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | v2_struct_0(X4)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ l1_pre_topc(X0)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X0) ),
% 2.05/0.98      inference(cnf_transformation,[],[f99]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_684,plain,
% 2.05/0.98      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.05/0.98      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.05/0.98      | ~ m1_pre_topc(X4,X0)
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.05/0.98      | ~ v1_funct_1(X2)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | v2_struct_0(X4)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ l1_pre_topc(X0)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X0)
% 2.05/0.98      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.05/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.05/0.98      | sK3 != X2 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_685,plain,
% 2.05/0.98      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.05/0.98      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.05/0.98      | ~ m1_pre_topc(X0,X2)
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.05/0.98      | ~ v1_funct_1(sK3)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | v2_struct_0(X2)
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ l1_pre_topc(X2)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X2)
% 2.05/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.05/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_684]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_689,plain,
% 2.05/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_pre_topc(X0,X2)
% 2.05/0.98      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.05/0.98      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | v2_struct_0(X2)
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ l1_pre_topc(X2)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X2)
% 2.05/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.05/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_685,c_30]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_690,plain,
% 2.05/0.98      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.05/0.98      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.05/0.98      | ~ m1_pre_topc(X0,X2)
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | v2_struct_0(X2)
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ l1_pre_topc(X2)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X2)
% 2.05/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.05/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_689]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_725,plain,
% 2.05/0.98      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.05/0.98      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.05/0.98      | ~ m1_pre_topc(X0,X2)
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | v2_struct_0(X2)
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ l1_pre_topc(X2)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X2)
% 2.05/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.05/0.98      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_690,c_4]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_842,plain,
% 2.05/0.98      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.05/0.98      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.05/0.98      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.05/0.98      | v2_struct_0(X2)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X2)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X2)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.05/0.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.05/0.98      | sK2 != X2
% 2.05/0.98      | sK4 != X0 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_725]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_843,plain,
% 2.05/0.98      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.05/0.98      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | v2_struct_0(sK2)
% 2.05/0.98      | v2_struct_0(sK4)
% 2.05/0.98      | ~ l1_pre_topc(X0)
% 2.05/0.98      | ~ l1_pre_topc(sK2)
% 2.05/0.98      | ~ v2_pre_topc(X0)
% 2.05/0.98      | ~ v2_pre_topc(sK2)
% 2.05/0.98      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.05/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_842]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_847,plain,
% 2.05/0.98      ( ~ v2_pre_topc(X0)
% 2.05/0.98      | ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.05/0.98      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X0)
% 2.05/0.98      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.05/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_843,c_33,c_32,c_31,c_27]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_848,plain,
% 2.05/0.98      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.05/0.98      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X0)
% 2.05/0.98      | ~ v2_pre_topc(X0)
% 2.05/0.98      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.05/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_847]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1606,plain,
% 2.05/0.98      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.05/0.98      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.05/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.05/0.98      | v2_struct_0(X0)
% 2.05/0.98      | ~ l1_pre_topc(X0)
% 2.05/0.98      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.05/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.05/0.98      | sK1 != X0 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_848,c_35]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1607,plain,
% 2.05/0.98      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 2.05/0.98      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.05/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.05/0.98      | v2_struct_0(sK1)
% 2.05/0.98      | ~ l1_pre_topc(sK1)
% 2.05/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_1606]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1611,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.05/0.98      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.05/0.98      | ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 2.05/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_1607,c_36,c_34,c_28]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1612,plain,
% 2.05/0.98      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 2.05/0.98      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.05/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.05/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_1611]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2504,plain,
% 2.05/0.98      ( ~ r1_tmap_1(sK2,sK1,sK3,X0_54)
% 2.05/0.98      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
% 2.05/0.98      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 2.05/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_1612]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2780,plain,
% 2.05/0.98      ( ~ r1_tmap_1(sK2,sK1,sK3,X0_54)
% 2.05/0.98      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
% 2.05/0.98      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 2.05/0.98      inference(equality_resolution_simp,[status(thm)],[c_2504]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4536,plain,
% 2.05/0.98      ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
% 2.05/0.98      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
% 2.05/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2780]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2553,plain,
% 2.05/0.98      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 2.05/0.98      theory(equality) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4261,plain,
% 2.05/0.98      ( X0_54 != X1_54 | X0_54 = sK5 | sK5 != X1_54 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2553]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4490,plain,
% 2.05/0.98      ( X0_54 = sK5 | X0_54 != sK6 | sK5 != sK6 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_4261]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4535,plain,
% 2.05/0.98      ( sK5 != sK6 | sK6 = sK5 | sK6 != sK6 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_4490]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_0,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.05/0.98      | ~ r2_hidden(X2,X0)
% 2.05/0.98      | r2_hidden(X2,X1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2542,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 2.05/0.98      | ~ r2_hidden(X2_54,X0_54)
% 2.05/0.98      | r2_hidden(X2_54,X1_54) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4224,plain,
% 2.05/0.98      ( ~ m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(X0_54))
% 2.05/0.98      | r2_hidden(sK6,X0_54)
% 2.05/0.98      | ~ r2_hidden(sK6,k1_connsp_2(sK4,sK6)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2542]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4393,plain,
% 2.05/0.98      ( ~ m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.05/0.98      | ~ r2_hidden(sK6,k1_connsp_2(sK4,sK6))
% 2.05/0.98      | r2_hidden(sK6,u1_struct_0(sK4)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_4224]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2552,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4331,plain,
% 2.05/0.98      ( k2_tmap_1(sK2,sK1,sK3,sK4) = k2_tmap_1(sK2,sK1,sK3,sK4) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2552]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4147,plain,
% 2.05/0.98      ( r1_tmap_1(sK4,sK1,X0_54,X1_54)
% 2.05/0.98      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 2.05/0.98      | X0_54 != k2_tmap_1(sK2,sK1,sK3,sK4)
% 2.05/0.98      | X1_54 != sK6 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2561]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4276,plain,
% 2.05/0.98      ( r1_tmap_1(sK4,sK1,X0_54,sK5)
% 2.05/0.98      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 2.05/0.98      | X0_54 != k2_tmap_1(sK2,sK1,sK3,sK4)
% 2.05/0.98      | sK5 != sK6 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_4147]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4330,plain,
% 2.05/0.98      ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
% 2.05/0.98      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 2.05/0.98      | k2_tmap_1(sK2,sK1,sK3,sK4) != k2_tmap_1(sK2,sK1,sK3,sK4)
% 2.05/0.98      | sK5 != sK6 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_4276]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4326,plain,
% 2.05/0.98      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2552]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2556,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0_54,X1_54)
% 2.05/0.98      | m1_subset_1(X2_54,X3_54)
% 2.05/0.98      | X2_54 != X0_54
% 2.05/0.98      | X3_54 != X1_54 ),
% 2.05/0.98      theory(equality) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4127,plain,
% 2.05/0.98      ( m1_subset_1(X0_54,X1_54)
% 2.05/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.05/0.98      | X1_54 != u1_struct_0(sK4)
% 2.05/0.98      | X0_54 != sK6 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2556]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4242,plain,
% 2.05/0.98      ( m1_subset_1(sK5,X0_54)
% 2.05/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.05/0.98      | X0_54 != u1_struct_0(sK4)
% 2.05/0.98      | sK5 != sK6 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_4127]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4325,plain,
% 2.05/0.98      ( m1_subset_1(sK5,u1_struct_0(sK4))
% 2.05/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.05/0.98      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.05/0.98      | sK5 != sK6 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_4242]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4248,plain,
% 2.05/0.98      ( sK6 = sK6 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2552]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_7,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.05/0.98      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2,plain,
% 2.05/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | v2_pre_topc(X0) ),
% 2.05/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_831,plain,
% 2.05/0.98      ( ~ l1_pre_topc(X0)
% 2.05/0.98      | ~ v2_pre_topc(X0)
% 2.05/0.98      | v2_pre_topc(X1)
% 2.05/0.98      | sK2 != X0
% 2.05/0.98      | sK4 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_25]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_832,plain,
% 2.05/0.98      ( ~ l1_pre_topc(sK2) | ~ v2_pre_topc(sK2) | v2_pre_topc(sK4) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_831]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_834,plain,
% 2.05/0.98      ( v2_pre_topc(sK4) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_832,c_32,c_31]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1453,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.05/0.98      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | sK4 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_834]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1454,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.05/0.98      | r2_hidden(X0,k1_connsp_2(sK4,X0))
% 2.05/0.98      | v2_struct_0(sK4)
% 2.05/0.98      | ~ l1_pre_topc(sK4) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_1453]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3,plain,
% 2.05/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.05/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_820,plain,
% 2.05/0.98      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X0 | sK4 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_25]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_821,plain,
% 2.05/0.98      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_820]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1458,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.05/0.98      | r2_hidden(X0,k1_connsp_2(sK4,X0)) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_1454,c_31,c_27,c_821]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2510,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 2.05/0.98      | r2_hidden(X0_54,k1_connsp_2(sK4,X0_54)) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_1458]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4038,plain,
% 2.05/0.98      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.05/0.98      | r2_hidden(sK6,k1_connsp_2(sK4,sK6)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2510]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_5,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.05/0.98      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1492,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.05/0.98      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | sK4 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_834]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1493,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.05/0.98      | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.05/0.98      | v2_struct_0(sK4)
% 2.05/0.98      | ~ l1_pre_topc(sK4) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_1492]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1497,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.05/0.98      | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_1493,c_31,c_27,c_821]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2508,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 2.05/0.98      | m1_subset_1(k1_connsp_2(sK4,X0_54),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_1497]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4035,plain,
% 2.05/0.98      ( m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.05/0.98      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2508]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_24,negated_conjecture,
% 2.05/0.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.05/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2536,negated_conjecture,
% 2.05/0.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_24]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3588,plain,
% 2.05/0.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_2536]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_22,negated_conjecture,
% 2.05/0.98      ( sK5 = sK6 ),
% 2.05/0.98      inference(cnf_transformation,[],[f93]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2538,negated_conjecture,
% 2.05/0.98      ( sK5 = sK6 ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_22]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3631,plain,
% 2.05/0.98      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 2.05/0.98      inference(light_normalisation,[status(thm)],[c_3588,c_2538]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3928,plain,
% 2.05/0.98      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 2.05/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3631]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_20,negated_conjecture,
% 2.05/0.98      ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
% 2.05/0.98      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 2.05/0.98      inference(cnf_transformation,[],[f95]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2540,negated_conjecture,
% 2.05/0.98      ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
% 2.05/0.98      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 2.05/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3585,plain,
% 2.05/0.98      ( r1_tmap_1(sK2,sK1,sK3,sK5) != iProver_top
% 2.05/0.98      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_2540]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3685,plain,
% 2.05/0.98      ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
% 2.05/0.98      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
% 2.05/0.98      inference(light_normalisation,[status(thm)],[c_3585,c_2538]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3896,plain,
% 2.05/0.98      ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
% 2.05/0.98      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 2.05/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3685]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_16,plain,
% 2.05/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.05/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ l1_pre_topc(X1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_791,plain,
% 2.05/0.98      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | sK2 != X1
% 2.05/0.98      | sK4 != X0 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_792,plain,
% 2.05/0.98      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.05/0.98      | ~ l1_pre_topc(sK2) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_791]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_15,plain,
% 2.05/0.98      ( ~ v1_tsep_1(X0,X1)
% 2.05/0.98      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.05/0.98      | ~ m1_pre_topc(X0,X1)
% 2.05/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f98]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_200,plain,
% 2.05/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.05/0.98      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.05/0.98      | ~ v1_tsep_1(X0,X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_15,c_16]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_201,plain,
% 2.05/0.98      ( ~ v1_tsep_1(X0,X1)
% 2.05/0.98      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.05/0.98      | ~ m1_pre_topc(X0,X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_200]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_26,negated_conjecture,
% 2.05/0.98      ( v1_tsep_1(sK4,sK2) ),
% 2.05/0.98      inference(cnf_transformation,[],[f89]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_483,plain,
% 2.05/0.98      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.05/0.98      | ~ m1_pre_topc(X0,X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | sK2 != X1
% 2.05/0.98      | sK4 != X0 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_201,c_26]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_484,plain,
% 2.05/0.98      ( v3_pre_topc(u1_struct_0(sK4),sK2)
% 2.05/0.98      | ~ m1_pre_topc(sK4,sK2)
% 2.05/0.98      | ~ l1_pre_topc(sK2)
% 2.05/0.98      | ~ v2_pre_topc(sK2) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_483]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_21,negated_conjecture,
% 2.05/0.98      ( r1_tmap_1(sK2,sK1,sK3,sK5)
% 2.05/0.98      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 2.05/0.98      inference(cnf_transformation,[],[f94]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_23,negated_conjecture,
% 2.05/0.98      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.05/0.98      inference(cnf_transformation,[],[f92]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(contradiction,plain,
% 2.05/0.98      ( $false ),
% 2.05/0.98      inference(minisat,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_5555,c_5539,c_4860,c_4862,c_4864,c_4630,c_4536,c_4535,
% 2.05/0.98                 c_4393,c_4331,c_4330,c_4326,c_4325,c_4248,c_4038,c_4035,
% 2.05/0.98                 c_3928,c_3896,c_2538,c_792,c_484,c_21,c_23,c_25,c_31,
% 2.05/0.98                 c_32]) ).
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  ------                               Statistics
% 2.05/0.98  
% 2.05/0.98  ------ General
% 2.05/0.98  
% 2.05/0.98  abstr_ref_over_cycles:                  0
% 2.05/0.98  abstr_ref_under_cycles:                 0
% 2.05/0.98  gc_basic_clause_elim:                   0
% 2.05/0.98  forced_gc_time:                         0
% 2.05/0.98  parsing_time:                           0.025
% 2.05/0.98  unif_index_cands_time:                  0.
% 2.05/0.98  unif_index_add_time:                    0.
% 2.05/0.98  orderings_time:                         0.
% 2.05/0.98  out_proof_time:                         0.014
% 2.05/0.98  total_time:                             0.212
% 2.05/0.98  num_of_symbols:                         62
% 2.05/0.98  num_of_terms:                           3627
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing
% 2.05/0.98  
% 2.05/0.98  num_of_splits:                          4
% 2.05/0.98  num_of_split_atoms:                     4
% 2.05/0.98  num_of_reused_defs:                     0
% 2.05/0.98  num_eq_ax_congr_red:                    24
% 2.05/0.98  num_of_sem_filtered_clauses:            1
% 2.05/0.98  num_of_subtypes:                        2
% 2.05/0.98  monotx_restored_types:                  0
% 2.05/0.98  sat_num_of_epr_types:                   0
% 2.05/0.98  sat_num_of_non_cyclic_types:            0
% 2.05/0.98  sat_guarded_non_collapsed_types:        0
% 2.05/0.98  num_pure_diseq_elim:                    0
% 2.05/0.98  simp_replaced_by:                       0
% 2.05/0.98  res_preprocessed:                       148
% 2.05/0.98  prep_upred:                             0
% 2.05/0.98  prep_unflattend:                        86
% 2.05/0.98  smt_new_axioms:                         0
% 2.05/0.98  pred_elim_cands:                        13
% 2.05/0.98  pred_elim:                              7
% 2.05/0.98  pred_elim_cl:                           -6
% 2.05/0.98  pred_elim_cycles:                       13
% 2.05/0.98  merged_defs:                            6
% 2.05/0.98  merged_defs_ncl:                        0
% 2.05/0.98  bin_hyper_res:                          6
% 2.05/0.98  prep_cycles:                            3
% 2.05/0.98  pred_elim_time:                         0.058
% 2.05/0.98  splitting_time:                         0.
% 2.05/0.98  sem_filter_time:                        0.
% 2.05/0.98  monotx_time:                            0.
% 2.05/0.98  subtype_inf_time:                       0.
% 2.05/0.98  
% 2.05/0.98  ------ Problem properties
% 2.05/0.98  
% 2.05/0.98  clauses:                                45
% 2.05/0.98  conjectures:                            6
% 2.05/0.98  epr:                                    1
% 2.05/0.98  horn:                                   44
% 2.05/0.98  ground:                                 12
% 2.05/0.98  unary:                                  6
% 2.05/0.98  binary:                                 9
% 2.05/0.98  lits:                                   132
% 2.05/0.98  lits_eq:                                7
% 2.05/0.98  fd_pure:                                0
% 2.05/0.98  fd_pseudo:                              0
% 2.05/0.98  fd_cond:                                0
% 2.05/0.98  fd_pseudo_cond:                         0
% 2.05/0.98  ac_symbols:                             0
% 2.05/0.98  
% 2.05/0.98  ------ Propositional Solver
% 2.05/0.98  
% 2.05/0.98  prop_solver_calls:                      24
% 2.05/0.98  prop_fast_solver_calls:                 1780
% 2.05/0.98  smt_solver_calls:                       0
% 2.05/0.98  smt_fast_solver_calls:                  0
% 2.05/0.98  prop_num_of_clauses:                    1441
% 2.05/0.98  prop_preprocess_simplified:             5393
% 2.05/0.98  prop_fo_subsumed:                       100
% 2.05/0.98  prop_solver_time:                       0.
% 2.05/0.98  smt_solver_time:                        0.
% 2.05/0.98  smt_fast_solver_time:                   0.
% 2.05/0.98  prop_fast_solver_time:                  0.
% 2.05/0.98  prop_unsat_core_time:                   0.
% 2.05/0.98  
% 2.05/0.98  ------ QBF
% 2.05/0.98  
% 2.05/0.98  qbf_q_res:                              0
% 2.05/0.98  qbf_num_tautologies:                    0
% 2.05/0.98  qbf_prep_cycles:                        0
% 2.05/0.98  
% 2.05/0.98  ------ BMC1
% 2.05/0.98  
% 2.05/0.98  bmc1_current_bound:                     -1
% 2.05/0.98  bmc1_last_solved_bound:                 -1
% 2.05/0.98  bmc1_unsat_core_size:                   -1
% 2.05/0.98  bmc1_unsat_core_parents_size:           -1
% 2.05/0.98  bmc1_merge_next_fun:                    0
% 2.05/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.05/0.98  
% 2.05/0.98  ------ Instantiation
% 2.05/0.98  
% 2.05/0.98  inst_num_of_clauses:                    309
% 2.05/0.98  inst_num_in_passive:                    43
% 2.05/0.98  inst_num_in_active:                     249
% 2.05/0.98  inst_num_in_unprocessed:                16
% 2.05/0.98  inst_num_of_loops:                      255
% 2.05/0.98  inst_num_of_learning_restarts:          0
% 2.05/0.98  inst_num_moves_active_passive:          1
% 2.05/0.98  inst_lit_activity:                      0
% 2.05/0.98  inst_lit_activity_moves:                0
% 2.05/0.98  inst_num_tautologies:                   0
% 2.05/0.98  inst_num_prop_implied:                  0
% 2.05/0.98  inst_num_existing_simplified:           0
% 2.05/0.98  inst_num_eq_res_simplified:             0
% 2.05/0.98  inst_num_child_elim:                    0
% 2.05/0.98  inst_num_of_dismatching_blockings:      9
% 2.05/0.98  inst_num_of_non_proper_insts:           283
% 2.05/0.98  inst_num_of_duplicates:                 0
% 2.05/0.98  inst_inst_num_from_inst_to_res:         0
% 2.05/0.98  inst_dismatching_checking_time:         0.
% 2.05/0.98  
% 2.05/0.98  ------ Resolution
% 2.05/0.98  
% 2.05/0.98  res_num_of_clauses:                     0
% 2.05/0.98  res_num_in_passive:                     0
% 2.05/0.98  res_num_in_active:                      0
% 2.05/0.98  res_num_of_loops:                       151
% 2.05/0.98  res_forward_subset_subsumed:            52
% 2.05/0.98  res_backward_subset_subsumed:           0
% 2.05/0.98  res_forward_subsumed:                   0
% 2.05/0.98  res_backward_subsumed:                  0
% 2.05/0.98  res_forward_subsumption_resolution:     10
% 2.05/0.98  res_backward_subsumption_resolution:    0
% 2.05/0.98  res_clause_to_clause_subsumption:       211
% 2.05/0.98  res_orphan_elimination:                 0
% 2.05/0.98  res_tautology_del:                      78
% 2.05/0.98  res_num_eq_res_simplified:              2
% 2.05/0.98  res_num_sel_changes:                    0
% 2.05/0.98  res_moves_from_active_to_pass:          0
% 2.05/0.98  
% 2.05/0.98  ------ Superposition
% 2.05/0.98  
% 2.05/0.98  sup_time_total:                         0.
% 2.05/0.98  sup_time_generating:                    0.
% 2.05/0.98  sup_time_sim_full:                      0.
% 2.05/0.98  sup_time_sim_immed:                     0.
% 2.05/0.98  
% 2.05/0.98  sup_num_of_clauses:                     69
% 2.05/0.98  sup_num_in_active:                      50
% 2.05/0.98  sup_num_in_passive:                     19
% 2.05/0.98  sup_num_of_loops:                       50
% 2.05/0.98  sup_fw_superposition:                   15
% 2.05/0.98  sup_bw_superposition:                   13
% 2.05/0.98  sup_immediate_simplified:               1
% 2.05/0.98  sup_given_eliminated:                   0
% 2.05/0.98  comparisons_done:                       0
% 2.05/0.98  comparisons_avoided:                    0
% 2.05/0.98  
% 2.05/0.98  ------ Simplifications
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  sim_fw_subset_subsumed:                 1
% 2.05/0.98  sim_bw_subset_subsumed:                 0
% 2.05/0.98  sim_fw_subsumed:                        0
% 2.05/0.98  sim_bw_subsumed:                        0
% 2.05/0.98  sim_fw_subsumption_res:                 0
% 2.05/0.98  sim_bw_subsumption_res:                 0
% 2.05/0.98  sim_tautology_del:                      3
% 2.05/0.98  sim_eq_tautology_del:                   0
% 2.05/0.98  sim_eq_res_simp:                        2
% 2.05/0.98  sim_fw_demodulated:                     0
% 2.05/0.98  sim_bw_demodulated:                     0
% 2.05/0.98  sim_light_normalised:                   3
% 2.05/0.98  sim_joinable_taut:                      0
% 2.05/0.98  sim_joinable_simp:                      0
% 2.05/0.98  sim_ac_normalised:                      0
% 2.05/0.98  sim_smt_subsumption:                    0
% 2.05/0.98  
%------------------------------------------------------------------------------
