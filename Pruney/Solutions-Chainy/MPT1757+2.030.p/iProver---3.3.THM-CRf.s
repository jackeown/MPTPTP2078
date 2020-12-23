%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:47 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  194 (1662 expanded)
%              Number of clauses        :  115 ( 315 expanded)
%              Number of leaves         :   19 ( 643 expanded)
%              Depth                    :   35
%              Number of atoms          : 1373 (26421 expanded)
%              Number of equality atoms :  238 (2100 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | ~ r1_tmap_1(X1,X0,X2,X4) )
          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | r1_tmap_1(X1,X0,X2,X4) )
          & X4 = X5
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5)
          | ~ r1_tmap_1(X1,X0,X2,X4) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5)
          | r1_tmap_1(X1,X0,X2,X4) )
        & sK5 = X4
        & m1_subset_1(sK5,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
              | ~ r1_tmap_1(X1,X0,X2,sK4) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | r1_tmap_1(X1,X0,X2,sK4) )
            & sK4 = X5
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
                ( ( ~ r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5)
                  | ~ r1_tmap_1(X1,X0,X2,X4) )
                & ( r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5)
                  | r1_tmap_1(X1,X0,X2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(sK3)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_pre_topc(sK3,X1)
        & v1_tsep_1(sK3,X1)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
                    ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5)
                      | ~ r1_tmap_1(X1,X0,sK2,X4) )
                    & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5)
                      | r1_tmap_1(X1,X0,sK2,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_pre_topc(X3,X1)
            & v1_tsep_1(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(sK1,X0,X2,X4) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5)
                          | r1_tmap_1(sK1,X0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                & m1_pre_topc(X3,sK1)
                & v1_tsep_1(X3,sK1)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
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
                          ( ( ~ r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK0,X2,X4) )
                          & ( r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5)
                            | r1_tmap_1(X1,sK0,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | ~ r1_tmap_1(sK1,sK0,sK2,sK4) )
    & ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
      | r1_tmap_1(sK1,sK0,sK2,sK4) )
    & sK4 = sK5
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_pre_topc(sK3,sK1)
    & v1_tsep_1(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f39,f45,f44,f43,f42,f41,f40])).

fof(f73,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f65,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
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
    inference(equality_resolution,[],[f60])).

fof(f10,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
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
    inference(equality_resolution,[],[f59])).

fof(f69,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f20,plain,(
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

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
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
    inference(equality_resolution,[],[f61])).

fof(f6,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f74,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_9,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1274,plain,
    ( m1_pre_topc(X0_52,X0_52)
    | ~ l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1841,plain,
    ( m1_pre_topc(X0_52,X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1274])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1266,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1848,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1266])).

cnf(c_10,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1273,plain,
    ( r1_tarski(u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_pre_topc(X1_52,X2_52)
    | ~ m1_pre_topc(X0_52,X1_52)
    | ~ v2_pre_topc(X2_52)
    | ~ l1_pre_topc(X2_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1842,plain,
    ( r1_tarski(u1_struct_0(X0_52),u1_struct_0(X1_52)) = iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X1_52,X2_52) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | l1_pre_topc(X2_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1273])).

cnf(c_2870,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_52)) = iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | m1_pre_topc(sK3,X0_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_1842])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2962,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_52)) = iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | m1_pre_topc(sK3,X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2870,c_36,c_37])).

cnf(c_16,negated_conjecture,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1270,negated_conjecture,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1845,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1270])).

cnf(c_17,negated_conjecture,
    ( sK4 = sK5 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1269,negated_conjecture,
    ( sK4 = sK5 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1902,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1845,c_1269])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1271,negated_conjecture,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1844,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1271])).

cnf(c_1919,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1844,c_1269])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_32,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_33,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_34,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_41,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_43,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_45,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1281,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_2069,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_2191,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_14,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X5)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_12,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_164,plain,
    ( ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_12])).

cnf(c_165,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_164])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_679,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_165,c_24])).

cnf(c_680,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_684,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK2,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_680,c_25])).

cnf(c_685,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_684])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_720,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_685,c_4])).

cnf(c_1256,plain,
    ( r1_tmap_1(X0_52,X1_52,k2_tmap_1(X2_52,X1_52,sK2,X0_52),X0_53)
    | ~ r1_tmap_1(X2_52,X1_52,sK2,X0_53)
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(X2_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(X2_52)
    | u1_struct_0(X2_52) != u1_struct_0(sK1)
    | u1_struct_0(X1_52) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_720])).

cnf(c_2190,plain,
    ( r1_tmap_1(X0_52,sK0,k2_tmap_1(X1_52,sK0,sK2,X0_52),X0_53)
    | ~ r1_tmap_1(X1_52,sK0,sK2,X0_53)
    | ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(sK0))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(X1_52) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1256])).

cnf(c_2353,plain,
    ( ~ r1_tmap_1(X0_52,sK0,sK2,sK5)
    | r1_tmap_1(sK3,sK0,k2_tmap_1(X0_52,sK0,sK2,sK3),sK5)
    | ~ m1_pre_topc(sK3,X0_52)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK0))))
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_2354,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | r1_tmap_1(X0_52,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(X0_52,sK0,sK2,sK3),sK5) = iProver_top
    | m1_pre_topc(sK3,X0_52) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK0)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2353])).

cnf(c_2356,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
    | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2354])).

cnf(c_2376,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1919,c_32,c_33,c_34,c_35,c_36,c_37,c_40,c_41,c_43,c_45,c_2069,c_2191,c_2356])).

cnf(c_2450,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1902,c_32,c_33,c_34,c_35,c_36,c_37,c_40,c_41,c_43,c_45,c_1919,c_2069,c_2191,c_2356])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_13,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v3_pre_topc(X5,X0)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X5)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_7,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_175,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_8])).

cnf(c_176,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_21,negated_conjecture,
    ( v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_446,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_176,c_21])).

cnf(c_447,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_449,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_27,c_26,c_20])).

cnf(c_459,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X5)
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK3) != X5
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_449])).

cnf(c_460,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X3,u1_struct_0(sK3))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_464,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,sK1)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_28,c_27,c_26])).

cnf(c_465,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X3,u1_struct_0(sK3))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_464])).

cnf(c_515,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X5)
    | X3 != X4
    | u1_struct_0(sK3) != X5 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_465])).

cnf(c_516,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_785,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
    | r1_tmap_1(sK1,X1,X2,X3)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_516])).

cnf(c_786,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_785])).

cnf(c_790,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_786,c_25])).

cnf(c_791,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
    | r1_tmap_1(sK1,X1,sK2,X2)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_790])).

cnf(c_1255,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,k2_tmap_1(sK1,X1_52,sK2,X0_52),X0_53)
    | r1_tmap_1(sK1,X1_52,sK2,X0_53)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_52))
    | ~ m1_pre_topc(X0_52,sK1)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X1_52)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(X1_52) != u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_791])).

cnf(c_1278,plain,
    ( ~ r1_tmap_1(X0_52,X1_52,k2_tmap_1(sK1,X1_52,sK2,X0_52),X0_53)
    | r1_tmap_1(sK1,X1_52,sK2,X0_53)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_52))
    | ~ m1_pre_topc(X0_52,sK1)
    | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X1_52)
    | u1_struct_0(X1_52) != u1_struct_0(sK0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1255])).

cnf(c_1860,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK0)
    | r1_tmap_1(X1_52,X0_52,k2_tmap_1(sK1,X0_52,sK2,X1_52),X0_53) != iProver_top
    | r1_tmap_1(sK1,X0_52,sK2,X0_53) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X1_52,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_52)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1278])).

cnf(c_1279,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1255])).

cnf(c_1322,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1279])).

cnf(c_1323,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK0)
    | r1_tmap_1(X1_52,X0_52,k2_tmap_1(sK1,X0_52,sK2,X1_52),X0_53) != iProver_top
    | r1_tmap_1(sK1,X0_52,sK2,X0_53) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X1_52,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_52)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1278])).

cnf(c_1275,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | m1_subset_1(u1_struct_0(X0_52),k1_zfmisc_1(u1_struct_0(X1_52)))
    | ~ l1_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2077,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1275])).

cnf(c_2078,plain,
    ( m1_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2077])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_405,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_1257,plain,
    ( v2_struct_0(X0_52)
    | ~ l1_pre_topc(X0_52)
    | ~ v1_xboole_0(u1_struct_0(X0_52)) ),
    inference(subtyping,[status(esa)],[c_405])).

cnf(c_2182,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1257])).

cnf(c_2183,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2182])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1277,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ l1_pre_topc(X1_52)
    | l1_pre_topc(X0_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1838,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1277])).

cnf(c_2251,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_1838])).

cnf(c_2507,plain,
    ( l1_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X1_52,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_52)) != iProver_top
    | r1_tmap_1(sK1,X0_52,sK2,X0_53) = iProver_top
    | r1_tmap_1(X1_52,X0_52,k2_tmap_1(sK1,X0_52,sK2,X1_52),X0_53) != iProver_top
    | u1_struct_0(X0_52) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1860,c_37,c_41,c_43,c_1322,c_1323,c_2078,c_2183,c_2251])).

cnf(c_2508,plain,
    ( u1_struct_0(X0_52) != u1_struct_0(sK0)
    | r1_tmap_1(X1_52,X0_52,k2_tmap_1(sK1,X0_52,sK2,X1_52),X0_53) != iProver_top
    | r1_tmap_1(sK1,X0_52,sK2,X0_53) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X1_52,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_52)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_2507])).

cnf(c_2526,plain,
    ( r1_tmap_1(X0_52,sK0,k2_tmap_1(sK1,sK0,sK2,X0_52),X0_53) != iProver_top
    | r1_tmap_1(sK1,sK0,sK2,X0_53) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2508])).

cnf(c_2571,plain,
    ( r1_tmap_1(X0_52,sK0,k2_tmap_1(sK1,sK0,sK2,X0_52),X0_53) != iProver_top
    | r1_tmap_1(sK1,sK0,sK2,X0_53) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(X0_52,sK1) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2526,c_32,c_33,c_34,c_40])).

cnf(c_2585,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2450,c_2571])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1267,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1847,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1267])).

cnf(c_1881,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1847,c_1269])).

cnf(c_2588,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2585,c_32,c_33,c_34,c_35,c_36,c_37,c_40,c_41,c_43,c_45,c_1881,c_1919,c_2069,c_2191,c_2356])).

cnf(c_2972,plain,
    ( m1_pre_topc(sK3,sK1) != iProver_top
    | m1_pre_topc(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2962,c_2588])).

cnf(c_3100,plain,
    ( m1_pre_topc(sK3,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2972,c_43])).

cnf(c_3105,plain,
    ( l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1841,c_3100])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3105,c_2251,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:27:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.79/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/0.99  
% 1.79/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.79/0.99  
% 1.79/0.99  ------  iProver source info
% 1.79/0.99  
% 1.79/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.79/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.79/0.99  git: non_committed_changes: false
% 1.79/0.99  git: last_make_outside_of_git: false
% 1.79/0.99  
% 1.79/0.99  ------ 
% 1.79/0.99  
% 1.79/0.99  ------ Input Options
% 1.79/0.99  
% 1.79/0.99  --out_options                           all
% 1.79/0.99  --tptp_safe_out                         true
% 1.79/0.99  --problem_path                          ""
% 1.79/0.99  --include_path                          ""
% 1.79/0.99  --clausifier                            res/vclausify_rel
% 1.79/0.99  --clausifier_options                    --mode clausify
% 1.79/0.99  --stdin                                 false
% 1.79/0.99  --stats_out                             all
% 1.79/0.99  
% 1.79/0.99  ------ General Options
% 1.79/0.99  
% 1.79/0.99  --fof                                   false
% 1.79/0.99  --time_out_real                         305.
% 1.79/0.99  --time_out_virtual                      -1.
% 1.79/0.99  --symbol_type_check                     false
% 1.79/0.99  --clausify_out                          false
% 1.79/0.99  --sig_cnt_out                           false
% 1.79/0.99  --trig_cnt_out                          false
% 1.79/0.99  --trig_cnt_out_tolerance                1.
% 1.79/0.99  --trig_cnt_out_sk_spl                   false
% 1.79/0.99  --abstr_cl_out                          false
% 1.79/0.99  
% 1.79/0.99  ------ Global Options
% 1.79/0.99  
% 1.79/0.99  --schedule                              default
% 1.79/0.99  --add_important_lit                     false
% 1.79/0.99  --prop_solver_per_cl                    1000
% 1.79/0.99  --min_unsat_core                        false
% 1.79/0.99  --soft_assumptions                      false
% 1.79/0.99  --soft_lemma_size                       3
% 1.79/0.99  --prop_impl_unit_size                   0
% 1.79/0.99  --prop_impl_unit                        []
% 1.79/0.99  --share_sel_clauses                     true
% 1.79/0.99  --reset_solvers                         false
% 1.79/0.99  --bc_imp_inh                            [conj_cone]
% 1.79/0.99  --conj_cone_tolerance                   3.
% 1.79/0.99  --extra_neg_conj                        none
% 1.79/0.99  --large_theory_mode                     true
% 1.79/0.99  --prolific_symb_bound                   200
% 1.79/0.99  --lt_threshold                          2000
% 1.79/0.99  --clause_weak_htbl                      true
% 1.79/0.99  --gc_record_bc_elim                     false
% 1.79/0.99  
% 1.79/0.99  ------ Preprocessing Options
% 1.79/0.99  
% 1.79/0.99  --preprocessing_flag                    true
% 1.79/0.99  --time_out_prep_mult                    0.1
% 1.79/0.99  --splitting_mode                        input
% 1.79/0.99  --splitting_grd                         true
% 1.79/0.99  --splitting_cvd                         false
% 1.79/0.99  --splitting_cvd_svl                     false
% 1.79/0.99  --splitting_nvd                         32
% 1.79/0.99  --sub_typing                            true
% 1.79/0.99  --prep_gs_sim                           true
% 1.79/0.99  --prep_unflatten                        true
% 1.79/0.99  --prep_res_sim                          true
% 1.79/0.99  --prep_upred                            true
% 1.79/0.99  --prep_sem_filter                       exhaustive
% 1.79/0.99  --prep_sem_filter_out                   false
% 1.79/0.99  --pred_elim                             true
% 1.79/0.99  --res_sim_input                         true
% 1.79/0.99  --eq_ax_congr_red                       true
% 1.79/0.99  --pure_diseq_elim                       true
% 1.79/0.99  --brand_transform                       false
% 1.79/0.99  --non_eq_to_eq                          false
% 1.79/0.99  --prep_def_merge                        true
% 1.79/0.99  --prep_def_merge_prop_impl              false
% 1.79/1.00  --prep_def_merge_mbd                    true
% 1.79/1.00  --prep_def_merge_tr_red                 false
% 1.79/1.00  --prep_def_merge_tr_cl                  false
% 1.79/1.00  --smt_preprocessing                     true
% 1.79/1.00  --smt_ac_axioms                         fast
% 1.79/1.00  --preprocessed_out                      false
% 1.79/1.00  --preprocessed_stats                    false
% 1.79/1.00  
% 1.79/1.00  ------ Abstraction refinement Options
% 1.79/1.00  
% 1.79/1.00  --abstr_ref                             []
% 1.79/1.00  --abstr_ref_prep                        false
% 1.79/1.00  --abstr_ref_until_sat                   false
% 1.79/1.00  --abstr_ref_sig_restrict                funpre
% 1.79/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.79/1.00  --abstr_ref_under                       []
% 1.79/1.00  
% 1.79/1.00  ------ SAT Options
% 1.79/1.00  
% 1.79/1.00  --sat_mode                              false
% 1.79/1.00  --sat_fm_restart_options                ""
% 1.79/1.00  --sat_gr_def                            false
% 1.79/1.00  --sat_epr_types                         true
% 1.79/1.00  --sat_non_cyclic_types                  false
% 1.79/1.00  --sat_finite_models                     false
% 1.79/1.00  --sat_fm_lemmas                         false
% 1.79/1.00  --sat_fm_prep                           false
% 1.79/1.00  --sat_fm_uc_incr                        true
% 1.79/1.00  --sat_out_model                         small
% 1.79/1.00  --sat_out_clauses                       false
% 1.79/1.00  
% 1.79/1.00  ------ QBF Options
% 1.79/1.00  
% 1.79/1.00  --qbf_mode                              false
% 1.79/1.00  --qbf_elim_univ                         false
% 1.79/1.00  --qbf_dom_inst                          none
% 1.79/1.00  --qbf_dom_pre_inst                      false
% 1.79/1.00  --qbf_sk_in                             false
% 1.79/1.00  --qbf_pred_elim                         true
% 1.79/1.00  --qbf_split                             512
% 1.79/1.00  
% 1.79/1.00  ------ BMC1 Options
% 1.79/1.00  
% 1.79/1.00  --bmc1_incremental                      false
% 1.79/1.00  --bmc1_axioms                           reachable_all
% 1.79/1.00  --bmc1_min_bound                        0
% 1.79/1.00  --bmc1_max_bound                        -1
% 1.79/1.00  --bmc1_max_bound_default                -1
% 1.79/1.00  --bmc1_symbol_reachability              true
% 1.79/1.00  --bmc1_property_lemmas                  false
% 1.79/1.00  --bmc1_k_induction                      false
% 1.79/1.00  --bmc1_non_equiv_states                 false
% 1.79/1.00  --bmc1_deadlock                         false
% 1.79/1.00  --bmc1_ucm                              false
% 1.79/1.00  --bmc1_add_unsat_core                   none
% 1.79/1.00  --bmc1_unsat_core_children              false
% 1.79/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.79/1.00  --bmc1_out_stat                         full
% 1.79/1.00  --bmc1_ground_init                      false
% 1.79/1.00  --bmc1_pre_inst_next_state              false
% 1.79/1.00  --bmc1_pre_inst_state                   false
% 1.79/1.00  --bmc1_pre_inst_reach_state             false
% 1.79/1.00  --bmc1_out_unsat_core                   false
% 1.79/1.00  --bmc1_aig_witness_out                  false
% 1.79/1.00  --bmc1_verbose                          false
% 1.79/1.00  --bmc1_dump_clauses_tptp                false
% 1.79/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.79/1.00  --bmc1_dump_file                        -
% 1.79/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.79/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.79/1.00  --bmc1_ucm_extend_mode                  1
% 1.79/1.00  --bmc1_ucm_init_mode                    2
% 1.79/1.00  --bmc1_ucm_cone_mode                    none
% 1.79/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.79/1.00  --bmc1_ucm_relax_model                  4
% 1.79/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.79/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.79/1.00  --bmc1_ucm_layered_model                none
% 1.79/1.00  --bmc1_ucm_max_lemma_size               10
% 1.79/1.00  
% 1.79/1.00  ------ AIG Options
% 1.79/1.00  
% 1.79/1.00  --aig_mode                              false
% 1.79/1.00  
% 1.79/1.00  ------ Instantiation Options
% 1.79/1.00  
% 1.79/1.00  --instantiation_flag                    true
% 1.79/1.00  --inst_sos_flag                         false
% 1.79/1.00  --inst_sos_phase                        true
% 1.79/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.79/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.79/1.00  --inst_lit_sel_side                     num_symb
% 1.79/1.00  --inst_solver_per_active                1400
% 1.79/1.00  --inst_solver_calls_frac                1.
% 1.79/1.00  --inst_passive_queue_type               priority_queues
% 1.79/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.79/1.00  --inst_passive_queues_freq              [25;2]
% 1.79/1.00  --inst_dismatching                      true
% 1.79/1.00  --inst_eager_unprocessed_to_passive     true
% 1.79/1.00  --inst_prop_sim_given                   true
% 1.79/1.00  --inst_prop_sim_new                     false
% 1.79/1.00  --inst_subs_new                         false
% 1.79/1.00  --inst_eq_res_simp                      false
% 1.79/1.00  --inst_subs_given                       false
% 1.79/1.00  --inst_orphan_elimination               true
% 1.79/1.00  --inst_learning_loop_flag               true
% 1.79/1.00  --inst_learning_start                   3000
% 1.79/1.00  --inst_learning_factor                  2
% 1.79/1.00  --inst_start_prop_sim_after_learn       3
% 1.79/1.00  --inst_sel_renew                        solver
% 1.79/1.00  --inst_lit_activity_flag                true
% 1.79/1.00  --inst_restr_to_given                   false
% 1.79/1.00  --inst_activity_threshold               500
% 1.79/1.00  --inst_out_proof                        true
% 1.79/1.00  
% 1.79/1.00  ------ Resolution Options
% 1.79/1.00  
% 1.79/1.00  --resolution_flag                       true
% 1.79/1.00  --res_lit_sel                           adaptive
% 1.79/1.00  --res_lit_sel_side                      none
% 1.79/1.00  --res_ordering                          kbo
% 1.79/1.00  --res_to_prop_solver                    active
% 1.79/1.00  --res_prop_simpl_new                    false
% 1.79/1.00  --res_prop_simpl_given                  true
% 1.79/1.00  --res_passive_queue_type                priority_queues
% 1.79/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.79/1.00  --res_passive_queues_freq               [15;5]
% 1.79/1.00  --res_forward_subs                      full
% 1.79/1.00  --res_backward_subs                     full
% 1.79/1.00  --res_forward_subs_resolution           true
% 1.79/1.00  --res_backward_subs_resolution          true
% 1.79/1.00  --res_orphan_elimination                true
% 1.79/1.00  --res_time_limit                        2.
% 1.79/1.00  --res_out_proof                         true
% 1.79/1.00  
% 1.79/1.00  ------ Superposition Options
% 1.79/1.00  
% 1.79/1.00  --superposition_flag                    true
% 1.79/1.00  --sup_passive_queue_type                priority_queues
% 1.79/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.79/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.79/1.00  --demod_completeness_check              fast
% 1.79/1.00  --demod_use_ground                      true
% 1.79/1.00  --sup_to_prop_solver                    passive
% 1.79/1.00  --sup_prop_simpl_new                    true
% 1.79/1.00  --sup_prop_simpl_given                  true
% 1.79/1.00  --sup_fun_splitting                     false
% 1.79/1.00  --sup_smt_interval                      50000
% 1.79/1.00  
% 1.79/1.00  ------ Superposition Simplification Setup
% 1.79/1.00  
% 1.79/1.00  --sup_indices_passive                   []
% 1.79/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.79/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.00  --sup_full_bw                           [BwDemod]
% 1.79/1.00  --sup_immed_triv                        [TrivRules]
% 1.79/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.79/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.00  --sup_immed_bw_main                     []
% 1.79/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.79/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/1.00  
% 1.79/1.00  ------ Combination Options
% 1.79/1.00  
% 1.79/1.00  --comb_res_mult                         3
% 1.79/1.00  --comb_sup_mult                         2
% 1.79/1.00  --comb_inst_mult                        10
% 1.79/1.00  
% 1.79/1.00  ------ Debug Options
% 1.79/1.00  
% 1.79/1.00  --dbg_backtrace                         false
% 1.79/1.00  --dbg_dump_prop_clauses                 false
% 1.79/1.00  --dbg_dump_prop_clauses_file            -
% 1.79/1.00  --dbg_out_stat                          false
% 1.79/1.00  ------ Parsing...
% 1.79/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.79/1.00  
% 1.79/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.79/1.00  
% 1.79/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.79/1.00  
% 1.79/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.79/1.00  ------ Proving...
% 1.79/1.00  ------ Problem Properties 
% 1.79/1.00  
% 1.79/1.00  
% 1.79/1.00  clauses                                 24
% 1.79/1.00  conjectures                             14
% 1.79/1.00  EPR                                     11
% 1.79/1.00  Horn                                    19
% 1.79/1.00  unary                                   12
% 1.79/1.00  binary                                  3
% 1.79/1.00  lits                                    76
% 1.79/1.00  lits eq                                 4
% 1.79/1.00  fd_pure                                 0
% 1.79/1.00  fd_pseudo                               0
% 1.79/1.00  fd_cond                                 0
% 1.79/1.00  fd_pseudo_cond                          0
% 1.79/1.00  AC symbols                              0
% 1.79/1.00  
% 1.79/1.00  ------ Schedule dynamic 5 is on 
% 1.79/1.00  
% 1.79/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.79/1.00  
% 1.79/1.00  
% 1.79/1.00  ------ 
% 1.79/1.00  Current options:
% 1.79/1.00  ------ 
% 1.79/1.00  
% 1.79/1.00  ------ Input Options
% 1.79/1.00  
% 1.79/1.00  --out_options                           all
% 1.79/1.00  --tptp_safe_out                         true
% 1.79/1.00  --problem_path                          ""
% 1.79/1.00  --include_path                          ""
% 1.79/1.00  --clausifier                            res/vclausify_rel
% 1.79/1.00  --clausifier_options                    --mode clausify
% 1.79/1.00  --stdin                                 false
% 1.79/1.00  --stats_out                             all
% 1.79/1.00  
% 1.79/1.00  ------ General Options
% 1.79/1.00  
% 1.79/1.00  --fof                                   false
% 1.79/1.00  --time_out_real                         305.
% 1.79/1.00  --time_out_virtual                      -1.
% 1.79/1.00  --symbol_type_check                     false
% 1.79/1.00  --clausify_out                          false
% 1.79/1.00  --sig_cnt_out                           false
% 1.79/1.00  --trig_cnt_out                          false
% 1.79/1.00  --trig_cnt_out_tolerance                1.
% 1.79/1.00  --trig_cnt_out_sk_spl                   false
% 1.79/1.00  --abstr_cl_out                          false
% 1.79/1.00  
% 1.79/1.00  ------ Global Options
% 1.79/1.00  
% 1.79/1.00  --schedule                              default
% 1.79/1.00  --add_important_lit                     false
% 1.79/1.00  --prop_solver_per_cl                    1000
% 1.79/1.00  --min_unsat_core                        false
% 1.79/1.00  --soft_assumptions                      false
% 1.79/1.00  --soft_lemma_size                       3
% 1.79/1.00  --prop_impl_unit_size                   0
% 1.79/1.00  --prop_impl_unit                        []
% 1.79/1.00  --share_sel_clauses                     true
% 1.79/1.00  --reset_solvers                         false
% 1.79/1.00  --bc_imp_inh                            [conj_cone]
% 1.79/1.00  --conj_cone_tolerance                   3.
% 1.79/1.00  --extra_neg_conj                        none
% 1.79/1.00  --large_theory_mode                     true
% 1.79/1.00  --prolific_symb_bound                   200
% 1.79/1.00  --lt_threshold                          2000
% 1.79/1.00  --clause_weak_htbl                      true
% 1.79/1.00  --gc_record_bc_elim                     false
% 1.79/1.00  
% 1.79/1.00  ------ Preprocessing Options
% 1.79/1.00  
% 1.79/1.00  --preprocessing_flag                    true
% 1.79/1.00  --time_out_prep_mult                    0.1
% 1.79/1.00  --splitting_mode                        input
% 1.79/1.00  --splitting_grd                         true
% 1.79/1.00  --splitting_cvd                         false
% 1.79/1.00  --splitting_cvd_svl                     false
% 1.79/1.00  --splitting_nvd                         32
% 1.79/1.00  --sub_typing                            true
% 1.79/1.00  --prep_gs_sim                           true
% 1.79/1.00  --prep_unflatten                        true
% 1.79/1.00  --prep_res_sim                          true
% 1.79/1.00  --prep_upred                            true
% 1.79/1.00  --prep_sem_filter                       exhaustive
% 1.79/1.00  --prep_sem_filter_out                   false
% 1.79/1.00  --pred_elim                             true
% 1.79/1.00  --res_sim_input                         true
% 1.79/1.00  --eq_ax_congr_red                       true
% 1.79/1.00  --pure_diseq_elim                       true
% 1.79/1.00  --brand_transform                       false
% 1.79/1.00  --non_eq_to_eq                          false
% 1.79/1.00  --prep_def_merge                        true
% 1.79/1.00  --prep_def_merge_prop_impl              false
% 1.79/1.00  --prep_def_merge_mbd                    true
% 1.79/1.00  --prep_def_merge_tr_red                 false
% 1.79/1.00  --prep_def_merge_tr_cl                  false
% 1.79/1.00  --smt_preprocessing                     true
% 1.79/1.00  --smt_ac_axioms                         fast
% 1.79/1.00  --preprocessed_out                      false
% 1.79/1.00  --preprocessed_stats                    false
% 1.79/1.00  
% 1.79/1.00  ------ Abstraction refinement Options
% 1.79/1.00  
% 1.79/1.00  --abstr_ref                             []
% 1.79/1.00  --abstr_ref_prep                        false
% 1.79/1.00  --abstr_ref_until_sat                   false
% 1.79/1.00  --abstr_ref_sig_restrict                funpre
% 1.79/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.79/1.00  --abstr_ref_under                       []
% 1.79/1.00  
% 1.79/1.00  ------ SAT Options
% 1.79/1.00  
% 1.79/1.00  --sat_mode                              false
% 1.79/1.00  --sat_fm_restart_options                ""
% 1.79/1.00  --sat_gr_def                            false
% 1.79/1.00  --sat_epr_types                         true
% 1.79/1.00  --sat_non_cyclic_types                  false
% 1.79/1.00  --sat_finite_models                     false
% 1.79/1.00  --sat_fm_lemmas                         false
% 1.79/1.00  --sat_fm_prep                           false
% 1.79/1.00  --sat_fm_uc_incr                        true
% 1.79/1.00  --sat_out_model                         small
% 1.79/1.00  --sat_out_clauses                       false
% 1.79/1.00  
% 1.79/1.00  ------ QBF Options
% 1.79/1.00  
% 1.79/1.00  --qbf_mode                              false
% 1.79/1.00  --qbf_elim_univ                         false
% 1.79/1.00  --qbf_dom_inst                          none
% 1.79/1.00  --qbf_dom_pre_inst                      false
% 1.79/1.00  --qbf_sk_in                             false
% 1.79/1.00  --qbf_pred_elim                         true
% 1.79/1.00  --qbf_split                             512
% 1.79/1.00  
% 1.79/1.00  ------ BMC1 Options
% 1.79/1.00  
% 1.79/1.00  --bmc1_incremental                      false
% 1.79/1.00  --bmc1_axioms                           reachable_all
% 1.79/1.00  --bmc1_min_bound                        0
% 1.79/1.00  --bmc1_max_bound                        -1
% 1.79/1.00  --bmc1_max_bound_default                -1
% 1.79/1.00  --bmc1_symbol_reachability              true
% 1.79/1.00  --bmc1_property_lemmas                  false
% 1.79/1.00  --bmc1_k_induction                      false
% 1.79/1.00  --bmc1_non_equiv_states                 false
% 1.79/1.00  --bmc1_deadlock                         false
% 1.79/1.00  --bmc1_ucm                              false
% 1.79/1.00  --bmc1_add_unsat_core                   none
% 1.79/1.00  --bmc1_unsat_core_children              false
% 1.79/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.79/1.00  --bmc1_out_stat                         full
% 1.79/1.00  --bmc1_ground_init                      false
% 1.79/1.00  --bmc1_pre_inst_next_state              false
% 1.79/1.00  --bmc1_pre_inst_state                   false
% 1.79/1.00  --bmc1_pre_inst_reach_state             false
% 1.79/1.00  --bmc1_out_unsat_core                   false
% 1.79/1.00  --bmc1_aig_witness_out                  false
% 1.79/1.00  --bmc1_verbose                          false
% 1.79/1.00  --bmc1_dump_clauses_tptp                false
% 1.79/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.79/1.00  --bmc1_dump_file                        -
% 1.79/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.79/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.79/1.00  --bmc1_ucm_extend_mode                  1
% 1.79/1.00  --bmc1_ucm_init_mode                    2
% 1.79/1.00  --bmc1_ucm_cone_mode                    none
% 1.79/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.79/1.00  --bmc1_ucm_relax_model                  4
% 1.79/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.79/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.79/1.00  --bmc1_ucm_layered_model                none
% 1.79/1.00  --bmc1_ucm_max_lemma_size               10
% 1.79/1.00  
% 1.79/1.00  ------ AIG Options
% 1.79/1.00  
% 1.79/1.00  --aig_mode                              false
% 1.79/1.00  
% 1.79/1.00  ------ Instantiation Options
% 1.79/1.00  
% 1.79/1.00  --instantiation_flag                    true
% 1.79/1.00  --inst_sos_flag                         false
% 1.79/1.00  --inst_sos_phase                        true
% 1.79/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.79/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.79/1.00  --inst_lit_sel_side                     none
% 1.79/1.00  --inst_solver_per_active                1400
% 1.79/1.00  --inst_solver_calls_frac                1.
% 1.79/1.00  --inst_passive_queue_type               priority_queues
% 1.79/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.79/1.00  --inst_passive_queues_freq              [25;2]
% 1.79/1.00  --inst_dismatching                      true
% 1.79/1.00  --inst_eager_unprocessed_to_passive     true
% 1.79/1.00  --inst_prop_sim_given                   true
% 1.79/1.00  --inst_prop_sim_new                     false
% 1.79/1.00  --inst_subs_new                         false
% 1.79/1.00  --inst_eq_res_simp                      false
% 1.79/1.00  --inst_subs_given                       false
% 1.79/1.00  --inst_orphan_elimination               true
% 1.79/1.00  --inst_learning_loop_flag               true
% 1.79/1.00  --inst_learning_start                   3000
% 1.79/1.00  --inst_learning_factor                  2
% 1.79/1.00  --inst_start_prop_sim_after_learn       3
% 1.79/1.00  --inst_sel_renew                        solver
% 1.79/1.00  --inst_lit_activity_flag                true
% 1.79/1.00  --inst_restr_to_given                   false
% 1.79/1.00  --inst_activity_threshold               500
% 1.79/1.00  --inst_out_proof                        true
% 1.79/1.00  
% 1.79/1.00  ------ Resolution Options
% 1.79/1.00  
% 1.79/1.00  --resolution_flag                       false
% 1.79/1.00  --res_lit_sel                           adaptive
% 1.79/1.00  --res_lit_sel_side                      none
% 1.79/1.00  --res_ordering                          kbo
% 1.79/1.00  --res_to_prop_solver                    active
% 1.79/1.00  --res_prop_simpl_new                    false
% 1.79/1.00  --res_prop_simpl_given                  true
% 1.79/1.00  --res_passive_queue_type                priority_queues
% 1.79/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.79/1.00  --res_passive_queues_freq               [15;5]
% 1.79/1.00  --res_forward_subs                      full
% 1.79/1.00  --res_backward_subs                     full
% 1.79/1.00  --res_forward_subs_resolution           true
% 1.79/1.00  --res_backward_subs_resolution          true
% 1.79/1.00  --res_orphan_elimination                true
% 1.79/1.00  --res_time_limit                        2.
% 1.79/1.00  --res_out_proof                         true
% 1.79/1.00  
% 1.79/1.00  ------ Superposition Options
% 1.79/1.00  
% 1.79/1.00  --superposition_flag                    true
% 1.79/1.00  --sup_passive_queue_type                priority_queues
% 1.79/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.79/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.79/1.00  --demod_completeness_check              fast
% 1.79/1.00  --demod_use_ground                      true
% 1.79/1.00  --sup_to_prop_solver                    passive
% 1.79/1.00  --sup_prop_simpl_new                    true
% 1.79/1.00  --sup_prop_simpl_given                  true
% 1.79/1.00  --sup_fun_splitting                     false
% 1.79/1.00  --sup_smt_interval                      50000
% 1.79/1.00  
% 1.79/1.00  ------ Superposition Simplification Setup
% 1.79/1.00  
% 1.79/1.00  --sup_indices_passive                   []
% 1.79/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.79/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.00  --sup_full_bw                           [BwDemod]
% 1.79/1.00  --sup_immed_triv                        [TrivRules]
% 1.79/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.79/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.00  --sup_immed_bw_main                     []
% 1.79/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.79/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/1.00  
% 1.79/1.00  ------ Combination Options
% 1.79/1.00  
% 1.79/1.00  --comb_res_mult                         3
% 1.79/1.00  --comb_sup_mult                         2
% 1.79/1.00  --comb_inst_mult                        10
% 1.79/1.00  
% 1.79/1.00  ------ Debug Options
% 1.79/1.00  
% 1.79/1.00  --dbg_backtrace                         false
% 1.79/1.00  --dbg_dump_prop_clauses                 false
% 1.79/1.00  --dbg_dump_prop_clauses_file            -
% 1.79/1.00  --dbg_out_stat                          false
% 1.79/1.00  
% 1.79/1.00  
% 1.79/1.00  
% 1.79/1.00  
% 1.79/1.00  ------ Proving...
% 1.79/1.00  
% 1.79/1.00  
% 1.79/1.00  % SZS status Theorem for theBenchmark.p
% 1.79/1.00  
% 1.79/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.79/1.00  
% 1.79/1.00  fof(f8,axiom,(
% 1.79/1.00    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/1.00  
% 1.79/1.00  fof(f25,plain,(
% 1.79/1.00    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.79/1.00    inference(ennf_transformation,[],[f8])).
% 1.79/1.00  
% 1.79/1.00  fof(f56,plain,(
% 1.79/1.00    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.79/1.00    inference(cnf_transformation,[],[f25])).
% 1.79/1.00  
% 1.79/1.00  fof(f12,conjecture,(
% 1.79/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/1.00  
% 1.79/1.00  fof(f13,negated_conjecture,(
% 1.79/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.79/1.00    inference(negated_conjecture,[],[f12])).
% 1.79/1.00  
% 1.79/1.00  fof(f32,plain,(
% 1.79/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.79/1.00    inference(ennf_transformation,[],[f13])).
% 1.79/1.00  
% 1.79/1.00  fof(f33,plain,(
% 1.79/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.79/1.00    inference(flattening,[],[f32])).
% 1.79/1.00  
% 1.79/1.00  fof(f38,plain,(
% 1.79/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.79/1.00    inference(nnf_transformation,[],[f33])).
% 1.79/1.00  
% 1.79/1.00  fof(f39,plain,(
% 1.79/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.79/1.00    inference(flattening,[],[f38])).
% 1.79/1.00  
% 1.79/1.00  fof(f45,plain,(
% 1.79/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK5) | r1_tmap_1(X1,X0,X2,X4)) & sK5 = X4 & m1_subset_1(sK5,u1_struct_0(X3)))) )),
% 1.79/1.00    introduced(choice_axiom,[])).
% 1.79/1.00  
% 1.79/1.00  fof(f44,plain,(
% 1.79/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK4)) & sK4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 1.79/1.00    introduced(choice_axiom,[])).
% 1.79/1.00  
% 1.79/1.00  fof(f43,plain,(
% 1.79/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK3,X0,k2_tmap_1(X1,X0,X2,sK3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK3,X1) & v1_tsep_1(sK3,X1) & ~v2_struct_0(sK3))) )),
% 1.79/1.00    introduced(choice_axiom,[])).
% 1.79/1.00  
% 1.79/1.00  fof(f42,plain,(
% 1.79/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5) | ~r1_tmap_1(X1,X0,sK2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK2,X3),X5) | r1_tmap_1(X1,X0,sK2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK2))) )),
% 1.79/1.00    introduced(choice_axiom,[])).
% 1.79/1.00  
% 1.79/1.00  fof(f41,plain,(
% 1.79/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5) | ~r1_tmap_1(sK1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK1,X0,X2,X3),X5) | r1_tmap_1(sK1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_pre_topc(X3,sK1) & v1_tsep_1(X3,sK1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 1.79/1.00    introduced(choice_axiom,[])).
% 1.79/1.00  
% 1.79/1.00  fof(f40,plain,(
% 1.79/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | ~r1_tmap_1(X1,sK0,X2,X4)) & (r1_tmap_1(X3,sK0,k2_tmap_1(X1,sK0,X2,X3),X5) | r1_tmap_1(X1,sK0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.79/1.00    introduced(choice_axiom,[])).
% 1.79/1.00  
% 1.79/1.00  fof(f46,plain,(
% 1.79/1.00    ((((((~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)) & (r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_pre_topc(sK3,sK1) & v1_tsep_1(sK3,sK1) & ~v2_struct_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.79/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f39,f45,f44,f43,f42,f41,f40])).
% 1.79/1.00  
% 1.79/1.00  fof(f73,plain,(
% 1.79/1.00    m1_pre_topc(sK3,sK1)),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f9,axiom,(
% 1.79/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/1.00  
% 1.79/1.00  fof(f26,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.79/1.00    inference(ennf_transformation,[],[f9])).
% 1.79/1.00  
% 1.79/1.00  fof(f27,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.79/1.00    inference(flattening,[],[f26])).
% 1.79/1.00  
% 1.79/1.00  fof(f36,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.79/1.00    inference(nnf_transformation,[],[f27])).
% 1.79/1.00  
% 1.79/1.00  fof(f58,plain,(
% 1.79/1.00    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.79/1.00    inference(cnf_transformation,[],[f36])).
% 1.79/1.00  
% 1.79/1.00  fof(f66,plain,(
% 1.79/1.00    v2_pre_topc(sK1)),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f67,plain,(
% 1.79/1.00    l1_pre_topc(sK1)),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f77,plain,(
% 1.79/1.00    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f76,plain,(
% 1.79/1.00    sK4 = sK5),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f78,plain,(
% 1.79/1.00    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f62,plain,(
% 1.79/1.00    ~v2_struct_0(sK0)),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f63,plain,(
% 1.79/1.00    v2_pre_topc(sK0)),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f64,plain,(
% 1.79/1.00    l1_pre_topc(sK0)),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f65,plain,(
% 1.79/1.00    ~v2_struct_0(sK1)),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f70,plain,(
% 1.79/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f71,plain,(
% 1.79/1.00    ~v2_struct_0(sK3)),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f75,plain,(
% 1.79/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f11,axiom,(
% 1.79/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/1.00  
% 1.79/1.00  fof(f30,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/1.00    inference(ennf_transformation,[],[f11])).
% 1.79/1.00  
% 1.79/1.00  fof(f31,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/1.00    inference(flattening,[],[f30])).
% 1.79/1.00  
% 1.79/1.00  fof(f37,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/1.00    inference(nnf_transformation,[],[f31])).
% 1.79/1.00  
% 1.79/1.00  fof(f60,plain,(
% 1.79/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/1.00    inference(cnf_transformation,[],[f37])).
% 1.79/1.00  
% 1.79/1.00  fof(f84,plain,(
% 1.79/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/1.00    inference(equality_resolution,[],[f60])).
% 1.79/1.00  
% 1.79/1.00  fof(f10,axiom,(
% 1.79/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/1.00  
% 1.79/1.00  fof(f28,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/1.00    inference(ennf_transformation,[],[f10])).
% 1.79/1.00  
% 1.79/1.00  fof(f29,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/1.00    inference(flattening,[],[f28])).
% 1.79/1.00  
% 1.79/1.00  fof(f59,plain,(
% 1.79/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/1.00    inference(cnf_transformation,[],[f29])).
% 1.79/1.00  
% 1.79/1.00  fof(f82,plain,(
% 1.79/1.00    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/1.00    inference(equality_resolution,[],[f59])).
% 1.79/1.00  
% 1.79/1.00  fof(f69,plain,(
% 1.79/1.00    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f68,plain,(
% 1.79/1.00    v1_funct_1(sK2)),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f5,axiom,(
% 1.79/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/1.00  
% 1.79/1.00  fof(f20,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/1.00    inference(ennf_transformation,[],[f5])).
% 1.79/1.00  
% 1.79/1.00  fof(f21,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/1.00    inference(flattening,[],[f20])).
% 1.79/1.00  
% 1.79/1.00  fof(f51,plain,(
% 1.79/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/1.00    inference(cnf_transformation,[],[f21])).
% 1.79/1.00  
% 1.79/1.00  fof(f1,axiom,(
% 1.79/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/1.00  
% 1.79/1.00  fof(f14,plain,(
% 1.79/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.79/1.00    inference(ennf_transformation,[],[f1])).
% 1.79/1.00  
% 1.79/1.00  fof(f15,plain,(
% 1.79/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.79/1.00    inference(flattening,[],[f14])).
% 1.79/1.00  
% 1.79/1.00  fof(f47,plain,(
% 1.79/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.79/1.00    inference(cnf_transformation,[],[f15])).
% 1.79/1.00  
% 1.79/1.00  fof(f61,plain,(
% 1.79/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/1.00    inference(cnf_transformation,[],[f37])).
% 1.79/1.00  
% 1.79/1.00  fof(f83,plain,(
% 1.79/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/1.00    inference(equality_resolution,[],[f61])).
% 1.79/1.00  
% 1.79/1.00  fof(f6,axiom,(
% 1.79/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/1.00  
% 1.79/1.00  fof(f22,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.79/1.00    inference(ennf_transformation,[],[f6])).
% 1.79/1.00  
% 1.79/1.00  fof(f23,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.79/1.00    inference(flattening,[],[f22])).
% 1.79/1.00  
% 1.79/1.00  fof(f34,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.79/1.00    inference(nnf_transformation,[],[f23])).
% 1.79/1.00  
% 1.79/1.00  fof(f35,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.79/1.00    inference(flattening,[],[f34])).
% 1.79/1.00  
% 1.79/1.00  fof(f52,plain,(
% 1.79/1.00    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.79/1.00    inference(cnf_transformation,[],[f35])).
% 1.79/1.00  
% 1.79/1.00  fof(f81,plain,(
% 1.79/1.00    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.79/1.00    inference(equality_resolution,[],[f52])).
% 1.79/1.00  
% 1.79/1.00  fof(f7,axiom,(
% 1.79/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/1.00  
% 1.79/1.00  fof(f24,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.79/1.00    inference(ennf_transformation,[],[f7])).
% 1.79/1.00  
% 1.79/1.00  fof(f55,plain,(
% 1.79/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.79/1.00    inference(cnf_transformation,[],[f24])).
% 1.79/1.00  
% 1.79/1.00  fof(f72,plain,(
% 1.79/1.00    v1_tsep_1(sK3,sK1)),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  fof(f2,axiom,(
% 1.79/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/1.00  
% 1.79/1.00  fof(f16,plain,(
% 1.79/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.79/1.00    inference(ennf_transformation,[],[f2])).
% 1.79/1.00  
% 1.79/1.00  fof(f48,plain,(
% 1.79/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.79/1.00    inference(cnf_transformation,[],[f16])).
% 1.79/1.00  
% 1.79/1.00  fof(f4,axiom,(
% 1.79/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/1.00  
% 1.79/1.00  fof(f18,plain,(
% 1.79/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.79/1.00    inference(ennf_transformation,[],[f4])).
% 1.79/1.00  
% 1.79/1.00  fof(f19,plain,(
% 1.79/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.79/1.00    inference(flattening,[],[f18])).
% 1.79/1.00  
% 1.79/1.00  fof(f50,plain,(
% 1.79/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.79/1.00    inference(cnf_transformation,[],[f19])).
% 1.79/1.00  
% 1.79/1.00  fof(f3,axiom,(
% 1.79/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.79/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.79/1.00  
% 1.79/1.00  fof(f17,plain,(
% 1.79/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.79/1.00    inference(ennf_transformation,[],[f3])).
% 1.79/1.00  
% 1.79/1.00  fof(f49,plain,(
% 1.79/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.79/1.00    inference(cnf_transformation,[],[f17])).
% 1.79/1.00  
% 1.79/1.00  fof(f74,plain,(
% 1.79/1.00    m1_subset_1(sK4,u1_struct_0(sK1))),
% 1.79/1.00    inference(cnf_transformation,[],[f46])).
% 1.79/1.00  
% 1.79/1.00  cnf(c_9,plain,
% 1.79/1.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 1.79/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1274,plain,
% 1.79/1.00      ( m1_pre_topc(X0_52,X0_52) | ~ l1_pre_topc(X0_52) ),
% 1.79/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1841,plain,
% 1.79/1.00      ( m1_pre_topc(X0_52,X0_52) = iProver_top
% 1.79/1.00      | l1_pre_topc(X0_52) != iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1274]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_20,negated_conjecture,
% 1.79/1.00      ( m1_pre_topc(sK3,sK1) ),
% 1.79/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1266,negated_conjecture,
% 1.79/1.00      ( m1_pre_topc(sK3,sK1) ),
% 1.79/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1848,plain,
% 1.79/1.00      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1266]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_10,plain,
% 1.79/1.00      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 1.79/1.00      | ~ m1_pre_topc(X0,X2)
% 1.79/1.00      | ~ m1_pre_topc(X0,X1)
% 1.79/1.00      | ~ m1_pre_topc(X1,X2)
% 1.79/1.00      | ~ v2_pre_topc(X2)
% 1.79/1.00      | ~ l1_pre_topc(X2) ),
% 1.79/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1273,plain,
% 1.79/1.00      ( r1_tarski(u1_struct_0(X0_52),u1_struct_0(X1_52))
% 1.79/1.00      | ~ m1_pre_topc(X0_52,X2_52)
% 1.79/1.00      | ~ m1_pre_topc(X1_52,X2_52)
% 1.79/1.00      | ~ m1_pre_topc(X0_52,X1_52)
% 1.79/1.00      | ~ v2_pre_topc(X2_52)
% 1.79/1.00      | ~ l1_pre_topc(X2_52) ),
% 1.79/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1842,plain,
% 1.79/1.00      ( r1_tarski(u1_struct_0(X0_52),u1_struct_0(X1_52)) = iProver_top
% 1.79/1.00      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 1.79/1.00      | m1_pre_topc(X1_52,X2_52) != iProver_top
% 1.79/1.00      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 1.79/1.00      | v2_pre_topc(X2_52) != iProver_top
% 1.79/1.00      | l1_pre_topc(X2_52) != iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1273]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2870,plain,
% 1.79/1.00      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_52)) = iProver_top
% 1.79/1.00      | m1_pre_topc(X0_52,sK1) != iProver_top
% 1.79/1.00      | m1_pre_topc(sK3,X0_52) != iProver_top
% 1.79/1.00      | v2_pre_topc(sK1) != iProver_top
% 1.79/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.79/1.00      inference(superposition,[status(thm)],[c_1848,c_1842]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_27,negated_conjecture,
% 1.79/1.00      ( v2_pre_topc(sK1) ),
% 1.79/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_36,plain,
% 1.79/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_26,negated_conjecture,
% 1.79/1.00      ( l1_pre_topc(sK1) ),
% 1.79/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_37,plain,
% 1.79/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2962,plain,
% 1.79/1.00      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_52)) = iProver_top
% 1.79/1.00      | m1_pre_topc(X0_52,sK1) != iProver_top
% 1.79/1.00      | m1_pre_topc(sK3,X0_52) != iProver_top ),
% 1.79/1.00      inference(global_propositional_subsumption,
% 1.79/1.00                [status(thm)],
% 1.79/1.00                [c_2870,c_36,c_37]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_16,negated_conjecture,
% 1.79/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.79/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.79/1.00      inference(cnf_transformation,[],[f77]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1270,negated_conjecture,
% 1.79/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.79/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.79/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1845,plain,
% 1.79/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK4) = iProver_top
% 1.79/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1270]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_17,negated_conjecture,
% 1.79/1.00      ( sK4 = sK5 ),
% 1.79/1.00      inference(cnf_transformation,[],[f76]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1269,negated_conjecture,
% 1.79/1.00      ( sK4 = sK5 ),
% 1.79/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1902,plain,
% 1.79/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.79/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
% 1.79/1.00      inference(light_normalisation,[status(thm)],[c_1845,c_1269]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_15,negated_conjecture,
% 1.79/1.00      ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.79/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.79/1.00      inference(cnf_transformation,[],[f78]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1271,negated_conjecture,
% 1.79/1.00      ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
% 1.79/1.00      | ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) ),
% 1.79/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1844,plain,
% 1.79/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK4) != iProver_top
% 1.79/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1271]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1919,plain,
% 1.79/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
% 1.79/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) != iProver_top ),
% 1.79/1.00      inference(light_normalisation,[status(thm)],[c_1844,c_1269]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_31,negated_conjecture,
% 1.79/1.00      ( ~ v2_struct_0(sK0) ),
% 1.79/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_32,plain,
% 1.79/1.00      ( v2_struct_0(sK0) != iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_30,negated_conjecture,
% 1.79/1.00      ( v2_pre_topc(sK0) ),
% 1.79/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_33,plain,
% 1.79/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_29,negated_conjecture,
% 1.79/1.00      ( l1_pre_topc(sK0) ),
% 1.79/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_34,plain,
% 1.79/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_28,negated_conjecture,
% 1.79/1.00      ( ~ v2_struct_0(sK1) ),
% 1.79/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_35,plain,
% 1.79/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_23,negated_conjecture,
% 1.79/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 1.79/1.00      inference(cnf_transformation,[],[f70]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_40,plain,
% 1.79/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_22,negated_conjecture,
% 1.79/1.00      ( ~ v2_struct_0(sK3) ),
% 1.79/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_41,plain,
% 1.79/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_43,plain,
% 1.79/1.00      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_18,negated_conjecture,
% 1.79/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 1.79/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_45,plain,
% 1.79/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1281,plain,( X0_53 = X0_53 ),theory(equality) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2069,plain,
% 1.79/1.00      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 1.79/1.00      inference(instantiation,[status(thm)],[c_1281]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2191,plain,
% 1.79/1.00      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 1.79/1.00      inference(instantiation,[status(thm)],[c_1281]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_14,plain,
% 1.79/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.79/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.79/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.79/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.79/1.00      | ~ v3_pre_topc(X5,X0)
% 1.79/1.00      | ~ m1_pre_topc(X4,X0)
% 1.79/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.79/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ r2_hidden(X3,X5)
% 1.79/1.00      | ~ v1_funct_1(X2)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | ~ v2_pre_topc(X0)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(X4)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | ~ l1_pre_topc(X0) ),
% 1.79/1.00      inference(cnf_transformation,[],[f84]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_12,plain,
% 1.79/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.79/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.79/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.79/1.00      | ~ m1_pre_topc(X4,X0)
% 1.79/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ v1_funct_1(X2)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | ~ v2_pre_topc(X0)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(X4)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | ~ l1_pre_topc(X0) ),
% 1.79/1.00      inference(cnf_transformation,[],[f82]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_164,plain,
% 1.79/1.00      ( ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.79/1.00      | ~ r1_tmap_1(X0,X1,X2,X3)
% 1.79/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.79/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.79/1.00      | ~ m1_pre_topc(X4,X0)
% 1.79/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.79/1.00      | ~ v1_funct_1(X2)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | ~ v2_pre_topc(X0)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(X4)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | ~ l1_pre_topc(X0) ),
% 1.79/1.00      inference(global_propositional_subsumption,
% 1.79/1.00                [status(thm)],
% 1.79/1.00                [c_14,c_12]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_165,plain,
% 1.79/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.79/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.79/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.79/1.00      | ~ m1_pre_topc(X4,X0)
% 1.79/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ v1_funct_1(X2)
% 1.79/1.00      | ~ v2_pre_topc(X0)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | v2_struct_0(X4)
% 1.79/1.00      | ~ l1_pre_topc(X0)
% 1.79/1.00      | ~ l1_pre_topc(X1) ),
% 1.79/1.00      inference(renaming,[status(thm)],[c_164]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_24,negated_conjecture,
% 1.79/1.00      ( v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 1.79/1.00      inference(cnf_transformation,[],[f69]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_679,plain,
% 1.79/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.79/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.79/1.00      | ~ m1_pre_topc(X4,X0)
% 1.79/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ v1_funct_1(X2)
% 1.79/1.00      | ~ v2_pre_topc(X0)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | v2_struct_0(X4)
% 1.79/1.00      | ~ l1_pre_topc(X0)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.79/1.00      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.79/1.00      | sK2 != X2 ),
% 1.79/1.00      inference(resolution_lifted,[status(thm)],[c_165,c_24]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_680,plain,
% 1.79/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.79/1.00      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.79/1.00      | ~ m1_pre_topc(X0,X2)
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.79/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.79/1.00      | ~ v1_funct_1(sK2)
% 1.79/1.00      | ~ v2_pre_topc(X2)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | v2_struct_0(X2)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | ~ l1_pre_topc(X2)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.79/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.79/1.00      inference(unflattening,[status(thm)],[c_679]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_25,negated_conjecture,
% 1.79/1.00      ( v1_funct_1(sK2) ),
% 1.79/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_684,plain,
% 1.79/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ m1_pre_topc(X0,X2)
% 1.79/1.00      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.79/1.00      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.79/1.00      | ~ v2_pre_topc(X2)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | v2_struct_0(X2)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | ~ l1_pre_topc(X2)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.79/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.79/1.00      inference(global_propositional_subsumption,
% 1.79/1.00                [status(thm)],
% 1.79/1.00                [c_680,c_25]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_685,plain,
% 1.79/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.79/1.00      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.79/1.00      | ~ m1_pre_topc(X0,X2)
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.79/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | ~ v2_pre_topc(X2)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | v2_struct_0(X2)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | ~ l1_pre_topc(X2)
% 1.79/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.79/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.79/1.00      inference(renaming,[status(thm)],[c_684]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_4,plain,
% 1.79/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.79/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.79/1.00      | m1_subset_1(X2,u1_struct_0(X1))
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | ~ l1_pre_topc(X1) ),
% 1.79/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_720,plain,
% 1.79/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK2,X0),X3)
% 1.79/1.00      | ~ r1_tmap_1(X2,X1,sK2,X3)
% 1.79/1.00      | ~ m1_pre_topc(X0,X2)
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | ~ v2_pre_topc(X2)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | v2_struct_0(X2)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | ~ l1_pre_topc(X2)
% 1.79/1.00      | u1_struct_0(X2) != u1_struct_0(sK1)
% 1.79/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.79/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_685,c_4]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1256,plain,
% 1.79/1.00      ( r1_tmap_1(X0_52,X1_52,k2_tmap_1(X2_52,X1_52,sK2,X0_52),X0_53)
% 1.79/1.00      | ~ r1_tmap_1(X2_52,X1_52,sK2,X0_53)
% 1.79/1.00      | ~ m1_pre_topc(X0_52,X2_52)
% 1.79/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 1.79/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 1.79/1.00      | ~ v2_pre_topc(X1_52)
% 1.79/1.00      | ~ v2_pre_topc(X2_52)
% 1.79/1.00      | v2_struct_0(X0_52)
% 1.79/1.00      | v2_struct_0(X1_52)
% 1.79/1.00      | v2_struct_0(X2_52)
% 1.79/1.00      | ~ l1_pre_topc(X1_52)
% 1.79/1.00      | ~ l1_pre_topc(X2_52)
% 1.79/1.00      | u1_struct_0(X2_52) != u1_struct_0(sK1)
% 1.79/1.00      | u1_struct_0(X1_52) != u1_struct_0(sK0) ),
% 1.79/1.00      inference(subtyping,[status(esa)],[c_720]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2190,plain,
% 1.79/1.00      ( r1_tmap_1(X0_52,sK0,k2_tmap_1(X1_52,sK0,sK2,X0_52),X0_53)
% 1.79/1.00      | ~ r1_tmap_1(X1_52,sK0,sK2,X0_53)
% 1.79/1.00      | ~ m1_pre_topc(X0_52,X1_52)
% 1.79/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 1.79/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(sK0))))
% 1.79/1.00      | ~ v2_pre_topc(X1_52)
% 1.79/1.00      | ~ v2_pre_topc(sK0)
% 1.79/1.00      | v2_struct_0(X0_52)
% 1.79/1.00      | v2_struct_0(X1_52)
% 1.79/1.00      | v2_struct_0(sK0)
% 1.79/1.00      | ~ l1_pre_topc(X1_52)
% 1.79/1.00      | ~ l1_pre_topc(sK0)
% 1.79/1.00      | u1_struct_0(X1_52) != u1_struct_0(sK1)
% 1.79/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.79/1.00      inference(instantiation,[status(thm)],[c_1256]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2353,plain,
% 1.79/1.00      ( ~ r1_tmap_1(X0_52,sK0,sK2,sK5)
% 1.79/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(X0_52,sK0,sK2,sK3),sK5)
% 1.79/1.00      | ~ m1_pre_topc(sK3,X0_52)
% 1.79/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 1.79/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK0))))
% 1.79/1.00      | ~ v2_pre_topc(X0_52)
% 1.79/1.00      | ~ v2_pre_topc(sK0)
% 1.79/1.00      | v2_struct_0(X0_52)
% 1.79/1.00      | v2_struct_0(sK0)
% 1.79/1.00      | v2_struct_0(sK3)
% 1.79/1.00      | ~ l1_pre_topc(X0_52)
% 1.79/1.00      | ~ l1_pre_topc(sK0)
% 1.79/1.00      | u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.79/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.79/1.00      inference(instantiation,[status(thm)],[c_2190]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2354,plain,
% 1.79/1.00      ( u1_struct_0(X0_52) != u1_struct_0(sK1)
% 1.79/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 1.79/1.00      | r1_tmap_1(X0_52,sK0,sK2,sK5) != iProver_top
% 1.79/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(X0_52,sK0,sK2,sK3),sK5) = iProver_top
% 1.79/1.00      | m1_pre_topc(sK3,X0_52) != iProver_top
% 1.79/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 1.79/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK0)))) != iProver_top
% 1.79/1.00      | v2_pre_topc(X0_52) != iProver_top
% 1.79/1.00      | v2_pre_topc(sK0) != iProver_top
% 1.79/1.00      | v2_struct_0(X0_52) = iProver_top
% 1.79/1.00      | v2_struct_0(sK0) = iProver_top
% 1.79/1.00      | v2_struct_0(sK3) = iProver_top
% 1.79/1.00      | l1_pre_topc(X0_52) != iProver_top
% 1.79/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_2353]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2356,plain,
% 1.79/1.00      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.79/1.00      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 1.79/1.00      | r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top
% 1.79/1.00      | r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top
% 1.79/1.00      | m1_pre_topc(sK3,sK1) != iProver_top
% 1.79/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 1.79/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 1.79/1.00      | v2_pre_topc(sK1) != iProver_top
% 1.79/1.00      | v2_pre_topc(sK0) != iProver_top
% 1.79/1.00      | v2_struct_0(sK1) = iProver_top
% 1.79/1.00      | v2_struct_0(sK0) = iProver_top
% 1.79/1.00      | v2_struct_0(sK3) = iProver_top
% 1.79/1.00      | l1_pre_topc(sK1) != iProver_top
% 1.79/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 1.79/1.00      inference(instantiation,[status(thm)],[c_2354]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2376,plain,
% 1.79/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5) != iProver_top ),
% 1.79/1.00      inference(global_propositional_subsumption,
% 1.79/1.00                [status(thm)],
% 1.79/1.00                [c_1919,c_32,c_33,c_34,c_35,c_36,c_37,c_40,c_41,c_43,
% 1.79/1.00                 c_45,c_2069,c_2191,c_2356]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2450,plain,
% 1.79/1.00      ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) = iProver_top ),
% 1.79/1.00      inference(global_propositional_subsumption,
% 1.79/1.00                [status(thm)],
% 1.79/1.00                [c_1902,c_32,c_33,c_34,c_35,c_36,c_37,c_40,c_41,c_43,
% 1.79/1.00                 c_45,c_1919,c_2069,c_2191,c_2356]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_0,plain,
% 1.79/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.79/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_13,plain,
% 1.79/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 1.79/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.79/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.79/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.79/1.00      | ~ v3_pre_topc(X5,X0)
% 1.79/1.00      | ~ m1_pre_topc(X4,X0)
% 1.79/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.79/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ r2_hidden(X3,X5)
% 1.79/1.00      | ~ v1_funct_1(X2)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | ~ v2_pre_topc(X0)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(X4)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | ~ l1_pre_topc(X0) ),
% 1.79/1.00      inference(cnf_transformation,[],[f83]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_7,plain,
% 1.79/1.00      ( ~ v1_tsep_1(X0,X1)
% 1.79/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.79/1.00      | ~ m1_pre_topc(X0,X1)
% 1.79/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | ~ l1_pre_topc(X1) ),
% 1.79/1.00      inference(cnf_transformation,[],[f81]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_8,plain,
% 1.79/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.79/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.79/1.00      | ~ l1_pre_topc(X1) ),
% 1.79/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_175,plain,
% 1.79/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.79/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.79/1.00      | ~ v1_tsep_1(X0,X1)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | ~ l1_pre_topc(X1) ),
% 1.79/1.00      inference(global_propositional_subsumption,[status(thm)],[c_7,c_8]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_176,plain,
% 1.79/1.00      ( ~ v1_tsep_1(X0,X1)
% 1.79/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.79/1.00      | ~ m1_pre_topc(X0,X1)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | ~ l1_pre_topc(X1) ),
% 1.79/1.00      inference(renaming,[status(thm)],[c_175]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_21,negated_conjecture,
% 1.79/1.00      ( v1_tsep_1(sK3,sK1) ),
% 1.79/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_446,plain,
% 1.79/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 1.79/1.00      | ~ m1_pre_topc(X0,X1)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | sK1 != X1
% 1.79/1.00      | sK3 != X0 ),
% 1.79/1.00      inference(resolution_lifted,[status(thm)],[c_176,c_21]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_447,plain,
% 1.79/1.00      ( v3_pre_topc(u1_struct_0(sK3),sK1)
% 1.79/1.00      | ~ m1_pre_topc(sK3,sK1)
% 1.79/1.00      | ~ v2_pre_topc(sK1)
% 1.79/1.00      | ~ l1_pre_topc(sK1) ),
% 1.79/1.00      inference(unflattening,[status(thm)],[c_446]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_449,plain,
% 1.79/1.00      ( v3_pre_topc(u1_struct_0(sK3),sK1) ),
% 1.79/1.00      inference(global_propositional_subsumption,
% 1.79/1.00                [status(thm)],
% 1.79/1.00                [c_447,c_27,c_26,c_20]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_459,plain,
% 1.79/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 1.79/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.79/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.79/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.79/1.00      | ~ m1_pre_topc(X4,X0)
% 1.79/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.79/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ r2_hidden(X3,X5)
% 1.79/1.00      | ~ v1_funct_1(X2)
% 1.79/1.00      | ~ v2_pre_topc(X0)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | v2_struct_0(X4)
% 1.79/1.00      | ~ l1_pre_topc(X0)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | u1_struct_0(sK3) != X5
% 1.79/1.00      | sK1 != X0 ),
% 1.79/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_449]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_460,plain,
% 1.79/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.79/1.00      | r1_tmap_1(sK1,X1,X2,X3)
% 1.79/1.00      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.79/1.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.79/1.00      | ~ m1_pre_topc(X0,sK1)
% 1.79/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.79/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.79/1.00      | ~ r2_hidden(X3,u1_struct_0(sK3))
% 1.79/1.00      | ~ v1_funct_1(X2)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | ~ v2_pre_topc(sK1)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(sK1)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | ~ l1_pre_topc(sK1) ),
% 1.79/1.00      inference(unflattening,[status(thm)],[c_459]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_464,plain,
% 1.79/1.00      ( ~ l1_pre_topc(X1)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | ~ v1_funct_1(X2)
% 1.79/1.00      | ~ r2_hidden(X3,u1_struct_0(sK3))
% 1.79/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.79/1.00      | ~ m1_pre_topc(X0,sK1)
% 1.79/1.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.79/1.00      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.79/1.00      | r1_tmap_1(sK1,X1,X2,X3)
% 1.79/1.00      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | v2_struct_0(X0) ),
% 1.79/1.00      inference(global_propositional_subsumption,
% 1.79/1.00                [status(thm)],
% 1.79/1.00                [c_460,c_28,c_27,c_26]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_465,plain,
% 1.79/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.79/1.00      | r1_tmap_1(sK1,X1,X2,X3)
% 1.79/1.00      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.79/1.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.79/1.00      | ~ m1_pre_topc(X0,sK1)
% 1.79/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.79/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.79/1.00      | ~ r2_hidden(X3,u1_struct_0(sK3))
% 1.79/1.00      | ~ v1_funct_1(X2)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | ~ l1_pre_topc(X1) ),
% 1.79/1.00      inference(renaming,[status(thm)],[c_464]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_515,plain,
% 1.79/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.79/1.00      | r1_tmap_1(sK1,X1,X2,X3)
% 1.79/1.00      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.79/1.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.79/1.00      | ~ m1_pre_topc(X0,sK1)
% 1.79/1.00      | ~ m1_subset_1(X4,X5)
% 1.79/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.79/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.79/1.00      | ~ v1_funct_1(X2)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | v1_xboole_0(X5)
% 1.79/1.00      | X3 != X4
% 1.79/1.00      | u1_struct_0(sK3) != X5 ),
% 1.79/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_465]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_516,plain,
% 1.79/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.79/1.00      | r1_tmap_1(sK1,X1,X2,X3)
% 1.79/1.00      | ~ v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
% 1.79/1.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.79/1.00      | ~ m1_pre_topc(X0,sK1)
% 1.79/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.79/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.79/1.00      | ~ v1_funct_1(X2)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.79/1.00      inference(unflattening,[status(thm)],[c_515]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_785,plain,
% 1.79/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,X2,X0),X3)
% 1.79/1.00      | r1_tmap_1(sK1,X1,X2,X3)
% 1.79/1.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.79/1.00      | ~ m1_pre_topc(X0,sK1)
% 1.79/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.79/1.00      | ~ m1_subset_1(X3,u1_struct_0(sK3))
% 1.79/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.79/1.00      | ~ v1_funct_1(X2)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 1.79/1.00      | u1_struct_0(X1) != u1_struct_0(sK0)
% 1.79/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.79/1.00      | sK2 != X2 ),
% 1.79/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_516]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_786,plain,
% 1.79/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.79/1.00      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.79/1.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.79/1.00      | ~ m1_pre_topc(X0,sK1)
% 1.79/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.79/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.79/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.79/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.79/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.79/1.00      | ~ v1_funct_1(sK2)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 1.79/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.79/1.00      inference(unflattening,[status(thm)],[c_785]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_790,plain,
% 1.79/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.79/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.79/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.79/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.79/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.79/1.00      | ~ m1_pre_topc(X0,sK1)
% 1.79/1.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.79/1.00      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.79/1.00      | ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 1.79/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.79/1.00      inference(global_propositional_subsumption,
% 1.79/1.00                [status(thm)],
% 1.79/1.00                [c_786,c_25]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_791,plain,
% 1.79/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(sK1,X1,sK2,X0),X2)
% 1.79/1.00      | r1_tmap_1(sK1,X1,sK2,X2)
% 1.79/1.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 1.79/1.00      | ~ m1_pre_topc(X0,sK1)
% 1.79/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.79/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.79/1.00      | ~ m1_subset_1(X2,u1_struct_0(sK3))
% 1.79/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.79/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 1.79/1.00      | ~ v2_pre_topc(X1)
% 1.79/1.00      | v2_struct_0(X0)
% 1.79/1.00      | v2_struct_0(X1)
% 1.79/1.00      | ~ l1_pre_topc(X1)
% 1.79/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 1.79/1.00      | u1_struct_0(X1) != u1_struct_0(sK0) ),
% 1.79/1.00      inference(renaming,[status(thm)],[c_790]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1255,plain,
% 1.79/1.00      ( ~ r1_tmap_1(X0_52,X1_52,k2_tmap_1(sK1,X1_52,sK2,X0_52),X0_53)
% 1.79/1.00      | r1_tmap_1(sK1,X1_52,sK2,X0_53)
% 1.79/1.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_52))
% 1.79/1.00      | ~ m1_pre_topc(X0_52,sK1)
% 1.79/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 1.79/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK1))
% 1.79/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 1.79/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.79/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1_52))))
% 1.79/1.00      | ~ v2_pre_topc(X1_52)
% 1.79/1.00      | v2_struct_0(X0_52)
% 1.79/1.00      | v2_struct_0(X1_52)
% 1.79/1.00      | ~ l1_pre_topc(X1_52)
% 1.79/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 1.79/1.00      | u1_struct_0(X1_52) != u1_struct_0(sK0) ),
% 1.79/1.00      inference(subtyping,[status(esa)],[c_791]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1278,plain,
% 1.79/1.00      ( ~ r1_tmap_1(X0_52,X1_52,k2_tmap_1(sK1,X1_52,sK2,X0_52),X0_53)
% 1.79/1.00      | r1_tmap_1(sK1,X1_52,sK2,X0_53)
% 1.79/1.00      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_52))
% 1.79/1.00      | ~ m1_pre_topc(X0_52,sK1)
% 1.79/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(X0_52))
% 1.79/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK1))
% 1.79/1.00      | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
% 1.79/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1_52))))
% 1.79/1.00      | ~ v2_pre_topc(X1_52)
% 1.79/1.00      | v2_struct_0(X0_52)
% 1.79/1.00      | v2_struct_0(X1_52)
% 1.79/1.00      | ~ l1_pre_topc(X1_52)
% 1.79/1.00      | u1_struct_0(X1_52) != u1_struct_0(sK0)
% 1.79/1.00      | ~ sP0_iProver_split ),
% 1.79/1.00      inference(splitting,
% 1.79/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.79/1.00                [c_1255]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1860,plain,
% 1.79/1.00      ( u1_struct_0(X0_52) != u1_struct_0(sK0)
% 1.79/1.00      | r1_tmap_1(X1_52,X0_52,k2_tmap_1(sK1,X0_52,sK2,X1_52),X0_53) != iProver_top
% 1.79/1.00      | r1_tmap_1(sK1,X0_52,sK2,X0_53) = iProver_top
% 1.79/1.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_52)) != iProver_top
% 1.79/1.00      | m1_pre_topc(X1_52,sK1) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 1.79/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_52)))) != iProver_top
% 1.79/1.00      | v2_pre_topc(X0_52) != iProver_top
% 1.79/1.00      | v2_struct_0(X0_52) = iProver_top
% 1.79/1.00      | v2_struct_0(X1_52) = iProver_top
% 1.79/1.00      | l1_pre_topc(X0_52) != iProver_top
% 1.79/1.00      | sP0_iProver_split != iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1278]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1279,plain,
% 1.79/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.79/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 1.79/1.00      | sP0_iProver_split ),
% 1.79/1.00      inference(splitting,
% 1.79/1.00                [splitting(split),new_symbols(definition,[])],
% 1.79/1.00                [c_1255]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1322,plain,
% 1.79/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.79/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 1.79/1.00      | sP0_iProver_split = iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1279]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1323,plain,
% 1.79/1.00      ( u1_struct_0(X0_52) != u1_struct_0(sK0)
% 1.79/1.00      | r1_tmap_1(X1_52,X0_52,k2_tmap_1(sK1,X0_52,sK2,X1_52),X0_53) != iProver_top
% 1.79/1.00      | r1_tmap_1(sK1,X0_52,sK2,X0_53) = iProver_top
% 1.79/1.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_52)) != iProver_top
% 1.79/1.00      | m1_pre_topc(X1_52,sK1) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 1.79/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_52)))) != iProver_top
% 1.79/1.00      | v2_pre_topc(X0_52) != iProver_top
% 1.79/1.00      | v2_struct_0(X0_52) = iProver_top
% 1.79/1.00      | v2_struct_0(X1_52) = iProver_top
% 1.79/1.00      | l1_pre_topc(X0_52) != iProver_top
% 1.79/1.00      | sP0_iProver_split != iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1278]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1275,plain,
% 1.79/1.00      ( ~ m1_pre_topc(X0_52,X1_52)
% 1.79/1.00      | m1_subset_1(u1_struct_0(X0_52),k1_zfmisc_1(u1_struct_0(X1_52)))
% 1.79/1.00      | ~ l1_pre_topc(X1_52) ),
% 1.79/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2077,plain,
% 1.79/1.00      ( ~ m1_pre_topc(sK3,sK1)
% 1.79/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.79/1.00      | ~ l1_pre_topc(sK1) ),
% 1.79/1.00      inference(instantiation,[status(thm)],[c_1275]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2078,plain,
% 1.79/1.00      ( m1_pre_topc(sK3,sK1) != iProver_top
% 1.79/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.79/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_2077]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1,plain,
% 1.79/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.79/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_3,plain,
% 1.79/1.00      ( v2_struct_0(X0)
% 1.79/1.00      | ~ l1_struct_0(X0)
% 1.79/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.79/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_405,plain,
% 1.79/1.00      ( v2_struct_0(X0)
% 1.79/1.00      | ~ l1_pre_topc(X0)
% 1.79/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.79/1.00      inference(resolution,[status(thm)],[c_1,c_3]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1257,plain,
% 1.79/1.00      ( v2_struct_0(X0_52)
% 1.79/1.00      | ~ l1_pre_topc(X0_52)
% 1.79/1.00      | ~ v1_xboole_0(u1_struct_0(X0_52)) ),
% 1.79/1.00      inference(subtyping,[status(esa)],[c_405]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2182,plain,
% 1.79/1.00      ( v2_struct_0(sK3)
% 1.79/1.00      | ~ l1_pre_topc(sK3)
% 1.79/1.00      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.79/1.00      inference(instantiation,[status(thm)],[c_1257]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2183,plain,
% 1.79/1.00      ( v2_struct_0(sK3) = iProver_top
% 1.79/1.00      | l1_pre_topc(sK3) != iProver_top
% 1.79/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_2182]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2,plain,
% 1.79/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.79/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1277,plain,
% 1.79/1.00      ( ~ m1_pre_topc(X0_52,X1_52)
% 1.79/1.00      | ~ l1_pre_topc(X1_52)
% 1.79/1.00      | l1_pre_topc(X0_52) ),
% 1.79/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1838,plain,
% 1.79/1.00      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 1.79/1.00      | l1_pre_topc(X1_52) != iProver_top
% 1.79/1.00      | l1_pre_topc(X0_52) = iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1277]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2251,plain,
% 1.79/1.00      ( l1_pre_topc(sK1) != iProver_top
% 1.79/1.00      | l1_pre_topc(sK3) = iProver_top ),
% 1.79/1.00      inference(superposition,[status(thm)],[c_1848,c_1838]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2507,plain,
% 1.79/1.00      ( l1_pre_topc(X0_52) != iProver_top
% 1.79/1.00      | v2_struct_0(X1_52) = iProver_top
% 1.79/1.00      | v2_struct_0(X0_52) = iProver_top
% 1.79/1.00      | v2_pre_topc(X0_52) != iProver_top
% 1.79/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_52)))) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 1.79/1.00      | m1_pre_topc(X1_52,sK1) != iProver_top
% 1.79/1.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_52)) != iProver_top
% 1.79/1.00      | r1_tmap_1(sK1,X0_52,sK2,X0_53) = iProver_top
% 1.79/1.00      | r1_tmap_1(X1_52,X0_52,k2_tmap_1(sK1,X0_52,sK2,X1_52),X0_53) != iProver_top
% 1.79/1.00      | u1_struct_0(X0_52) != u1_struct_0(sK0) ),
% 1.79/1.00      inference(global_propositional_subsumption,
% 1.79/1.00                [status(thm)],
% 1.79/1.00                [c_1860,c_37,c_41,c_43,c_1322,c_1323,c_2078,c_2183,
% 1.79/1.00                 c_2251]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2508,plain,
% 1.79/1.00      ( u1_struct_0(X0_52) != u1_struct_0(sK0)
% 1.79/1.00      | r1_tmap_1(X1_52,X0_52,k2_tmap_1(sK1,X0_52,sK2,X1_52),X0_53) != iProver_top
% 1.79/1.00      | r1_tmap_1(sK1,X0_52,sK2,X0_53) = iProver_top
% 1.79/1.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X1_52)) != iProver_top
% 1.79/1.00      | m1_pre_topc(X1_52,sK1) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(X1_52)) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 1.79/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0_52)))) != iProver_top
% 1.79/1.00      | v2_pre_topc(X0_52) != iProver_top
% 1.79/1.00      | v2_struct_0(X1_52) = iProver_top
% 1.79/1.00      | v2_struct_0(X0_52) = iProver_top
% 1.79/1.00      | l1_pre_topc(X0_52) != iProver_top ),
% 1.79/1.00      inference(renaming,[status(thm)],[c_2507]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2526,plain,
% 1.79/1.00      ( r1_tmap_1(X0_52,sK0,k2_tmap_1(sK1,sK0,sK2,X0_52),X0_53) != iProver_top
% 1.79/1.00      | r1_tmap_1(sK1,sK0,sK2,X0_53) = iProver_top
% 1.79/1.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
% 1.79/1.00      | m1_pre_topc(X0_52,sK1) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 1.79/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 1.79/1.00      | v2_pre_topc(sK0) != iProver_top
% 1.79/1.00      | v2_struct_0(X0_52) = iProver_top
% 1.79/1.00      | v2_struct_0(sK0) = iProver_top
% 1.79/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 1.79/1.00      inference(equality_resolution,[status(thm)],[c_2508]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2571,plain,
% 1.79/1.00      ( r1_tmap_1(X0_52,sK0,k2_tmap_1(sK1,sK0,sK2,X0_52),X0_53) != iProver_top
% 1.79/1.00      | r1_tmap_1(sK1,sK0,sK2,X0_53) = iProver_top
% 1.79/1.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
% 1.79/1.00      | m1_pre_topc(X0_52,sK1) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(X0_52)) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(sK1)) != iProver_top
% 1.79/1.00      | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top
% 1.79/1.00      | v2_struct_0(X0_52) = iProver_top ),
% 1.79/1.00      inference(global_propositional_subsumption,
% 1.79/1.00                [status(thm)],
% 1.79/1.00                [c_2526,c_32,c_33,c_34,c_40]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2585,plain,
% 1.79/1.00      ( r1_tmap_1(sK1,sK0,sK2,sK5) = iProver_top
% 1.79/1.00      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top
% 1.79/1.00      | m1_pre_topc(sK3,sK1) != iProver_top
% 1.79/1.00      | m1_subset_1(sK5,u1_struct_0(sK1)) != iProver_top
% 1.79/1.00      | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 1.79/1.00      | v2_struct_0(sK3) = iProver_top ),
% 1.79/1.00      inference(superposition,[status(thm)],[c_2450,c_2571]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_19,negated_conjecture,
% 1.79/1.00      ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
% 1.79/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1267,negated_conjecture,
% 1.79/1.00      ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
% 1.79/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1847,plain,
% 1.79/1.00      ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
% 1.79/1.00      inference(predicate_to_equality,[status(thm)],[c_1267]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_1881,plain,
% 1.79/1.00      ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 1.79/1.00      inference(light_normalisation,[status(thm)],[c_1847,c_1269]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2588,plain,
% 1.79/1.00      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK3)) != iProver_top ),
% 1.79/1.00      inference(global_propositional_subsumption,
% 1.79/1.00                [status(thm)],
% 1.79/1.00                [c_2585,c_32,c_33,c_34,c_35,c_36,c_37,c_40,c_41,c_43,
% 1.79/1.00                 c_45,c_1881,c_1919,c_2069,c_2191,c_2356]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_2972,plain,
% 1.79/1.00      ( m1_pre_topc(sK3,sK1) != iProver_top
% 1.79/1.00      | m1_pre_topc(sK3,sK3) != iProver_top ),
% 1.79/1.00      inference(superposition,[status(thm)],[c_2962,c_2588]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_3100,plain,
% 1.79/1.00      ( m1_pre_topc(sK3,sK3) != iProver_top ),
% 1.79/1.00      inference(global_propositional_subsumption,
% 1.79/1.00                [status(thm)],
% 1.79/1.00                [c_2972,c_43]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(c_3105,plain,
% 1.79/1.00      ( l1_pre_topc(sK3) != iProver_top ),
% 1.79/1.00      inference(superposition,[status(thm)],[c_1841,c_3100]) ).
% 1.79/1.00  
% 1.79/1.00  cnf(contradiction,plain,
% 1.79/1.00      ( $false ),
% 1.79/1.00      inference(minisat,[status(thm)],[c_3105,c_2251,c_37]) ).
% 1.79/1.00  
% 1.79/1.00  
% 1.79/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.79/1.00  
% 1.79/1.00  ------                               Statistics
% 1.79/1.00  
% 1.79/1.00  ------ General
% 1.79/1.00  
% 1.79/1.00  abstr_ref_over_cycles:                  0
% 1.79/1.00  abstr_ref_under_cycles:                 0
% 1.79/1.00  gc_basic_clause_elim:                   0
% 1.79/1.00  forced_gc_time:                         0
% 1.79/1.00  parsing_time:                           0.023
% 1.79/1.00  unif_index_cands_time:                  0.
% 1.79/1.00  unif_index_add_time:                    0.
% 1.79/1.00  orderings_time:                         0.
% 1.79/1.00  out_proof_time:                         0.013
% 1.79/1.00  total_time:                             0.148
% 1.79/1.00  num_of_symbols:                         58
% 1.79/1.00  num_of_terms:                           2305
% 1.79/1.00  
% 1.79/1.00  ------ Preprocessing
% 1.79/1.00  
% 1.79/1.00  num_of_splits:                          1
% 1.79/1.00  num_of_split_atoms:                     1
% 1.79/1.00  num_of_reused_defs:                     0
% 1.79/1.00  num_eq_ax_congr_red:                    15
% 1.79/1.00  num_of_sem_filtered_clauses:            1
% 1.79/1.00  num_of_subtypes:                        2
% 1.79/1.00  monotx_restored_types:                  0
% 1.79/1.00  sat_num_of_epr_types:                   0
% 1.79/1.00  sat_num_of_non_cyclic_types:            0
% 1.79/1.00  sat_guarded_non_collapsed_types:        0
% 1.79/1.00  num_pure_diseq_elim:                    0
% 1.79/1.00  simp_replaced_by:                       0
% 1.79/1.00  res_preprocessed:                       121
% 1.79/1.00  prep_upred:                             0
% 1.79/1.00  prep_unflattend:                        10
% 1.79/1.00  smt_new_axioms:                         0
% 1.79/1.00  pred_elim_cands:                        8
% 1.79/1.00  pred_elim:                              6
% 1.79/1.00  pred_elim_cl:                           8
% 1.79/1.00  pred_elim_cycles:                       13
% 1.79/1.00  merged_defs:                            8
% 1.79/1.00  merged_defs_ncl:                        0
% 1.79/1.00  bin_hyper_res:                          8
% 1.79/1.00  prep_cycles:                            4
% 1.79/1.00  pred_elim_time:                         0.023
% 1.79/1.00  splitting_time:                         0.
% 1.79/1.00  sem_filter_time:                        0.
% 1.79/1.00  monotx_time:                            0.
% 1.79/1.00  subtype_inf_time:                       0.
% 1.79/1.00  
% 1.79/1.00  ------ Problem properties
% 1.79/1.00  
% 1.79/1.00  clauses:                                24
% 1.79/1.00  conjectures:                            14
% 1.79/1.00  epr:                                    11
% 1.79/1.00  horn:                                   19
% 1.79/1.00  ground:                                 15
% 1.79/1.00  unary:                                  12
% 1.79/1.00  binary:                                 3
% 1.79/1.00  lits:                                   76
% 1.79/1.00  lits_eq:                                4
% 1.79/1.00  fd_pure:                                0
% 1.79/1.00  fd_pseudo:                              0
% 1.79/1.00  fd_cond:                                0
% 1.79/1.00  fd_pseudo_cond:                         0
% 1.79/1.00  ac_symbols:                             0
% 1.79/1.00  
% 1.79/1.00  ------ Propositional Solver
% 1.79/1.00  
% 1.79/1.00  prop_solver_calls:                      26
% 1.79/1.00  prop_fast_solver_calls:                 1230
% 1.79/1.00  smt_solver_calls:                       0
% 1.79/1.00  smt_fast_solver_calls:                  0
% 1.79/1.00  prop_num_of_clauses:                    633
% 1.79/1.00  prop_preprocess_simplified:             3511
% 1.79/1.00  prop_fo_subsumed:                       36
% 1.79/1.00  prop_solver_time:                       0.
% 1.79/1.00  smt_solver_time:                        0.
% 1.79/1.00  smt_fast_solver_time:                   0.
% 1.79/1.00  prop_fast_solver_time:                  0.
% 1.79/1.00  prop_unsat_core_time:                   0.
% 1.79/1.00  
% 1.79/1.00  ------ QBF
% 1.79/1.00  
% 1.79/1.00  qbf_q_res:                              0
% 1.79/1.00  qbf_num_tautologies:                    0
% 1.79/1.00  qbf_prep_cycles:                        0
% 1.79/1.00  
% 1.79/1.00  ------ BMC1
% 1.79/1.00  
% 1.79/1.00  bmc1_current_bound:                     -1
% 1.79/1.00  bmc1_last_solved_bound:                 -1
% 1.79/1.00  bmc1_unsat_core_size:                   -1
% 1.79/1.00  bmc1_unsat_core_parents_size:           -1
% 1.79/1.00  bmc1_merge_next_fun:                    0
% 1.79/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.79/1.00  
% 1.79/1.00  ------ Instantiation
% 1.79/1.00  
% 1.79/1.00  inst_num_of_clauses:                    204
% 1.79/1.00  inst_num_in_passive:                    4
% 1.79/1.00  inst_num_in_active:                     142
% 1.79/1.00  inst_num_in_unprocessed:                58
% 1.79/1.00  inst_num_of_loops:                      150
% 1.79/1.00  inst_num_of_learning_restarts:          0
% 1.79/1.00  inst_num_moves_active_passive:          6
% 1.79/1.00  inst_lit_activity:                      0
% 1.79/1.00  inst_lit_activity_moves:                0
% 1.79/1.00  inst_num_tautologies:                   0
% 1.79/1.00  inst_num_prop_implied:                  0
% 1.79/1.00  inst_num_existing_simplified:           0
% 1.79/1.00  inst_num_eq_res_simplified:             0
% 1.79/1.00  inst_num_child_elim:                    0
% 1.79/1.00  inst_num_of_dismatching_blockings:      40
% 1.79/1.00  inst_num_of_non_proper_insts:           196
% 1.79/1.00  inst_num_of_duplicates:                 0
% 1.79/1.00  inst_inst_num_from_inst_to_res:         0
% 1.79/1.00  inst_dismatching_checking_time:         0.
% 1.79/1.00  
% 1.79/1.00  ------ Resolution
% 1.79/1.00  
% 1.79/1.00  res_num_of_clauses:                     0
% 1.79/1.00  res_num_in_passive:                     0
% 1.79/1.00  res_num_in_active:                      0
% 1.79/1.00  res_num_of_loops:                       125
% 1.79/1.00  res_forward_subset_subsumed:            35
% 1.79/1.00  res_backward_subset_subsumed:           0
% 1.79/1.00  res_forward_subsumed:                   0
% 1.79/1.00  res_backward_subsumed:                  0
% 1.79/1.00  res_forward_subsumption_resolution:     1
% 1.79/1.00  res_backward_subsumption_resolution:    0
% 1.79/1.00  res_clause_to_clause_subsumption:       233
% 1.79/1.00  res_orphan_elimination:                 0
% 1.79/1.00  res_tautology_del:                      73
% 1.79/1.00  res_num_eq_res_simplified:              0
% 1.79/1.00  res_num_sel_changes:                    0
% 1.79/1.00  res_moves_from_active_to_pass:          0
% 1.79/1.00  
% 1.79/1.00  ------ Superposition
% 1.79/1.00  
% 1.79/1.00  sup_time_total:                         0.
% 1.79/1.00  sup_time_generating:                    0.
% 1.79/1.00  sup_time_sim_full:                      0.
% 1.79/1.00  sup_time_sim_immed:                     0.
% 1.79/1.00  
% 1.79/1.00  sup_num_of_clauses:                     37
% 1.79/1.00  sup_num_in_active:                      30
% 1.79/1.00  sup_num_in_passive:                     7
% 1.79/1.00  sup_num_of_loops:                       29
% 1.79/1.00  sup_fw_superposition:                   7
% 1.79/1.00  sup_bw_superposition:                   5
% 1.79/1.00  sup_immediate_simplified:               0
% 1.79/1.00  sup_given_eliminated:                   0
% 1.79/1.00  comparisons_done:                       0
% 1.79/1.00  comparisons_avoided:                    0
% 1.79/1.00  
% 1.79/1.00  ------ Simplifications
% 1.79/1.00  
% 1.79/1.00  
% 1.79/1.00  sim_fw_subset_subsumed:                 0
% 1.79/1.00  sim_bw_subset_subsumed:                 0
% 1.79/1.00  sim_fw_subsumed:                        0
% 1.79/1.00  sim_bw_subsumed:                        0
% 1.79/1.00  sim_fw_subsumption_res:                 0
% 1.79/1.00  sim_bw_subsumption_res:                 0
% 1.79/1.00  sim_tautology_del:                      1
% 1.79/1.00  sim_eq_tautology_del:                   0
% 1.79/1.00  sim_eq_res_simp:                        0
% 1.79/1.00  sim_fw_demodulated:                     0
% 1.79/1.00  sim_bw_demodulated:                     0
% 1.79/1.00  sim_light_normalised:                   3
% 1.79/1.00  sim_joinable_taut:                      0
% 1.79/1.00  sim_joinable_simp:                      0
% 1.79/1.00  sim_ac_normalised:                      0
% 1.79/1.00  sim_smt_subsumption:                    0
% 1.79/1.00  
%------------------------------------------------------------------------------
