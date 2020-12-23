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
% DateTime   : Thu Dec  3 12:22:46 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 863 expanded)
%              Number of clauses        :  119 ( 153 expanded)
%              Number of leaves         :   23 ( 339 expanded)
%              Depth                    :   26
%              Number of atoms          : 1478 (13518 expanded)
%              Number of equality atoms :  125 ( 969 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    4 (   1 average)

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
    inference(negated_conjecture,[],[f13])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f44,f50,f49,f48,f47,f46,f45])).

fof(f82,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,(
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
    inference(equality_resolution,[],[f70])).

fof(f78,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

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
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f72,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f71,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f73,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_connsp_2(X3,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X3) )
     => ( r1_tarski(sK0(X0,X1,X2),X2)
        & v3_pre_topc(sK0(X0,X1,X2),X0)
        & m1_connsp_2(sK0(X0,X1,X2),X0,X1)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK0(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(sK0(X0,X1,X2),X2)
                & v3_pre_topc(sK0(X0,X1,X2),X0)
                & m1_connsp_2(sK0(X0,X1,X2),X0,X1)
                & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(sK0(X0,X1,X2)) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f38])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK0(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK0(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5)
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
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X6)
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
    inference(equality_resolution,[],[f69])).

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
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,(
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
    inference(equality_resolution,[],[f68])).

fof(f86,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | r1_tmap_1(sK2,sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f81,plain,(
    v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ r1_tmap_1(sK2,sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_17,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
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
    inference(cnf_transformation,[],[f92])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_792,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
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
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_793,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_792])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_797,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_793,c_29])).

cnf(c_798,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_797])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_5,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_839,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_798,c_4,c_5])).

cnf(c_1016,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_839])).

cnf(c_1017,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1016])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1021,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1017,c_32,c_31,c_30,c_26])).

cnf(c_1022,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1021])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1250,plain,
    ( r1_tmap_1(sK2,X0,sK3,X1)
    | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_connsp_2(X2,sK2,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1022,c_34])).

cnf(c_1251,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_connsp_2(X1,sK2,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1250])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1255,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | ~ m1_connsp_2(X1,sK2,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | r1_tmap_1(sK2,sK1,sK3,X0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1251,c_35,c_33,c_27])).

cnf(c_1256,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_connsp_2(X1,sK2,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1255])).

cnf(c_2214,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_connsp_2(X1,sK2,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1256])).

cnf(c_2854,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0_55)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_55)
    | ~ m1_connsp_2(X1_55,sK2,X0_55)
    | ~ r1_tarski(X1_55,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_2214])).

cnf(c_4478,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0_55)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_55)
    | ~ m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,X0_55)
    | ~ r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2854])).

cnf(c_4942,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
    | ~ m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,sK5)
    | ~ r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_4478])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2883,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | r2_hidden(X0_55,X1_55)
    | v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_4329,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2883])).

cnf(c_7,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_240,plain,
    ( r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_5])).

cnf(c_241,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_240])).

cnf(c_1280,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_241,c_31])).

cnf(c_1281,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | r1_tarski(sK0(sK2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1280])).

cnf(c_1285,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | r1_tarski(sK0(sK2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1281,c_32,c_30])).

cnf(c_2871,plain,
    ( ~ m1_connsp_2(X0_55,sK2,X1_55)
    | r1_tarski(sK0(sK2,X1_55,X0_55),X0_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1285])).

cnf(c_3968,plain,
    ( ~ m1_connsp_2(X0_55,sK2,sK5)
    | r1_tarski(sK0(sK2,sK5,X0_55),X0_55)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2871])).

cnf(c_4300,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK5)
    | r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3968])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_226,plain,
    ( m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_5])).

cnf(c_227,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_226])).

cnf(c_1322,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_227,c_31])).

cnf(c_1323,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | m1_connsp_2(sK0(sK2,X1,X0),sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1322])).

cnf(c_1327,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | m1_connsp_2(sK0(sK2,X1,X0),sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1323,c_32,c_30])).

cnf(c_2869,plain,
    ( ~ m1_connsp_2(X0_55,sK2,X1_55)
    | m1_connsp_2(sK0(sK2,X1_55,X0_55),sK2,X1_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1327])).

cnf(c_3963,plain,
    ( ~ m1_connsp_2(X0_55,sK2,sK5)
    | m1_connsp_2(sK0(sK2,sK5,X0_55),sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2869])).

cnf(c_4301,plain,
    ( m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,sK5)
    | ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3963])).

cnf(c_6,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1385,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_31])).

cnf(c_1386,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1385])).

cnf(c_1390,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1386,c_32,c_30])).

cnf(c_2866,plain,
    ( m1_connsp_2(X0_55,sK2,X1_55)
    | ~ v3_pre_topc(X0_55,sK2)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_55,u1_struct_0(sK2))
    | ~ r2_hidden(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_1390])).

cnf(c_3981,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK2,X0_55)
    | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0_55,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2866])).

cnf(c_4244,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK2,sK5)
    | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3981])).

cnf(c_2889,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_4187,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK4) = k2_tmap_1(sK2,sK1,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2889])).

cnf(c_2898,plain,
    ( ~ r1_tmap_1(X0_54,X1_54,X0_55,X1_55)
    | r1_tmap_1(X0_54,X1_54,X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55 ),
    theory(equality)).

cnf(c_4032,plain,
    ( r1_tmap_1(sK4,sK1,X0_55,X1_55)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | X0_55 != k2_tmap_1(sK2,sK1,sK3,sK4)
    | X1_55 != sK6 ),
    inference(instantiation,[status(thm)],[c_2898])).

cnf(c_4143,plain,
    ( r1_tmap_1(sK4,sK1,X0_55,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | X0_55 != k2_tmap_1(sK2,sK1,sK3,sK4)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_4032])).

cnf(c_4186,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | k2_tmap_1(sK2,sK1,sK3,sK4) != k2_tmap_1(sK2,sK1,sK3,sK4)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_4143])).

cnf(c_4182,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2889])).

cnf(c_2892,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | m1_subset_1(X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55 ),
    theory(equality)).

cnf(c_4008,plain,
    ( m1_subset_1(X0_55,X1_55)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | X1_55 != u1_struct_0(sK4)
    | X0_55 != sK6 ),
    inference(instantiation,[status(thm)],[c_2892])).

cnf(c_4109,plain,
    ( m1_subset_1(sK5,X0_55)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | X0_55 != u1_struct_0(sK4)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_4008])).

cnf(c_4181,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_4109])).

cnf(c_18,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
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
    inference(cnf_transformation,[],[f93])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f91])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
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
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_16])).

cnf(c_191,plain,
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
    inference(renaming,[status(thm)],[c_190])).

cnf(c_735,plain,
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
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_191,c_28])).

cnf(c_736,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_735])).

cnf(c_740,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_736,c_29])).

cnf(c_741,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_740])).

cnf(c_776,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_741,c_4])).

cnf(c_1061,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_776])).

cnf(c_1062,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1061])).

cnf(c_1066,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1062,c_32,c_31,c_30,c_26])).

cnf(c_1067,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1066])).

cnf(c_1226,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1067,c_34])).

cnf(c_1227,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1226])).

cnf(c_1231,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1227,c_35,c_33,c_27])).

cnf(c_1232,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1231])).

cnf(c_2218,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_1232])).

cnf(c_2853,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0_55)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_2218])).

cnf(c_3986,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2853])).

cnf(c_20,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,sK3,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2881,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,sK3,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_3654,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2881])).

cnf(c_21,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2880,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_3713,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3654,c_2880])).

cnf(c_3870,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3713])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_484,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1005,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_24])).

cnf(c_1006,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1005])).

cnf(c_1008,plain,
    ( l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1006,c_30])).

cnf(c_1694,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_484,c_1008])).

cnf(c_1695,plain,
    ( v2_struct_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1694])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_976,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_977,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_976])).

cnf(c_14,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_198,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_15])).

cnf(c_199,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_198])).

cnf(c_25,negated_conjecture,
    ( v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_601,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_199,c_25])).

cnf(c_602,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4942,c_4329,c_4300,c_4301,c_4244,c_4187,c_4186,c_4182,c_4181,c_3986,c_3870,c_2880,c_1695,c_977,c_602,c_19,c_22,c_23,c_24,c_26,c_30,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:03:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.82/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.00  
% 1.82/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.82/1.00  
% 1.82/1.00  ------  iProver source info
% 1.82/1.00  
% 1.82/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.82/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.82/1.00  git: non_committed_changes: false
% 1.82/1.00  git: last_make_outside_of_git: false
% 1.82/1.00  
% 1.82/1.00  ------ 
% 1.82/1.00  
% 1.82/1.00  ------ Input Options
% 1.82/1.00  
% 1.82/1.00  --out_options                           all
% 1.82/1.00  --tptp_safe_out                         true
% 1.82/1.00  --problem_path                          ""
% 1.82/1.00  --include_path                          ""
% 1.82/1.00  --clausifier                            res/vclausify_rel
% 1.82/1.00  --clausifier_options                    --mode clausify
% 1.82/1.00  --stdin                                 false
% 1.82/1.00  --stats_out                             all
% 1.82/1.00  
% 1.82/1.00  ------ General Options
% 1.82/1.00  
% 1.82/1.00  --fof                                   false
% 1.82/1.00  --time_out_real                         305.
% 1.82/1.00  --time_out_virtual                      -1.
% 1.82/1.00  --symbol_type_check                     false
% 1.82/1.00  --clausify_out                          false
% 1.82/1.00  --sig_cnt_out                           false
% 1.82/1.00  --trig_cnt_out                          false
% 1.82/1.00  --trig_cnt_out_tolerance                1.
% 1.82/1.00  --trig_cnt_out_sk_spl                   false
% 1.82/1.00  --abstr_cl_out                          false
% 1.82/1.00  
% 1.82/1.00  ------ Global Options
% 1.82/1.00  
% 1.82/1.00  --schedule                              default
% 1.82/1.00  --add_important_lit                     false
% 1.82/1.00  --prop_solver_per_cl                    1000
% 1.82/1.00  --min_unsat_core                        false
% 1.82/1.00  --soft_assumptions                      false
% 1.82/1.00  --soft_lemma_size                       3
% 1.82/1.00  --prop_impl_unit_size                   0
% 1.82/1.00  --prop_impl_unit                        []
% 1.82/1.00  --share_sel_clauses                     true
% 1.82/1.00  --reset_solvers                         false
% 1.82/1.00  --bc_imp_inh                            [conj_cone]
% 1.82/1.00  --conj_cone_tolerance                   3.
% 1.82/1.00  --extra_neg_conj                        none
% 1.82/1.00  --large_theory_mode                     true
% 1.82/1.00  --prolific_symb_bound                   200
% 1.82/1.00  --lt_threshold                          2000
% 1.82/1.00  --clause_weak_htbl                      true
% 1.82/1.00  --gc_record_bc_elim                     false
% 1.82/1.00  
% 1.82/1.00  ------ Preprocessing Options
% 1.82/1.00  
% 1.82/1.00  --preprocessing_flag                    true
% 1.82/1.00  --time_out_prep_mult                    0.1
% 1.82/1.00  --splitting_mode                        input
% 1.82/1.00  --splitting_grd                         true
% 1.82/1.00  --splitting_cvd                         false
% 1.82/1.00  --splitting_cvd_svl                     false
% 1.82/1.00  --splitting_nvd                         32
% 1.82/1.00  --sub_typing                            true
% 1.82/1.00  --prep_gs_sim                           true
% 1.82/1.00  --prep_unflatten                        true
% 1.82/1.00  --prep_res_sim                          true
% 1.82/1.00  --prep_upred                            true
% 1.82/1.00  --prep_sem_filter                       exhaustive
% 1.82/1.00  --prep_sem_filter_out                   false
% 1.82/1.00  --pred_elim                             true
% 1.82/1.00  --res_sim_input                         true
% 1.82/1.00  --eq_ax_congr_red                       true
% 1.82/1.00  --pure_diseq_elim                       true
% 1.82/1.00  --brand_transform                       false
% 1.82/1.00  --non_eq_to_eq                          false
% 1.82/1.00  --prep_def_merge                        true
% 1.82/1.00  --prep_def_merge_prop_impl              false
% 1.82/1.00  --prep_def_merge_mbd                    true
% 1.82/1.00  --prep_def_merge_tr_red                 false
% 1.82/1.00  --prep_def_merge_tr_cl                  false
% 1.82/1.00  --smt_preprocessing                     true
% 1.82/1.00  --smt_ac_axioms                         fast
% 1.82/1.00  --preprocessed_out                      false
% 1.82/1.00  --preprocessed_stats                    false
% 1.82/1.00  
% 1.82/1.00  ------ Abstraction refinement Options
% 1.82/1.00  
% 1.82/1.00  --abstr_ref                             []
% 1.82/1.00  --abstr_ref_prep                        false
% 1.82/1.00  --abstr_ref_until_sat                   false
% 1.82/1.00  --abstr_ref_sig_restrict                funpre
% 1.82/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.82/1.00  --abstr_ref_under                       []
% 1.82/1.00  
% 1.82/1.00  ------ SAT Options
% 1.82/1.00  
% 1.82/1.00  --sat_mode                              false
% 1.82/1.00  --sat_fm_restart_options                ""
% 1.82/1.00  --sat_gr_def                            false
% 1.82/1.00  --sat_epr_types                         true
% 1.82/1.00  --sat_non_cyclic_types                  false
% 1.82/1.00  --sat_finite_models                     false
% 1.82/1.00  --sat_fm_lemmas                         false
% 1.82/1.00  --sat_fm_prep                           false
% 1.82/1.00  --sat_fm_uc_incr                        true
% 1.82/1.00  --sat_out_model                         small
% 1.82/1.00  --sat_out_clauses                       false
% 1.82/1.00  
% 1.82/1.00  ------ QBF Options
% 1.82/1.00  
% 1.82/1.00  --qbf_mode                              false
% 1.82/1.00  --qbf_elim_univ                         false
% 1.82/1.00  --qbf_dom_inst                          none
% 1.82/1.00  --qbf_dom_pre_inst                      false
% 1.82/1.00  --qbf_sk_in                             false
% 1.82/1.00  --qbf_pred_elim                         true
% 1.82/1.00  --qbf_split                             512
% 1.82/1.00  
% 1.82/1.00  ------ BMC1 Options
% 1.82/1.00  
% 1.82/1.00  --bmc1_incremental                      false
% 1.82/1.00  --bmc1_axioms                           reachable_all
% 1.82/1.00  --bmc1_min_bound                        0
% 1.82/1.00  --bmc1_max_bound                        -1
% 1.82/1.00  --bmc1_max_bound_default                -1
% 1.82/1.00  --bmc1_symbol_reachability              true
% 1.82/1.00  --bmc1_property_lemmas                  false
% 1.82/1.00  --bmc1_k_induction                      false
% 1.82/1.00  --bmc1_non_equiv_states                 false
% 1.82/1.00  --bmc1_deadlock                         false
% 1.82/1.00  --bmc1_ucm                              false
% 1.82/1.00  --bmc1_add_unsat_core                   none
% 1.82/1.00  --bmc1_unsat_core_children              false
% 1.82/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.82/1.00  --bmc1_out_stat                         full
% 1.82/1.00  --bmc1_ground_init                      false
% 1.82/1.00  --bmc1_pre_inst_next_state              false
% 1.82/1.00  --bmc1_pre_inst_state                   false
% 1.82/1.00  --bmc1_pre_inst_reach_state             false
% 1.82/1.00  --bmc1_out_unsat_core                   false
% 1.82/1.00  --bmc1_aig_witness_out                  false
% 1.82/1.00  --bmc1_verbose                          false
% 1.82/1.00  --bmc1_dump_clauses_tptp                false
% 1.82/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.82/1.00  --bmc1_dump_file                        -
% 1.82/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.82/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.82/1.00  --bmc1_ucm_extend_mode                  1
% 1.82/1.00  --bmc1_ucm_init_mode                    2
% 1.82/1.00  --bmc1_ucm_cone_mode                    none
% 1.82/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.82/1.00  --bmc1_ucm_relax_model                  4
% 1.82/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.82/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.82/1.00  --bmc1_ucm_layered_model                none
% 1.82/1.00  --bmc1_ucm_max_lemma_size               10
% 1.82/1.00  
% 1.82/1.00  ------ AIG Options
% 1.82/1.00  
% 1.82/1.00  --aig_mode                              false
% 1.82/1.00  
% 1.82/1.00  ------ Instantiation Options
% 1.82/1.00  
% 1.82/1.00  --instantiation_flag                    true
% 1.82/1.00  --inst_sos_flag                         false
% 1.82/1.00  --inst_sos_phase                        true
% 1.82/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.82/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.82/1.00  --inst_lit_sel_side                     num_symb
% 1.82/1.00  --inst_solver_per_active                1400
% 1.82/1.00  --inst_solver_calls_frac                1.
% 1.82/1.00  --inst_passive_queue_type               priority_queues
% 1.82/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.82/1.00  --inst_passive_queues_freq              [25;2]
% 1.82/1.00  --inst_dismatching                      true
% 1.82/1.00  --inst_eager_unprocessed_to_passive     true
% 1.82/1.00  --inst_prop_sim_given                   true
% 1.82/1.00  --inst_prop_sim_new                     false
% 1.82/1.00  --inst_subs_new                         false
% 1.82/1.00  --inst_eq_res_simp                      false
% 1.82/1.00  --inst_subs_given                       false
% 1.82/1.00  --inst_orphan_elimination               true
% 1.82/1.00  --inst_learning_loop_flag               true
% 1.82/1.00  --inst_learning_start                   3000
% 1.82/1.00  --inst_learning_factor                  2
% 1.82/1.00  --inst_start_prop_sim_after_learn       3
% 1.82/1.00  --inst_sel_renew                        solver
% 1.82/1.00  --inst_lit_activity_flag                true
% 1.82/1.00  --inst_restr_to_given                   false
% 1.82/1.00  --inst_activity_threshold               500
% 1.82/1.00  --inst_out_proof                        true
% 1.82/1.00  
% 1.82/1.00  ------ Resolution Options
% 1.82/1.00  
% 1.82/1.00  --resolution_flag                       true
% 1.82/1.00  --res_lit_sel                           adaptive
% 1.82/1.00  --res_lit_sel_side                      none
% 1.82/1.00  --res_ordering                          kbo
% 1.82/1.00  --res_to_prop_solver                    active
% 1.82/1.00  --res_prop_simpl_new                    false
% 1.82/1.00  --res_prop_simpl_given                  true
% 1.82/1.00  --res_passive_queue_type                priority_queues
% 1.82/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.82/1.00  --res_passive_queues_freq               [15;5]
% 1.82/1.00  --res_forward_subs                      full
% 1.82/1.00  --res_backward_subs                     full
% 1.82/1.00  --res_forward_subs_resolution           true
% 1.82/1.00  --res_backward_subs_resolution          true
% 1.82/1.00  --res_orphan_elimination                true
% 1.82/1.00  --res_time_limit                        2.
% 1.82/1.00  --res_out_proof                         true
% 1.82/1.00  
% 1.82/1.00  ------ Superposition Options
% 1.82/1.00  
% 1.82/1.00  --superposition_flag                    true
% 1.82/1.00  --sup_passive_queue_type                priority_queues
% 1.82/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.82/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.82/1.00  --demod_completeness_check              fast
% 1.82/1.00  --demod_use_ground                      true
% 1.82/1.00  --sup_to_prop_solver                    passive
% 1.82/1.00  --sup_prop_simpl_new                    true
% 1.82/1.00  --sup_prop_simpl_given                  true
% 1.82/1.00  --sup_fun_splitting                     false
% 1.82/1.00  --sup_smt_interval                      50000
% 1.82/1.00  
% 1.82/1.00  ------ Superposition Simplification Setup
% 1.82/1.00  
% 1.82/1.00  --sup_indices_passive                   []
% 1.82/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.82/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/1.00  --sup_full_bw                           [BwDemod]
% 1.82/1.00  --sup_immed_triv                        [TrivRules]
% 1.82/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.82/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/1.00  --sup_immed_bw_main                     []
% 1.82/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.82/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/1.00  
% 1.82/1.00  ------ Combination Options
% 1.82/1.00  
% 1.82/1.00  --comb_res_mult                         3
% 1.82/1.00  --comb_sup_mult                         2
% 1.82/1.00  --comb_inst_mult                        10
% 1.82/1.00  
% 1.82/1.00  ------ Debug Options
% 1.82/1.00  
% 1.82/1.00  --dbg_backtrace                         false
% 1.82/1.00  --dbg_dump_prop_clauses                 false
% 1.82/1.00  --dbg_dump_prop_clauses_file            -
% 1.82/1.00  --dbg_out_stat                          false
% 1.82/1.00  ------ Parsing...
% 1.82/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.82/1.00  
% 1.82/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.82/1.00  
% 1.82/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.82/1.00  
% 1.82/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.82/1.00  ------ Proving...
% 1.82/1.00  ------ Problem Properties 
% 1.82/1.00  
% 1.82/1.00  
% 1.82/1.00  clauses                                 33
% 1.82/1.00  conjectures                             6
% 1.82/1.00  EPR                                     2
% 1.82/1.00  Horn                                    31
% 1.82/1.00  unary                                   9
% 1.82/1.00  binary                                  3
% 1.82/1.00  lits                                    88
% 1.82/1.00  lits eq                                 3
% 1.82/1.00  fd_pure                                 0
% 1.82/1.00  fd_pseudo                               0
% 1.82/1.00  fd_cond                                 0
% 1.82/1.00  fd_pseudo_cond                          0
% 1.82/1.00  AC symbols                              0
% 1.82/1.00  
% 1.82/1.00  ------ Schedule dynamic 5 is on 
% 1.82/1.00  
% 1.82/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.82/1.00  
% 1.82/1.00  
% 1.82/1.00  ------ 
% 1.82/1.00  Current options:
% 1.82/1.00  ------ 
% 1.82/1.00  
% 1.82/1.00  ------ Input Options
% 1.82/1.00  
% 1.82/1.00  --out_options                           all
% 1.82/1.00  --tptp_safe_out                         true
% 1.82/1.00  --problem_path                          ""
% 1.82/1.00  --include_path                          ""
% 1.82/1.00  --clausifier                            res/vclausify_rel
% 1.82/1.00  --clausifier_options                    --mode clausify
% 1.82/1.00  --stdin                                 false
% 1.82/1.00  --stats_out                             all
% 1.82/1.00  
% 1.82/1.00  ------ General Options
% 1.82/1.00  
% 1.82/1.00  --fof                                   false
% 1.82/1.00  --time_out_real                         305.
% 1.82/1.00  --time_out_virtual                      -1.
% 1.82/1.00  --symbol_type_check                     false
% 1.82/1.00  --clausify_out                          false
% 1.82/1.00  --sig_cnt_out                           false
% 1.82/1.00  --trig_cnt_out                          false
% 1.82/1.00  --trig_cnt_out_tolerance                1.
% 1.82/1.00  --trig_cnt_out_sk_spl                   false
% 1.82/1.00  --abstr_cl_out                          false
% 1.82/1.00  
% 1.82/1.00  ------ Global Options
% 1.82/1.00  
% 1.82/1.00  --schedule                              default
% 1.82/1.00  --add_important_lit                     false
% 1.82/1.00  --prop_solver_per_cl                    1000
% 1.82/1.00  --min_unsat_core                        false
% 1.82/1.00  --soft_assumptions                      false
% 1.82/1.00  --soft_lemma_size                       3
% 1.82/1.00  --prop_impl_unit_size                   0
% 1.82/1.00  --prop_impl_unit                        []
% 1.82/1.00  --share_sel_clauses                     true
% 1.82/1.00  --reset_solvers                         false
% 1.82/1.00  --bc_imp_inh                            [conj_cone]
% 1.82/1.00  --conj_cone_tolerance                   3.
% 1.82/1.00  --extra_neg_conj                        none
% 1.82/1.00  --large_theory_mode                     true
% 1.82/1.00  --prolific_symb_bound                   200
% 1.82/1.00  --lt_threshold                          2000
% 1.82/1.00  --clause_weak_htbl                      true
% 1.82/1.00  --gc_record_bc_elim                     false
% 1.82/1.00  
% 1.82/1.00  ------ Preprocessing Options
% 1.82/1.00  
% 1.82/1.00  --preprocessing_flag                    true
% 1.82/1.00  --time_out_prep_mult                    0.1
% 1.82/1.00  --splitting_mode                        input
% 1.82/1.00  --splitting_grd                         true
% 1.82/1.00  --splitting_cvd                         false
% 1.82/1.00  --splitting_cvd_svl                     false
% 1.82/1.00  --splitting_nvd                         32
% 1.82/1.00  --sub_typing                            true
% 1.82/1.00  --prep_gs_sim                           true
% 1.82/1.00  --prep_unflatten                        true
% 1.82/1.00  --prep_res_sim                          true
% 1.82/1.00  --prep_upred                            true
% 1.82/1.00  --prep_sem_filter                       exhaustive
% 1.82/1.00  --prep_sem_filter_out                   false
% 1.82/1.00  --pred_elim                             true
% 1.82/1.00  --res_sim_input                         true
% 1.82/1.00  --eq_ax_congr_red                       true
% 1.82/1.00  --pure_diseq_elim                       true
% 1.82/1.00  --brand_transform                       false
% 1.82/1.00  --non_eq_to_eq                          false
% 1.82/1.00  --prep_def_merge                        true
% 1.82/1.00  --prep_def_merge_prop_impl              false
% 1.82/1.00  --prep_def_merge_mbd                    true
% 1.82/1.00  --prep_def_merge_tr_red                 false
% 1.82/1.00  --prep_def_merge_tr_cl                  false
% 1.82/1.00  --smt_preprocessing                     true
% 1.82/1.00  --smt_ac_axioms                         fast
% 1.82/1.00  --preprocessed_out                      false
% 1.82/1.00  --preprocessed_stats                    false
% 1.82/1.00  
% 1.82/1.00  ------ Abstraction refinement Options
% 1.82/1.00  
% 1.82/1.00  --abstr_ref                             []
% 1.82/1.00  --abstr_ref_prep                        false
% 1.82/1.00  --abstr_ref_until_sat                   false
% 1.82/1.00  --abstr_ref_sig_restrict                funpre
% 1.82/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.82/1.00  --abstr_ref_under                       []
% 1.82/1.00  
% 1.82/1.00  ------ SAT Options
% 1.82/1.00  
% 1.82/1.00  --sat_mode                              false
% 1.82/1.00  --sat_fm_restart_options                ""
% 1.82/1.00  --sat_gr_def                            false
% 1.82/1.00  --sat_epr_types                         true
% 1.82/1.00  --sat_non_cyclic_types                  false
% 1.82/1.00  --sat_finite_models                     false
% 1.82/1.00  --sat_fm_lemmas                         false
% 1.82/1.00  --sat_fm_prep                           false
% 1.82/1.00  --sat_fm_uc_incr                        true
% 1.82/1.00  --sat_out_model                         small
% 1.82/1.00  --sat_out_clauses                       false
% 1.82/1.00  
% 1.82/1.00  ------ QBF Options
% 1.82/1.00  
% 1.82/1.00  --qbf_mode                              false
% 1.82/1.00  --qbf_elim_univ                         false
% 1.82/1.00  --qbf_dom_inst                          none
% 1.82/1.00  --qbf_dom_pre_inst                      false
% 1.82/1.00  --qbf_sk_in                             false
% 1.82/1.00  --qbf_pred_elim                         true
% 1.82/1.00  --qbf_split                             512
% 1.82/1.00  
% 1.82/1.00  ------ BMC1 Options
% 1.82/1.00  
% 1.82/1.00  --bmc1_incremental                      false
% 1.82/1.00  --bmc1_axioms                           reachable_all
% 1.82/1.00  --bmc1_min_bound                        0
% 1.82/1.00  --bmc1_max_bound                        -1
% 1.82/1.00  --bmc1_max_bound_default                -1
% 1.82/1.00  --bmc1_symbol_reachability              true
% 1.82/1.00  --bmc1_property_lemmas                  false
% 1.82/1.00  --bmc1_k_induction                      false
% 1.82/1.00  --bmc1_non_equiv_states                 false
% 1.82/1.00  --bmc1_deadlock                         false
% 1.82/1.00  --bmc1_ucm                              false
% 1.82/1.00  --bmc1_add_unsat_core                   none
% 1.82/1.00  --bmc1_unsat_core_children              false
% 1.82/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.82/1.00  --bmc1_out_stat                         full
% 1.82/1.00  --bmc1_ground_init                      false
% 1.82/1.00  --bmc1_pre_inst_next_state              false
% 1.82/1.00  --bmc1_pre_inst_state                   false
% 1.82/1.00  --bmc1_pre_inst_reach_state             false
% 1.82/1.00  --bmc1_out_unsat_core                   false
% 1.82/1.00  --bmc1_aig_witness_out                  false
% 1.82/1.00  --bmc1_verbose                          false
% 1.82/1.00  --bmc1_dump_clauses_tptp                false
% 1.82/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.82/1.00  --bmc1_dump_file                        -
% 1.82/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.82/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.82/1.00  --bmc1_ucm_extend_mode                  1
% 1.82/1.00  --bmc1_ucm_init_mode                    2
% 1.82/1.00  --bmc1_ucm_cone_mode                    none
% 1.82/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.82/1.00  --bmc1_ucm_relax_model                  4
% 1.82/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.82/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.82/1.00  --bmc1_ucm_layered_model                none
% 1.82/1.00  --bmc1_ucm_max_lemma_size               10
% 1.82/1.00  
% 1.82/1.00  ------ AIG Options
% 1.82/1.00  
% 1.82/1.00  --aig_mode                              false
% 1.82/1.00  
% 1.82/1.00  ------ Instantiation Options
% 1.82/1.00  
% 1.82/1.00  --instantiation_flag                    true
% 1.82/1.00  --inst_sos_flag                         false
% 1.82/1.00  --inst_sos_phase                        true
% 1.82/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.82/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.82/1.00  --inst_lit_sel_side                     none
% 1.82/1.00  --inst_solver_per_active                1400
% 1.82/1.00  --inst_solver_calls_frac                1.
% 1.82/1.00  --inst_passive_queue_type               priority_queues
% 1.82/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.82/1.00  --inst_passive_queues_freq              [25;2]
% 1.82/1.00  --inst_dismatching                      true
% 1.82/1.00  --inst_eager_unprocessed_to_passive     true
% 1.82/1.00  --inst_prop_sim_given                   true
% 1.82/1.00  --inst_prop_sim_new                     false
% 1.82/1.00  --inst_subs_new                         false
% 1.82/1.00  --inst_eq_res_simp                      false
% 1.82/1.00  --inst_subs_given                       false
% 1.82/1.00  --inst_orphan_elimination               true
% 1.82/1.00  --inst_learning_loop_flag               true
% 1.82/1.00  --inst_learning_start                   3000
% 1.82/1.00  --inst_learning_factor                  2
% 1.82/1.00  --inst_start_prop_sim_after_learn       3
% 1.82/1.00  --inst_sel_renew                        solver
% 1.82/1.00  --inst_lit_activity_flag                true
% 1.82/1.00  --inst_restr_to_given                   false
% 1.82/1.00  --inst_activity_threshold               500
% 1.82/1.00  --inst_out_proof                        true
% 1.82/1.00  
% 1.82/1.00  ------ Resolution Options
% 1.82/1.00  
% 1.82/1.00  --resolution_flag                       false
% 1.82/1.00  --res_lit_sel                           adaptive
% 1.82/1.00  --res_lit_sel_side                      none
% 1.82/1.00  --res_ordering                          kbo
% 1.82/1.00  --res_to_prop_solver                    active
% 1.82/1.00  --res_prop_simpl_new                    false
% 1.82/1.00  --res_prop_simpl_given                  true
% 1.82/1.00  --res_passive_queue_type                priority_queues
% 1.82/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.82/1.00  --res_passive_queues_freq               [15;5]
% 1.82/1.00  --res_forward_subs                      full
% 1.82/1.00  --res_backward_subs                     full
% 1.82/1.00  --res_forward_subs_resolution           true
% 1.82/1.00  --res_backward_subs_resolution          true
% 1.82/1.00  --res_orphan_elimination                true
% 1.82/1.00  --res_time_limit                        2.
% 1.82/1.00  --res_out_proof                         true
% 1.82/1.00  
% 1.82/1.00  ------ Superposition Options
% 1.82/1.00  
% 1.82/1.00  --superposition_flag                    true
% 1.82/1.00  --sup_passive_queue_type                priority_queues
% 1.82/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.82/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.82/1.00  --demod_completeness_check              fast
% 1.82/1.00  --demod_use_ground                      true
% 1.82/1.00  --sup_to_prop_solver                    passive
% 1.82/1.00  --sup_prop_simpl_new                    true
% 1.82/1.00  --sup_prop_simpl_given                  true
% 1.82/1.00  --sup_fun_splitting                     false
% 1.82/1.00  --sup_smt_interval                      50000
% 1.82/1.00  
% 1.82/1.00  ------ Superposition Simplification Setup
% 1.82/1.00  
% 1.82/1.00  --sup_indices_passive                   []
% 1.82/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.82/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.82/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/1.00  --sup_full_bw                           [BwDemod]
% 1.82/1.00  --sup_immed_triv                        [TrivRules]
% 1.82/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.82/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/1.00  --sup_immed_bw_main                     []
% 1.82/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.82/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.82/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.82/1.00  
% 1.82/1.00  ------ Combination Options
% 1.82/1.00  
% 1.82/1.00  --comb_res_mult                         3
% 1.82/1.00  --comb_sup_mult                         2
% 1.82/1.00  --comb_inst_mult                        10
% 1.82/1.00  
% 1.82/1.00  ------ Debug Options
% 1.82/1.00  
% 1.82/1.00  --dbg_backtrace                         false
% 1.82/1.00  --dbg_dump_prop_clauses                 false
% 1.82/1.00  --dbg_dump_prop_clauses_file            -
% 1.82/1.00  --dbg_out_stat                          false
% 1.82/1.00  
% 1.82/1.00  
% 1.82/1.00  
% 1.82/1.00  
% 1.82/1.00  ------ Proving...
% 1.82/1.00  
% 1.82/1.00  
% 1.82/1.00  % SZS status Theorem for theBenchmark.p
% 1.82/1.00  
% 1.82/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.82/1.00  
% 1.82/1.00  fof(f13,conjecture,(
% 1.82/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.82/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/1.00  
% 1.82/1.00  fof(f14,negated_conjecture,(
% 1.82/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 1.82/1.00    inference(negated_conjecture,[],[f13])).
% 1.82/1.00  
% 1.82/1.00  fof(f36,plain,(
% 1.82/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.82/1.00    inference(ennf_transformation,[],[f14])).
% 1.82/1.00  
% 1.82/1.00  fof(f37,plain,(
% 1.82/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.82/1.00    inference(flattening,[],[f36])).
% 1.82/1.00  
% 1.82/1.00  fof(f43,plain,(
% 1.82/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.82/1.00    inference(nnf_transformation,[],[f37])).
% 1.82/1.00  
% 1.82/1.00  fof(f44,plain,(
% 1.82/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.82/1.00    inference(flattening,[],[f43])).
% 1.82/1.00  
% 1.82/1.00  fof(f50,plain,(
% 1.82/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | r1_tmap_1(X1,X0,X2,X4)) & sK6 = X4 & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 1.82/1.00    introduced(choice_axiom,[])).
% 1.82/1.00  
% 1.82/1.00  fof(f49,plain,(
% 1.82/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK5)) & sK5 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 1.82/1.00    introduced(choice_axiom,[])).
% 1.82/1.00  
% 1.82/1.00  fof(f48,plain,(
% 1.82/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK4,X1) & v1_tsep_1(sK4,X1) & ~v2_struct_0(sK4))) )),
% 1.82/1.01    introduced(choice_axiom,[])).
% 1.82/1.01  
% 1.82/1.01  fof(f47,plain,(
% 1.82/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5) | ~r1_tmap_1(X1,X0,sK3,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5) | r1_tmap_1(X1,X0,sK3,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 1.82/1.01    introduced(choice_axiom,[])).
% 1.82/1.01  
% 1.82/1.01  fof(f46,plain,(
% 1.82/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5) | ~r1_tmap_1(sK2,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5) | r1_tmap_1(sK2,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK2))) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 1.82/1.01    introduced(choice_axiom,[])).
% 1.82/1.01  
% 1.82/1.01  fof(f45,plain,(
% 1.82/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5) | ~r1_tmap_1(X1,sK1,X2,X4)) & (r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5) | r1_tmap_1(X1,sK1,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.82/1.01    introduced(choice_axiom,[])).
% 1.82/1.01  
% 1.82/1.01  fof(f51,plain,(
% 1.82/1.01    ((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | ~r1_tmap_1(sK2,sK1,sK3,sK5)) & (r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | r1_tmap_1(sK2,sK1,sK3,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_pre_topc(sK4,sK2) & v1_tsep_1(sK4,sK2) & ~v2_struct_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.82/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f44,f50,f49,f48,f47,f46,f45])).
% 1.82/1.01  
% 1.82/1.01  fof(f82,plain,(
% 1.82/1.01    m1_pre_topc(sK4,sK2)),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f12,axiom,(
% 1.82/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/1.01  
% 1.82/1.01  fof(f34,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/1.01    inference(ennf_transformation,[],[f12])).
% 1.82/1.01  
% 1.82/1.01  fof(f35,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/1.01    inference(flattening,[],[f34])).
% 1.82/1.01  
% 1.82/1.01  fof(f42,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/1.01    inference(nnf_transformation,[],[f35])).
% 1.82/1.01  
% 1.82/1.01  fof(f70,plain,(
% 1.82/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/1.01    inference(cnf_transformation,[],[f42])).
% 1.82/1.01  
% 1.82/1.01  fof(f92,plain,(
% 1.82/1.01    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/1.01    inference(equality_resolution,[],[f70])).
% 1.82/1.01  
% 1.82/1.01  fof(f78,plain,(
% 1.82/1.01    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f77,plain,(
% 1.82/1.01    v1_funct_1(sK3)),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f5,axiom,(
% 1.82/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/1.01  
% 1.82/1.01  fof(f21,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/1.01    inference(ennf_transformation,[],[f5])).
% 1.82/1.01  
% 1.82/1.01  fof(f22,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/1.01    inference(flattening,[],[f21])).
% 1.82/1.01  
% 1.82/1.01  fof(f56,plain,(
% 1.82/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/1.01    inference(cnf_transformation,[],[f22])).
% 1.82/1.01  
% 1.82/1.01  fof(f6,axiom,(
% 1.82/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/1.01  
% 1.82/1.01  fof(f23,plain,(
% 1.82/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/1.01    inference(ennf_transformation,[],[f6])).
% 1.82/1.01  
% 1.82/1.01  fof(f24,plain,(
% 1.82/1.01    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/1.01    inference(flattening,[],[f23])).
% 1.82/1.01  
% 1.82/1.01  fof(f57,plain,(
% 1.82/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/1.01    inference(cnf_transformation,[],[f24])).
% 1.82/1.01  
% 1.82/1.01  fof(f74,plain,(
% 1.82/1.01    ~v2_struct_0(sK2)),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f75,plain,(
% 1.82/1.01    v2_pre_topc(sK2)),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f76,plain,(
% 1.82/1.01    l1_pre_topc(sK2)),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f80,plain,(
% 1.82/1.01    ~v2_struct_0(sK4)),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f72,plain,(
% 1.82/1.01    v2_pre_topc(sK1)),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f71,plain,(
% 1.82/1.01    ~v2_struct_0(sK1)),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f73,plain,(
% 1.82/1.01    l1_pre_topc(sK1)),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f79,plain,(
% 1.82/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f1,axiom,(
% 1.82/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/1.01  
% 1.82/1.01  fof(f15,plain,(
% 1.82/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.82/1.01    inference(ennf_transformation,[],[f1])).
% 1.82/1.01  
% 1.82/1.01  fof(f16,plain,(
% 1.82/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.82/1.01    inference(flattening,[],[f15])).
% 1.82/1.01  
% 1.82/1.01  fof(f52,plain,(
% 1.82/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.82/1.01    inference(cnf_transformation,[],[f16])).
% 1.82/1.01  
% 1.82/1.01  fof(f8,axiom,(
% 1.82/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 1.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/1.01  
% 1.82/1.01  fof(f27,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/1.01    inference(ennf_transformation,[],[f8])).
% 1.82/1.01  
% 1.82/1.01  fof(f28,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/1.01    inference(flattening,[],[f27])).
% 1.82/1.01  
% 1.82/1.01  fof(f38,plain,(
% 1.82/1.01    ! [X2,X1,X0] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => (r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_connsp_2(sK0(X0,X1,X2),X0,X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK0(X0,X1,X2))))),
% 1.82/1.01    introduced(choice_axiom,[])).
% 1.82/1.01  
% 1.82/1.01  fof(f39,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_connsp_2(sK0(X0,X1,X2),X0,X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK0(X0,X1,X2))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f38])).
% 1.82/1.01  
% 1.82/1.01  fof(f63,plain,(
% 1.82/1.01    ( ! [X2,X0,X1] : (r1_tarski(sK0(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/1.01    inference(cnf_transformation,[],[f39])).
% 1.82/1.01  
% 1.82/1.01  fof(f61,plain,(
% 1.82/1.01    ( ! [X2,X0,X1] : (m1_connsp_2(sK0(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/1.01    inference(cnf_transformation,[],[f39])).
% 1.82/1.01  
% 1.82/1.01  fof(f7,axiom,(
% 1.82/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/1.01  
% 1.82/1.01  fof(f25,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/1.01    inference(ennf_transformation,[],[f7])).
% 1.82/1.01  
% 1.82/1.01  fof(f26,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/1.01    inference(flattening,[],[f25])).
% 1.82/1.01  
% 1.82/1.01  fof(f58,plain,(
% 1.82/1.01    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/1.01    inference(cnf_transformation,[],[f26])).
% 1.82/1.01  
% 1.82/1.01  fof(f69,plain,(
% 1.82/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/1.01    inference(cnf_transformation,[],[f42])).
% 1.82/1.01  
% 1.82/1.01  fof(f93,plain,(
% 1.82/1.01    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/1.01    inference(equality_resolution,[],[f69])).
% 1.82/1.01  
% 1.82/1.01  fof(f11,axiom,(
% 1.82/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/1.01  
% 1.82/1.01  fof(f32,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/1.01    inference(ennf_transformation,[],[f11])).
% 1.82/1.01  
% 1.82/1.01  fof(f33,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/1.01    inference(flattening,[],[f32])).
% 1.82/1.01  
% 1.82/1.01  fof(f68,plain,(
% 1.82/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/1.01    inference(cnf_transformation,[],[f33])).
% 1.82/1.01  
% 1.82/1.01  fof(f91,plain,(
% 1.82/1.01    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/1.01    inference(equality_resolution,[],[f68])).
% 1.82/1.01  
% 1.82/1.01  fof(f86,plain,(
% 1.82/1.01    r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | r1_tmap_1(sK2,sK1,sK3,sK5)),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f85,plain,(
% 1.82/1.01    sK5 = sK6),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f2,axiom,(
% 1.82/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/1.01  
% 1.82/1.01  fof(f17,plain,(
% 1.82/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.82/1.01    inference(ennf_transformation,[],[f2])).
% 1.82/1.01  
% 1.82/1.01  fof(f53,plain,(
% 1.82/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.82/1.01    inference(cnf_transformation,[],[f17])).
% 1.82/1.01  
% 1.82/1.01  fof(f4,axiom,(
% 1.82/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/1.01  
% 1.82/1.01  fof(f19,plain,(
% 1.82/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.82/1.01    inference(ennf_transformation,[],[f4])).
% 1.82/1.01  
% 1.82/1.01  fof(f20,plain,(
% 1.82/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.82/1.01    inference(flattening,[],[f19])).
% 1.82/1.01  
% 1.82/1.01  fof(f55,plain,(
% 1.82/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.82/1.01    inference(cnf_transformation,[],[f20])).
% 1.82/1.01  
% 1.82/1.01  fof(f3,axiom,(
% 1.82/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/1.01  
% 1.82/1.01  fof(f18,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.82/1.01    inference(ennf_transformation,[],[f3])).
% 1.82/1.01  
% 1.82/1.01  fof(f54,plain,(
% 1.82/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.82/1.01    inference(cnf_transformation,[],[f18])).
% 1.82/1.01  
% 1.82/1.01  fof(f10,axiom,(
% 1.82/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/1.01  
% 1.82/1.01  fof(f31,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.82/1.01    inference(ennf_transformation,[],[f10])).
% 1.82/1.01  
% 1.82/1.01  fof(f67,plain,(
% 1.82/1.01    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.82/1.01    inference(cnf_transformation,[],[f31])).
% 1.82/1.01  
% 1.82/1.01  fof(f9,axiom,(
% 1.82/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 1.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.82/1.01  
% 1.82/1.01  fof(f29,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.82/1.01    inference(ennf_transformation,[],[f9])).
% 1.82/1.01  
% 1.82/1.01  fof(f30,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.82/1.01    inference(flattening,[],[f29])).
% 1.82/1.01  
% 1.82/1.01  fof(f40,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.82/1.01    inference(nnf_transformation,[],[f30])).
% 1.82/1.01  
% 1.82/1.01  fof(f41,plain,(
% 1.82/1.01    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.82/1.01    inference(flattening,[],[f40])).
% 1.82/1.01  
% 1.82/1.01  fof(f64,plain,(
% 1.82/1.01    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.82/1.01    inference(cnf_transformation,[],[f41])).
% 1.82/1.01  
% 1.82/1.01  fof(f90,plain,(
% 1.82/1.01    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.82/1.01    inference(equality_resolution,[],[f64])).
% 1.82/1.01  
% 1.82/1.01  fof(f81,plain,(
% 1.82/1.01    v1_tsep_1(sK4,sK2)),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f87,plain,(
% 1.82/1.01    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | ~r1_tmap_1(sK2,sK1,sK3,sK5)),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f84,plain,(
% 1.82/1.01    m1_subset_1(sK6,u1_struct_0(sK4))),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  fof(f83,plain,(
% 1.82/1.01    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.82/1.01    inference(cnf_transformation,[],[f51])).
% 1.82/1.01  
% 1.82/1.01  cnf(c_24,negated_conjecture,
% 1.82/1.01      ( m1_pre_topc(sK4,sK2) ),
% 1.82/1.01      inference(cnf_transformation,[],[f82]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_17,plain,
% 1.82/1.01      ( r1_tmap_1(X0,X1,X2,X3)
% 1.82/1.01      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.82/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.82/1.01      | ~ m1_connsp_2(X5,X0,X3)
% 1.82/1.01      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.82/1.01      | ~ m1_pre_topc(X4,X0)
% 1.82/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.82/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ v1_funct_1(X2)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | ~ v2_pre_topc(X0)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | v2_struct_0(X4)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | ~ l1_pre_topc(X0) ),
% 1.82/1.01      inference(cnf_transformation,[],[f92]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_28,negated_conjecture,
% 1.82/1.01      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 1.82/1.01      inference(cnf_transformation,[],[f78]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_792,plain,
% 1.82/1.01      ( r1_tmap_1(X0,X1,X2,X3)
% 1.82/1.01      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.82/1.01      | ~ m1_connsp_2(X5,X0,X3)
% 1.82/1.01      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.82/1.01      | ~ m1_pre_topc(X4,X0)
% 1.82/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.82/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ v1_funct_1(X2)
% 1.82/1.01      | ~ v2_pre_topc(X0)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X4)
% 1.82/1.01      | ~ l1_pre_topc(X0)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.82/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.82/1.01      | sK3 != X2 ),
% 1.82/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_793,plain,
% 1.82/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 1.82/1.01      | r1_tmap_1(X2,X1,sK3,X3)
% 1.82/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 1.82/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 1.82/1.01      | ~ m1_pre_topc(X0,X2)
% 1.82/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.82/1.01      | ~ v1_funct_1(sK3)
% 1.82/1.01      | ~ v2_pre_topc(X2)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X2)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | ~ l1_pre_topc(X2)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.82/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.82/1.01      inference(unflattening,[status(thm)],[c_792]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_29,negated_conjecture,
% 1.82/1.01      ( v1_funct_1(sK3) ),
% 1.82/1.01      inference(cnf_transformation,[],[f77]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_797,plain,
% 1.82/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 1.82/1.01      | ~ m1_pre_topc(X0,X2)
% 1.82/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 1.82/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 1.82/1.01      | r1_tmap_1(X2,X1,sK3,X3)
% 1.82/1.01      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 1.82/1.01      | ~ v2_pre_topc(X2)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X2)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | ~ l1_pre_topc(X2)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.82/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.82/1.01      inference(global_propositional_subsumption,
% 1.82/1.01                [status(thm)],
% 1.82/1.01                [c_793,c_29]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_798,plain,
% 1.82/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 1.82/1.01      | r1_tmap_1(X2,X1,sK3,X3)
% 1.82/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 1.82/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 1.82/1.01      | ~ m1_pre_topc(X0,X2)
% 1.82/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | ~ v2_pre_topc(X2)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X2)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | ~ l1_pre_topc(X2)
% 1.82/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.82/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.82/1.01      inference(renaming,[status(thm)],[c_797]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_4,plain,
% 1.82/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.82/1.01      | m1_subset_1(X2,u1_struct_0(X1))
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | ~ l1_pre_topc(X1) ),
% 1.82/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_5,plain,
% 1.82/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.82/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | ~ l1_pre_topc(X1) ),
% 1.82/1.01      inference(cnf_transformation,[],[f57]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_839,plain,
% 1.82/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 1.82/1.01      | r1_tmap_1(X2,X1,sK3,X3)
% 1.82/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 1.82/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 1.82/1.01      | ~ m1_pre_topc(X0,X2)
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | ~ v2_pre_topc(X2)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X2)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | ~ l1_pre_topc(X2)
% 1.82/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.82/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.82/1.01      inference(forward_subsumption_resolution,
% 1.82/1.01                [status(thm)],
% 1.82/1.01                [c_798,c_4,c_5]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1016,plain,
% 1.82/1.01      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 1.82/1.01      | r1_tmap_1(X2,X1,sK3,X3)
% 1.82/1.01      | ~ m1_connsp_2(X4,X2,X3)
% 1.82/1.01      | ~ r1_tarski(X4,u1_struct_0(X0))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.82/1.01      | ~ v2_pre_topc(X2)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | v2_struct_0(X2)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | ~ l1_pre_topc(X2)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.82/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.82/1.01      | sK2 != X2
% 1.82/1.01      | sK4 != X0 ),
% 1.82/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_839]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1017,plain,
% 1.82/1.01      ( r1_tmap_1(sK2,X0,sK3,X1)
% 1.82/1.01      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.82/1.01      | ~ m1_connsp_2(X2,sK2,X1)
% 1.82/1.01      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.82/1.01      | ~ v2_pre_topc(X0)
% 1.82/1.01      | ~ v2_pre_topc(sK2)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | v2_struct_0(sK2)
% 1.82/1.01      | v2_struct_0(sK4)
% 1.82/1.01      | ~ l1_pre_topc(X0)
% 1.82/1.01      | ~ l1_pre_topc(sK2)
% 1.82/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.82/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.82/1.01      inference(unflattening,[status(thm)],[c_1016]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_32,negated_conjecture,
% 1.82/1.01      ( ~ v2_struct_0(sK2) ),
% 1.82/1.01      inference(cnf_transformation,[],[f74]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_31,negated_conjecture,
% 1.82/1.01      ( v2_pre_topc(sK2) ),
% 1.82/1.01      inference(cnf_transformation,[],[f75]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_30,negated_conjecture,
% 1.82/1.01      ( l1_pre_topc(sK2) ),
% 1.82/1.01      inference(cnf_transformation,[],[f76]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_26,negated_conjecture,
% 1.82/1.01      ( ~ v2_struct_0(sK4) ),
% 1.82/1.01      inference(cnf_transformation,[],[f80]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1021,plain,
% 1.82/1.01      ( ~ l1_pre_topc(X0)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | r1_tmap_1(sK2,X0,sK3,X1)
% 1.82/1.01      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.82/1.01      | ~ m1_connsp_2(X2,sK2,X1)
% 1.82/1.01      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.82/1.01      | ~ v2_pre_topc(X0)
% 1.82/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.82/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.82/1.01      inference(global_propositional_subsumption,
% 1.82/1.01                [status(thm)],
% 1.82/1.01                [c_1017,c_32,c_31,c_30,c_26]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1022,plain,
% 1.82/1.01      ( r1_tmap_1(sK2,X0,sK3,X1)
% 1.82/1.01      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.82/1.01      | ~ m1_connsp_2(X2,sK2,X1)
% 1.82/1.01      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.82/1.01      | ~ v2_pre_topc(X0)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | ~ l1_pre_topc(X0)
% 1.82/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.82/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.82/1.01      inference(renaming,[status(thm)],[c_1021]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_34,negated_conjecture,
% 1.82/1.01      ( v2_pre_topc(sK1) ),
% 1.82/1.01      inference(cnf_transformation,[],[f72]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1250,plain,
% 1.82/1.01      ( r1_tmap_1(sK2,X0,sK3,X1)
% 1.82/1.01      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.82/1.01      | ~ m1_connsp_2(X2,sK2,X1)
% 1.82/1.01      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | ~ l1_pre_topc(X0)
% 1.82/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.82/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.82/1.01      | sK1 != X0 ),
% 1.82/1.01      inference(resolution_lifted,[status(thm)],[c_1022,c_34]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1251,plain,
% 1.82/1.01      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 1.82/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.82/1.01      | ~ m1_connsp_2(X1,sK2,X0)
% 1.82/1.01      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.82/1.01      | v2_struct_0(sK1)
% 1.82/1.01      | ~ l1_pre_topc(sK1)
% 1.82/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.82/1.01      inference(unflattening,[status(thm)],[c_1250]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_35,negated_conjecture,
% 1.82/1.01      ( ~ v2_struct_0(sK1) ),
% 1.82/1.01      inference(cnf_transformation,[],[f71]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_33,negated_conjecture,
% 1.82/1.01      ( l1_pre_topc(sK1) ),
% 1.82/1.01      inference(cnf_transformation,[],[f73]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_27,negated_conjecture,
% 1.82/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 1.82/1.01      inference(cnf_transformation,[],[f79]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1255,plain,
% 1.82/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.82/1.01      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_connsp_2(X1,sK2,X0)
% 1.82/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.82/1.01      | r1_tmap_1(sK2,sK1,sK3,X0)
% 1.82/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.82/1.01      inference(global_propositional_subsumption,
% 1.82/1.01                [status(thm)],
% 1.82/1.01                [c_1251,c_35,c_33,c_27]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1256,plain,
% 1.82/1.01      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 1.82/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.82/1.01      | ~ m1_connsp_2(X1,sK2,X0)
% 1.82/1.01      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.82/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.82/1.01      inference(renaming,[status(thm)],[c_1255]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_2214,plain,
% 1.82/1.01      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 1.82/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.82/1.01      | ~ m1_connsp_2(X1,sK2,X0)
% 1.82/1.01      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 1.82/1.01      inference(equality_resolution_simp,[status(thm)],[c_1256]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_2854,plain,
% 1.82/1.01      ( r1_tmap_1(sK2,sK1,sK3,X0_55)
% 1.82/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_55)
% 1.82/1.01      | ~ m1_connsp_2(X1_55,sK2,X0_55)
% 1.82/1.01      | ~ r1_tarski(X1_55,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK4)) ),
% 1.82/1.01      inference(subtyping,[status(esa)],[c_2214]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_4478,plain,
% 1.82/1.01      ( r1_tmap_1(sK2,sK1,sK3,X0_55)
% 1.82/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_55)
% 1.82/1.01      | ~ m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,X0_55)
% 1.82/1.01      | ~ r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK4)) ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_2854]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_4942,plain,
% 1.82/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK5)
% 1.82/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
% 1.82/1.01      | ~ m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,sK5)
% 1.82/1.01      | ~ r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_4478]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_0,plain,
% 1.82/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.82/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_2883,plain,
% 1.82/1.01      ( ~ m1_subset_1(X0_55,X1_55)
% 1.82/1.01      | r2_hidden(X0_55,X1_55)
% 1.82/1.01      | v1_xboole_0(X1_55) ),
% 1.82/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_4329,plain,
% 1.82/1.01      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 1.82/1.01      | r2_hidden(sK5,u1_struct_0(sK4))
% 1.82/1.01      | v1_xboole_0(u1_struct_0(sK4)) ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_2883]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_7,plain,
% 1.82/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.82/1.01      | r1_tarski(sK0(X1,X2,X0),X0)
% 1.82/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | ~ l1_pre_topc(X1) ),
% 1.82/1.01      inference(cnf_transformation,[],[f63]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_240,plain,
% 1.82/1.01      ( r1_tarski(sK0(X1,X2,X0),X0)
% 1.82/1.01      | ~ m1_connsp_2(X0,X1,X2)
% 1.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | ~ l1_pre_topc(X1) ),
% 1.82/1.01      inference(global_propositional_subsumption,[status(thm)],[c_7,c_5]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_241,plain,
% 1.82/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.82/1.01      | r1_tarski(sK0(X1,X2,X0),X0)
% 1.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | ~ l1_pre_topc(X1) ),
% 1.82/1.01      inference(renaming,[status(thm)],[c_240]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1280,plain,
% 1.82/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.82/1.01      | r1_tarski(sK0(X1,X2,X0),X0)
% 1.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | sK2 != X1 ),
% 1.82/1.01      inference(resolution_lifted,[status(thm)],[c_241,c_31]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1281,plain,
% 1.82/1.01      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.82/1.01      | r1_tarski(sK0(sK2,X1,X0),X0)
% 1.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.82/1.01      | v2_struct_0(sK2)
% 1.82/1.01      | ~ l1_pre_topc(sK2) ),
% 1.82/1.01      inference(unflattening,[status(thm)],[c_1280]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1285,plain,
% 1.82/1.01      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.82/1.01      | r1_tarski(sK0(sK2,X1,X0),X0)
% 1.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.82/1.01      inference(global_propositional_subsumption,
% 1.82/1.01                [status(thm)],
% 1.82/1.01                [c_1281,c_32,c_30]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_2871,plain,
% 1.82/1.01      ( ~ m1_connsp_2(X0_55,sK2,X1_55)
% 1.82/1.01      | r1_tarski(sK0(sK2,X1_55,X0_55),X0_55)
% 1.82/1.01      | ~ m1_subset_1(X1_55,u1_struct_0(sK2)) ),
% 1.82/1.01      inference(subtyping,[status(esa)],[c_1285]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_3968,plain,
% 1.82/1.01      ( ~ m1_connsp_2(X0_55,sK2,sK5)
% 1.82/1.01      | r1_tarski(sK0(sK2,sK5,X0_55),X0_55)
% 1.82/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_2871]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_4300,plain,
% 1.82/1.01      ( ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK5)
% 1.82/1.01      | r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_3968]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_9,plain,
% 1.82/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.82/1.01      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 1.82/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | ~ l1_pre_topc(X1) ),
% 1.82/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_226,plain,
% 1.82/1.01      ( m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 1.82/1.01      | ~ m1_connsp_2(X0,X1,X2)
% 1.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | ~ l1_pre_topc(X1) ),
% 1.82/1.01      inference(global_propositional_subsumption,[status(thm)],[c_9,c_5]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_227,plain,
% 1.82/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.82/1.01      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 1.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | ~ l1_pre_topc(X1) ),
% 1.82/1.01      inference(renaming,[status(thm)],[c_226]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1322,plain,
% 1.82/1.01      ( ~ m1_connsp_2(X0,X1,X2)
% 1.82/1.01      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 1.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | sK2 != X1 ),
% 1.82/1.01      inference(resolution_lifted,[status(thm)],[c_227,c_31]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1323,plain,
% 1.82/1.01      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.82/1.01      | m1_connsp_2(sK0(sK2,X1,X0),sK2,X1)
% 1.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.82/1.01      | v2_struct_0(sK2)
% 1.82/1.01      | ~ l1_pre_topc(sK2) ),
% 1.82/1.01      inference(unflattening,[status(thm)],[c_1322]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1327,plain,
% 1.82/1.01      ( ~ m1_connsp_2(X0,sK2,X1)
% 1.82/1.01      | m1_connsp_2(sK0(sK2,X1,X0),sK2,X1)
% 1.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 1.82/1.01      inference(global_propositional_subsumption,
% 1.82/1.01                [status(thm)],
% 1.82/1.01                [c_1323,c_32,c_30]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_2869,plain,
% 1.82/1.01      ( ~ m1_connsp_2(X0_55,sK2,X1_55)
% 1.82/1.01      | m1_connsp_2(sK0(sK2,X1_55,X0_55),sK2,X1_55)
% 1.82/1.01      | ~ m1_subset_1(X1_55,u1_struct_0(sK2)) ),
% 1.82/1.01      inference(subtyping,[status(esa)],[c_1327]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_3963,plain,
% 1.82/1.01      ( ~ m1_connsp_2(X0_55,sK2,sK5)
% 1.82/1.01      | m1_connsp_2(sK0(sK2,sK5,X0_55),sK2,sK5)
% 1.82/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_2869]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_4301,plain,
% 1.82/1.01      ( m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,sK5)
% 1.82/1.01      | ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK5)
% 1.82/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_3963]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_6,plain,
% 1.82/1.01      ( m1_connsp_2(X0,X1,X2)
% 1.82/1.01      | ~ v3_pre_topc(X0,X1)
% 1.82/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.82/1.01      | ~ r2_hidden(X2,X0)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | ~ l1_pre_topc(X1) ),
% 1.82/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1385,plain,
% 1.82/1.01      ( m1_connsp_2(X0,X1,X2)
% 1.82/1.01      | ~ v3_pre_topc(X0,X1)
% 1.82/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.82/1.01      | ~ r2_hidden(X2,X0)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | sK2 != X1 ),
% 1.82/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_31]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1386,plain,
% 1.82/1.01      ( m1_connsp_2(X0,sK2,X1)
% 1.82/1.01      | ~ v3_pre_topc(X0,sK2)
% 1.82/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.82/1.01      | ~ r2_hidden(X1,X0)
% 1.82/1.01      | v2_struct_0(sK2)
% 1.82/1.01      | ~ l1_pre_topc(sK2) ),
% 1.82/1.01      inference(unflattening,[status(thm)],[c_1385]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1390,plain,
% 1.82/1.01      ( m1_connsp_2(X0,sK2,X1)
% 1.82/1.01      | ~ v3_pre_topc(X0,sK2)
% 1.82/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.82/1.01      | ~ r2_hidden(X1,X0) ),
% 1.82/1.01      inference(global_propositional_subsumption,
% 1.82/1.01                [status(thm)],
% 1.82/1.01                [c_1386,c_32,c_30]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_2866,plain,
% 1.82/1.01      ( m1_connsp_2(X0_55,sK2,X1_55)
% 1.82/1.01      | ~ v3_pre_topc(X0_55,sK2)
% 1.82/1.01      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.82/1.01      | ~ m1_subset_1(X1_55,u1_struct_0(sK2))
% 1.82/1.01      | ~ r2_hidden(X1_55,X0_55) ),
% 1.82/1.01      inference(subtyping,[status(esa)],[c_1390]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_3981,plain,
% 1.82/1.01      ( m1_connsp_2(u1_struct_0(sK4),sK2,X0_55)
% 1.82/1.01      | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
% 1.82/1.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK2))
% 1.82/1.01      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.82/1.01      | ~ r2_hidden(X0_55,u1_struct_0(sK4)) ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_2866]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_4244,plain,
% 1.82/1.01      ( m1_connsp_2(u1_struct_0(sK4),sK2,sK5)
% 1.82/1.01      | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
% 1.82/1.01      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.82/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 1.82/1.01      | ~ r2_hidden(sK5,u1_struct_0(sK4)) ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_3981]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_2889,plain,( X0_55 = X0_55 ),theory(equality) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_4187,plain,
% 1.82/1.01      ( k2_tmap_1(sK2,sK1,sK3,sK4) = k2_tmap_1(sK2,sK1,sK3,sK4) ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_2889]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_2898,plain,
% 1.82/1.01      ( ~ r1_tmap_1(X0_54,X1_54,X0_55,X1_55)
% 1.82/1.01      | r1_tmap_1(X0_54,X1_54,X2_55,X3_55)
% 1.82/1.01      | X2_55 != X0_55
% 1.82/1.01      | X3_55 != X1_55 ),
% 1.82/1.01      theory(equality) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_4032,plain,
% 1.82/1.01      ( r1_tmap_1(sK4,sK1,X0_55,X1_55)
% 1.82/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 1.82/1.01      | X0_55 != k2_tmap_1(sK2,sK1,sK3,sK4)
% 1.82/1.01      | X1_55 != sK6 ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_2898]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_4143,plain,
% 1.82/1.01      ( r1_tmap_1(sK4,sK1,X0_55,sK5)
% 1.82/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 1.82/1.01      | X0_55 != k2_tmap_1(sK2,sK1,sK3,sK4)
% 1.82/1.01      | sK5 != sK6 ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_4032]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_4186,plain,
% 1.82/1.01      ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
% 1.82/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 1.82/1.01      | k2_tmap_1(sK2,sK1,sK3,sK4) != k2_tmap_1(sK2,sK1,sK3,sK4)
% 1.82/1.01      | sK5 != sK6 ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_4143]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_4182,plain,
% 1.82/1.01      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_2889]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_2892,plain,
% 1.82/1.01      ( ~ m1_subset_1(X0_55,X1_55)
% 1.82/1.01      | m1_subset_1(X2_55,X3_55)
% 1.82/1.01      | X2_55 != X0_55
% 1.82/1.01      | X3_55 != X1_55 ),
% 1.82/1.01      theory(equality) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_4008,plain,
% 1.82/1.01      ( m1_subset_1(X0_55,X1_55)
% 1.82/1.01      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 1.82/1.01      | X1_55 != u1_struct_0(sK4)
% 1.82/1.01      | X0_55 != sK6 ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_2892]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_4109,plain,
% 1.82/1.01      ( m1_subset_1(sK5,X0_55)
% 1.82/1.01      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 1.82/1.01      | X0_55 != u1_struct_0(sK4)
% 1.82/1.01      | sK5 != sK6 ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_4008]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_4181,plain,
% 1.82/1.01      ( m1_subset_1(sK5,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 1.82/1.01      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 1.82/1.01      | sK5 != sK6 ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_4109]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_18,plain,
% 1.82/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.82/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.82/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.82/1.01      | ~ m1_connsp_2(X5,X0,X3)
% 1.82/1.01      | ~ r1_tarski(X5,u1_struct_0(X4))
% 1.82/1.01      | ~ m1_pre_topc(X4,X0)
% 1.82/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.82/1.01      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ v1_funct_1(X2)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | ~ v2_pre_topc(X0)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | v2_struct_0(X4)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | ~ l1_pre_topc(X0) ),
% 1.82/1.01      inference(cnf_transformation,[],[f93]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_16,plain,
% 1.82/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.82/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.82/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.82/1.01      | ~ m1_pre_topc(X4,X0)
% 1.82/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ v1_funct_1(X2)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | ~ v2_pre_topc(X0)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | v2_struct_0(X4)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | ~ l1_pre_topc(X0) ),
% 1.82/1.01      inference(cnf_transformation,[],[f91]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_190,plain,
% 1.82/1.01      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.82/1.01      | ~ m1_pre_topc(X4,X0)
% 1.82/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.82/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.82/1.01      | ~ r1_tmap_1(X0,X1,X2,X3)
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ v1_funct_1(X2)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | ~ v2_pre_topc(X0)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | v2_struct_0(X4)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | ~ l1_pre_topc(X0) ),
% 1.82/1.01      inference(global_propositional_subsumption,
% 1.82/1.01                [status(thm)],
% 1.82/1.01                [c_18,c_16]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_191,plain,
% 1.82/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.82/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.82/1.01      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 1.82/1.01      | ~ m1_pre_topc(X4,X0)
% 1.82/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ v1_funct_1(X2)
% 1.82/1.01      | ~ v2_pre_topc(X0)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X4)
% 1.82/1.01      | ~ l1_pre_topc(X0)
% 1.82/1.01      | ~ l1_pre_topc(X1) ),
% 1.82/1.01      inference(renaming,[status(thm)],[c_190]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_735,plain,
% 1.82/1.01      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 1.82/1.01      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 1.82/1.01      | ~ m1_pre_topc(X4,X0)
% 1.82/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ v1_funct_1(X2)
% 1.82/1.01      | ~ v2_pre_topc(X0)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X4)
% 1.82/1.01      | ~ l1_pre_topc(X0)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | u1_struct_0(X0) != u1_struct_0(sK2)
% 1.82/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.82/1.01      | sK3 != X2 ),
% 1.82/1.01      inference(resolution_lifted,[status(thm)],[c_191,c_28]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_736,plain,
% 1.82/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 1.82/1.01      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 1.82/1.01      | ~ m1_pre_topc(X0,X2)
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.82/1.01      | ~ v1_funct_1(sK3)
% 1.82/1.01      | ~ v2_pre_topc(X2)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X2)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | ~ l1_pre_topc(X2)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.82/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.82/1.01      inference(unflattening,[status(thm)],[c_735]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_740,plain,
% 1.82/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ m1_pre_topc(X0,X2)
% 1.82/1.01      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 1.82/1.01      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 1.82/1.01      | ~ v2_pre_topc(X2)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X2)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | ~ l1_pre_topc(X2)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.82/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.82/1.01      inference(global_propositional_subsumption,
% 1.82/1.01                [status(thm)],
% 1.82/1.01                [c_736,c_29]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_741,plain,
% 1.82/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 1.82/1.01      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 1.82/1.01      | ~ m1_pre_topc(X0,X2)
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | ~ v2_pre_topc(X2)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X2)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | ~ l1_pre_topc(X2)
% 1.82/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.82/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.82/1.01      inference(renaming,[status(thm)],[c_740]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_776,plain,
% 1.82/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 1.82/1.01      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 1.82/1.01      | ~ m1_pre_topc(X0,X2)
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | ~ v2_pre_topc(X2)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | v2_struct_0(X2)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | ~ l1_pre_topc(X2)
% 1.82/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.82/1.01      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 1.82/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_741,c_4]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1061,plain,
% 1.82/1.01      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 1.82/1.01      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 1.82/1.01      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 1.82/1.01      | ~ v2_pre_topc(X2)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | v2_struct_0(X2)
% 1.82/1.01      | v2_struct_0(X1)
% 1.82/1.01      | ~ l1_pre_topc(X2)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | u1_struct_0(X2) != u1_struct_0(sK2)
% 1.82/1.01      | u1_struct_0(X1) != u1_struct_0(sK1)
% 1.82/1.01      | sK2 != X2
% 1.82/1.01      | sK4 != X0 ),
% 1.82/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_776]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1062,plain,
% 1.82/1.01      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.82/1.01      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.82/1.01      | ~ v2_pre_topc(X0)
% 1.82/1.01      | ~ v2_pre_topc(sK2)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | v2_struct_0(sK2)
% 1.82/1.01      | v2_struct_0(sK4)
% 1.82/1.01      | ~ l1_pre_topc(X0)
% 1.82/1.01      | ~ l1_pre_topc(sK2)
% 1.82/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.82/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.82/1.01      inference(unflattening,[status(thm)],[c_1061]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1066,plain,
% 1.82/1.01      ( ~ l1_pre_topc(X0)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.82/1.01      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.82/1.01      | ~ v2_pre_topc(X0)
% 1.82/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.82/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.82/1.01      inference(global_propositional_subsumption,
% 1.82/1.01                [status(thm)],
% 1.82/1.01                [c_1062,c_32,c_31,c_30,c_26]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1067,plain,
% 1.82/1.01      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.82/1.01      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.82/1.01      | ~ v2_pre_topc(X0)
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | ~ l1_pre_topc(X0)
% 1.82/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.82/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 1.82/1.01      inference(renaming,[status(thm)],[c_1066]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1226,plain,
% 1.82/1.01      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 1.82/1.01      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 1.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 1.82/1.01      | v2_struct_0(X0)
% 1.82/1.01      | ~ l1_pre_topc(X0)
% 1.82/1.01      | u1_struct_0(X0) != u1_struct_0(sK1)
% 1.82/1.01      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 1.82/1.01      | sK1 != X0 ),
% 1.82/1.01      inference(resolution_lifted,[status(thm)],[c_1067,c_34]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1227,plain,
% 1.82/1.01      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 1.82/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.82/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.82/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 1.82/1.01      | v2_struct_0(sK1)
% 1.82/1.01      | ~ l1_pre_topc(sK1)
% 1.82/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.82/1.01      inference(unflattening,[status(thm)],[c_1226]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1231,plain,
% 1.82/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.82/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.82/1.01      | ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 1.82/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.82/1.01      inference(global_propositional_subsumption,
% 1.82/1.01                [status(thm)],
% 1.82/1.01                [c_1227,c_35,c_33,c_27]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1232,plain,
% 1.82/1.01      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 1.82/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.82/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 1.82/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.82/1.01      inference(renaming,[status(thm)],[c_1231]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_2218,plain,
% 1.82/1.01      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 1.82/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 1.82/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 1.82/1.01      inference(equality_resolution_simp,[status(thm)],[c_1232]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_2853,plain,
% 1.82/1.01      ( ~ r1_tmap_1(sK2,sK1,sK3,X0_55)
% 1.82/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_55)
% 1.82/1.01      | ~ m1_subset_1(X0_55,u1_struct_0(sK4)) ),
% 1.82/1.01      inference(subtyping,[status(esa)],[c_2218]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_3986,plain,
% 1.82/1.01      ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
% 1.82/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 1.82/1.01      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.82/1.01      inference(instantiation,[status(thm)],[c_2853]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_20,negated_conjecture,
% 1.82/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK5)
% 1.82/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 1.82/1.01      inference(cnf_transformation,[],[f86]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_2881,negated_conjecture,
% 1.82/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK5)
% 1.82/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 1.82/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_3654,plain,
% 1.82/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
% 1.82/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
% 1.82/1.01      inference(predicate_to_equality,[status(thm)],[c_2881]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_21,negated_conjecture,
% 1.82/1.01      ( sK5 = sK6 ),
% 1.82/1.01      inference(cnf_transformation,[],[f85]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_2880,negated_conjecture,
% 1.82/1.01      ( sK5 = sK6 ),
% 1.82/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_3713,plain,
% 1.82/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
% 1.82/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
% 1.82/1.01      inference(light_normalisation,[status(thm)],[c_3654,c_2880]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_3870,plain,
% 1.82/1.01      ( r1_tmap_1(sK2,sK1,sK3,sK6)
% 1.82/1.01      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 1.82/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3713]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1,plain,
% 1.82/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.82/1.01      inference(cnf_transformation,[],[f53]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_3,plain,
% 1.82/1.01      ( v2_struct_0(X0)
% 1.82/1.01      | ~ l1_struct_0(X0)
% 1.82/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.82/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_484,plain,
% 1.82/1.01      ( v2_struct_0(X0)
% 1.82/1.01      | ~ l1_pre_topc(X0)
% 1.82/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.82/1.01      inference(resolution,[status(thm)],[c_1,c_3]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_2,plain,
% 1.82/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.82/1.01      inference(cnf_transformation,[],[f54]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1005,plain,
% 1.82/1.01      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X0 | sK4 != X1 ),
% 1.82/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_24]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1006,plain,
% 1.82/1.01      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 1.82/1.01      inference(unflattening,[status(thm)],[c_1005]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1008,plain,
% 1.82/1.01      ( l1_pre_topc(sK4) ),
% 1.82/1.01      inference(global_propositional_subsumption,
% 1.82/1.01                [status(thm)],
% 1.82/1.01                [c_1006,c_30]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1694,plain,
% 1.82/1.01      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK4 != X0 ),
% 1.82/1.01      inference(resolution_lifted,[status(thm)],[c_484,c_1008]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_1695,plain,
% 1.82/1.01      ( v2_struct_0(sK4) | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 1.82/1.01      inference(unflattening,[status(thm)],[c_1694]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_15,plain,
% 1.82/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.82/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/1.01      | ~ l1_pre_topc(X1) ),
% 1.82/1.01      inference(cnf_transformation,[],[f67]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_976,plain,
% 1.82/1.01      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | sK2 != X1
% 1.82/1.01      | sK4 != X0 ),
% 1.82/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_977,plain,
% 1.82/1.01      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.82/1.01      | ~ l1_pre_topc(sK2) ),
% 1.82/1.01      inference(unflattening,[status(thm)],[c_976]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_14,plain,
% 1.82/1.01      ( ~ v1_tsep_1(X0,X1)
% 1.82/1.01      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.82/1.01      | ~ m1_pre_topc(X0,X1)
% 1.82/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | ~ l1_pre_topc(X1) ),
% 1.82/1.01      inference(cnf_transformation,[],[f90]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_198,plain,
% 1.82/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.82/1.01      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.82/1.01      | ~ v1_tsep_1(X0,X1)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | ~ l1_pre_topc(X1) ),
% 1.82/1.01      inference(global_propositional_subsumption,
% 1.82/1.01                [status(thm)],
% 1.82/1.01                [c_14,c_15]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_199,plain,
% 1.82/1.01      ( ~ v1_tsep_1(X0,X1)
% 1.82/1.01      | v3_pre_topc(u1_struct_0(X0),X1)
% 1.82/1.01      | ~ m1_pre_topc(X0,X1)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | ~ l1_pre_topc(X1) ),
% 1.82/1.01      inference(renaming,[status(thm)],[c_198]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_25,negated_conjecture,
% 1.82/1.01      ( v1_tsep_1(sK4,sK2) ),
% 1.82/1.01      inference(cnf_transformation,[],[f81]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_601,plain,
% 1.82/1.01      ( v3_pre_topc(u1_struct_0(X0),X1)
% 1.82/1.01      | ~ m1_pre_topc(X0,X1)
% 1.82/1.01      | ~ v2_pre_topc(X1)
% 1.82/1.01      | ~ l1_pre_topc(X1)
% 1.82/1.01      | sK2 != X1
% 1.82/1.01      | sK4 != X0 ),
% 1.82/1.01      inference(resolution_lifted,[status(thm)],[c_199,c_25]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_602,plain,
% 1.82/1.01      ( v3_pre_topc(u1_struct_0(sK4),sK2)
% 1.82/1.01      | ~ m1_pre_topc(sK4,sK2)
% 1.82/1.01      | ~ v2_pre_topc(sK2)
% 1.82/1.01      | ~ l1_pre_topc(sK2) ),
% 1.82/1.01      inference(unflattening,[status(thm)],[c_601]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_19,negated_conjecture,
% 1.82/1.01      ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
% 1.82/1.01      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 1.82/1.01      inference(cnf_transformation,[],[f87]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_22,negated_conjecture,
% 1.82/1.01      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 1.82/1.01      inference(cnf_transformation,[],[f84]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(c_23,negated_conjecture,
% 1.82/1.01      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 1.82/1.01      inference(cnf_transformation,[],[f83]) ).
% 1.82/1.01  
% 1.82/1.01  cnf(contradiction,plain,
% 1.82/1.01      ( $false ),
% 1.82/1.01      inference(minisat,
% 1.82/1.01                [status(thm)],
% 1.82/1.01                [c_4942,c_4329,c_4300,c_4301,c_4244,c_4187,c_4186,c_4182,
% 1.82/1.01                 c_4181,c_3986,c_3870,c_2880,c_1695,c_977,c_602,c_19,
% 1.82/1.01                 c_22,c_23,c_24,c_26,c_30,c_31]) ).
% 1.82/1.01  
% 1.82/1.01  
% 1.82/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.82/1.01  
% 1.82/1.01  ------                               Statistics
% 1.82/1.01  
% 1.82/1.01  ------ General
% 1.82/1.01  
% 1.82/1.01  abstr_ref_over_cycles:                  0
% 1.82/1.01  abstr_ref_under_cycles:                 0
% 1.82/1.01  gc_basic_clause_elim:                   0
% 1.82/1.01  forced_gc_time:                         0
% 1.82/1.01  parsing_time:                           0.015
% 1.82/1.01  unif_index_cands_time:                  0.
% 1.82/1.01  unif_index_add_time:                    0.
% 1.82/1.01  orderings_time:                         0.
% 1.82/1.01  out_proof_time:                         0.018
% 1.82/1.01  total_time:                             0.162
% 1.82/1.01  num_of_symbols:                         61
% 1.82/1.01  num_of_terms:                           3034
% 1.82/1.01  
% 1.82/1.01  ------ Preprocessing
% 1.82/1.01  
% 1.82/1.01  num_of_splits:                          2
% 1.82/1.01  num_of_split_atoms:                     2
% 1.82/1.01  num_of_reused_defs:                     0
% 1.82/1.01  num_eq_ax_congr_red:                    28
% 1.82/1.01  num_of_sem_filtered_clauses:            1
% 1.82/1.01  num_of_subtypes:                        2
% 1.82/1.01  monotx_restored_types:                  0
% 1.82/1.01  sat_num_of_epr_types:                   0
% 1.82/1.01  sat_num_of_non_cyclic_types:            0
% 1.82/1.01  sat_guarded_non_collapsed_types:        0
% 1.82/1.01  num_pure_diseq_elim:                    0
% 1.82/1.01  simp_replaced_by:                       0
% 1.82/1.01  res_preprocessed:                       155
% 1.82/1.01  prep_upred:                             0
% 1.82/1.01  prep_unflattend:                        96
% 1.82/1.01  smt_new_axioms:                         0
% 1.82/1.01  pred_elim_cands:                        7
% 1.82/1.01  pred_elim:                              8
% 1.82/1.01  pred_elim_cl:                           4
% 1.82/1.01  pred_elim_cycles:                       22
% 1.82/1.01  merged_defs:                            8
% 1.82/1.01  merged_defs_ncl:                        0
% 1.82/1.01  bin_hyper_res:                          8
% 1.82/1.01  prep_cycles:                            4
% 1.82/1.01  pred_elim_time:                         0.049
% 1.82/1.01  splitting_time:                         0.
% 1.82/1.01  sem_filter_time:                        0.
% 1.82/1.01  monotx_time:                            0.
% 1.82/1.01  subtype_inf_time:                       0.
% 1.82/1.01  
% 1.82/1.01  ------ Problem properties
% 1.82/1.01  
% 1.82/1.01  clauses:                                33
% 1.82/1.01  conjectures:                            6
% 1.82/1.01  epr:                                    2
% 1.82/1.01  horn:                                   31
% 1.82/1.01  ground:                                 13
% 1.82/1.01  unary:                                  9
% 1.82/1.01  binary:                                 3
% 1.82/1.01  lits:                                   88
% 1.82/1.01  lits_eq:                                3
% 1.82/1.01  fd_pure:                                0
% 1.82/1.01  fd_pseudo:                              0
% 1.82/1.01  fd_cond:                                0
% 1.82/1.01  fd_pseudo_cond:                         0
% 1.82/1.01  ac_symbols:                             0
% 1.82/1.01  
% 1.82/1.01  ------ Propositional Solver
% 1.82/1.01  
% 1.82/1.01  prop_solver_calls:                      26
% 1.82/1.01  prop_fast_solver_calls:                 1744
% 1.82/1.01  smt_solver_calls:                       0
% 1.82/1.01  smt_fast_solver_calls:                  0
% 1.82/1.01  prop_num_of_clauses:                    1077
% 1.82/1.01  prop_preprocess_simplified:             4951
% 1.82/1.01  prop_fo_subsumed:                       83
% 1.82/1.01  prop_solver_time:                       0.
% 1.82/1.01  smt_solver_time:                        0.
% 1.82/1.01  smt_fast_solver_time:                   0.
% 1.82/1.01  prop_fast_solver_time:                  0.
% 1.82/1.01  prop_unsat_core_time:                   0.
% 1.82/1.01  
% 1.82/1.01  ------ QBF
% 1.82/1.01  
% 1.82/1.01  qbf_q_res:                              0
% 1.82/1.01  qbf_num_tautologies:                    0
% 1.82/1.01  qbf_prep_cycles:                        0
% 1.82/1.01  
% 1.82/1.01  ------ BMC1
% 1.82/1.01  
% 1.82/1.01  bmc1_current_bound:                     -1
% 1.82/1.01  bmc1_last_solved_bound:                 -1
% 1.82/1.01  bmc1_unsat_core_size:                   -1
% 1.82/1.01  bmc1_unsat_core_parents_size:           -1
% 1.82/1.01  bmc1_merge_next_fun:                    0
% 1.82/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.82/1.01  
% 1.82/1.01  ------ Instantiation
% 1.82/1.01  
% 1.82/1.01  inst_num_of_clauses:                    226
% 1.82/1.01  inst_num_in_passive:                    16
% 1.82/1.01  inst_num_in_active:                     166
% 1.82/1.01  inst_num_in_unprocessed:                43
% 1.82/1.01  inst_num_of_loops:                      171
% 1.82/1.01  inst_num_of_learning_restarts:          0
% 1.82/1.01  inst_num_moves_active_passive:          1
% 1.82/1.01  inst_lit_activity:                      0
% 1.82/1.01  inst_lit_activity_moves:                0
% 1.82/1.01  inst_num_tautologies:                   0
% 1.82/1.01  inst_num_prop_implied:                  0
% 1.82/1.01  inst_num_existing_simplified:           0
% 1.82/1.01  inst_num_eq_res_simplified:             0
% 1.82/1.01  inst_num_child_elim:                    0
% 1.82/1.01  inst_num_of_dismatching_blockings:      4
% 1.82/1.01  inst_num_of_non_proper_insts:           168
% 1.82/1.01  inst_num_of_duplicates:                 0
% 1.82/1.01  inst_inst_num_from_inst_to_res:         0
% 1.82/1.01  inst_dismatching_checking_time:         0.
% 1.82/1.01  
% 1.82/1.01  ------ Resolution
% 1.82/1.01  
% 1.82/1.01  res_num_of_clauses:                     0
% 1.82/1.01  res_num_in_passive:                     0
% 1.82/1.01  res_num_in_active:                      0
% 1.82/1.01  res_num_of_loops:                       159
% 1.82/1.01  res_forward_subset_subsumed:            39
% 1.82/1.01  res_backward_subset_subsumed:           0
% 1.82/1.01  res_forward_subsumed:                   0
% 1.82/1.01  res_backward_subsumed:                  0
% 1.82/1.01  res_forward_subsumption_resolution:     4
% 1.82/1.01  res_backward_subsumption_resolution:    0
% 1.82/1.01  res_clause_to_clause_subsumption:       148
% 1.82/1.01  res_orphan_elimination:                 0
% 1.82/1.01  res_tautology_del:                      47
% 1.82/1.01  res_num_eq_res_simplified:              2
% 1.82/1.01  res_num_sel_changes:                    0
% 1.82/1.01  res_moves_from_active_to_pass:          0
% 1.82/1.01  
% 1.82/1.01  ------ Superposition
% 1.82/1.01  
% 1.82/1.01  sup_time_total:                         0.
% 1.82/1.01  sup_time_generating:                    0.
% 1.82/1.01  sup_time_sim_full:                      0.
% 1.82/1.01  sup_time_sim_immed:                     0.
% 1.82/1.01  
% 1.82/1.01  sup_num_of_clauses:                     44
% 1.82/1.01  sup_num_in_active:                      34
% 1.82/1.01  sup_num_in_passive:                     10
% 1.82/1.01  sup_num_of_loops:                       34
% 1.82/1.01  sup_fw_superposition:                   8
% 1.82/1.01  sup_bw_superposition:                   6
% 1.82/1.01  sup_immediate_simplified:               0
% 1.82/1.01  sup_given_eliminated:                   0
% 1.82/1.01  comparisons_done:                       0
% 1.82/1.01  comparisons_avoided:                    0
% 1.82/1.01  
% 1.82/1.01  ------ Simplifications
% 1.82/1.01  
% 1.82/1.01  
% 1.82/1.01  sim_fw_subset_subsumed:                 0
% 1.82/1.01  sim_bw_subset_subsumed:                 0
% 1.82/1.01  sim_fw_subsumed:                        0
% 1.82/1.01  sim_bw_subsumed:                        0
% 1.82/1.01  sim_fw_subsumption_res:                 0
% 1.82/1.01  sim_bw_subsumption_res:                 0
% 1.82/1.01  sim_tautology_del:                      1
% 1.82/1.01  sim_eq_tautology_del:                   0
% 1.82/1.01  sim_eq_res_simp:                        0
% 1.82/1.01  sim_fw_demodulated:                     0
% 1.82/1.01  sim_bw_demodulated:                     0
% 1.82/1.01  sim_light_normalised:                   3
% 1.82/1.01  sim_joinable_taut:                      0
% 1.82/1.01  sim_joinable_simp:                      0
% 1.82/1.01  sim_ac_normalised:                      0
% 1.82/1.01  sim_smt_subsumption:                    0
% 1.82/1.01  
%------------------------------------------------------------------------------
