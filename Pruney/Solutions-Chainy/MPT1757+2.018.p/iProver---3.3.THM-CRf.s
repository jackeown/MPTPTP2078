%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:44 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  240 (1188 expanded)
%              Number of clauses        :  144 ( 209 expanded)
%              Number of leaves         :   26 ( 468 expanded)
%              Depth                    :   27
%              Number of atoms          : 1685 (18499 expanded)
%              Number of equality atoms :  144 (1322 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   38 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(nnf_transformation,[],[f40])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | ~ r1_tmap_1(X1,X0,X2,X4) )
          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | r1_tmap_1(X1,X0,X2,X4) )
          & X4 = X5
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8)
          | ~ r1_tmap_1(X1,X0,X2,X4) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8)
          | r1_tmap_1(X1,X0,X2,X4) )
        & sK8 = X4
        & m1_subset_1(sK8,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
              | ~ r1_tmap_1(X1,X0,X2,sK7) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | r1_tmap_1(X1,X0,X2,sK7) )
            & sK7 = X5
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_subset_1(sK7,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
                ( ( ~ r1_tmap_1(sK6,X0,k2_tmap_1(X1,X0,X2,sK6),X5)
                  | ~ r1_tmap_1(X1,X0,X2,X4) )
                & ( r1_tmap_1(sK6,X0,k2_tmap_1(X1,X0,X2,sK6),X5)
                  | r1_tmap_1(X1,X0,X2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(sK6)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_pre_topc(sK6,X1)
        & v1_tsep_1(sK6,X1)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
                    ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK5,X3),X5)
                      | ~ r1_tmap_1(X1,X0,sK5,X4) )
                    & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK5,X3),X5)
                      | r1_tmap_1(X1,X0,sK5,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_pre_topc(X3,X1)
            & v1_tsep_1(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK4,X0,X2,X3),X5)
                          | ~ r1_tmap_1(sK4,X0,X2,X4) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(sK4,X0,X2,X3),X5)
                          | r1_tmap_1(sK4,X0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(sK4)) )
                & m1_pre_topc(X3,sK4)
                & v1_tsep_1(X3,sK4)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK4)
        & v2_pre_topc(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
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
                          ( ( ~ r1_tmap_1(X3,sK3,k2_tmap_1(X1,sK3,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK3,X2,X4) )
                          & ( r1_tmap_1(X3,sK3,k2_tmap_1(X1,sK3,X2,X3),X5)
                            | r1_tmap_1(X1,sK3,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8)
      | ~ r1_tmap_1(sK4,sK3,sK5,sK7) )
    & ( r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8)
      | r1_tmap_1(sK4,sK3,sK5,sK7) )
    & sK7 = sK8
    & m1_subset_1(sK8,u1_struct_0(sK6))
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_pre_topc(sK6,sK4)
    & v1_tsep_1(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f52,f58,f57,f56,f55,f54,f53])).

fof(f92,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f59])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f102,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f88,plain,(
    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f59])).

fof(f87,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f22])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f84,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f85,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f86,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f90,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f59])).

fof(f82,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f81,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f83,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f103,plain,(
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
    inference(equality_resolution,[],[f79])).

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
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f101,plain,(
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
    inference(equality_resolution,[],[f78])).

fof(f97,plain,
    ( ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8)
    | ~ r1_tmap_1(sK4,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f59])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( r1_tarski(X3,X1)
                      & m1_connsp_2(X3,X0,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_tarski(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( r1_tarski(X5,X1)
                      & m1_connsp_2(X5,X0,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f43])).

fof(f46,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK2(X0,X1,X4),X1)
        & m1_connsp_2(sK2(X0,X1,X4),X0,X4)
        & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X1)
              | ~ m1_connsp_2(X3,X0,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,X1)
            | ~ m1_connsp_2(X3,X0,sK1(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,sK1(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ( r1_tarski(sK2(X0,X1,X4),X1)
                    & m1_connsp_2(sK2(X0,X1,X4),X0,X4)
                    & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f44,f46,f45])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( m1_connsp_2(sK2(X0,X1,X4),X0,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK2(X0,X1,X4),X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK0(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f41])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK0(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f96,plain,
    ( r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8)
    | r1_tmap_1(sK4,sK3,sK5,sK7) ),
    inference(cnf_transformation,[],[f59])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(nnf_transformation,[],[f33])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f91,plain,(
    v1_tsep_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f94,plain,(
    m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f59])).

fof(f93,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f102])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_680,plain,
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
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_681,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_680])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_685,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_681,c_31])).

cnf(c_686,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_685])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_727,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_686,c_4])).

cnf(c_946,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK4 != X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_727])).

cnf(c_947,plain,
    ( r1_tmap_1(sK4,X0,sK5,X1)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_946])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_951,plain,
    ( ~ v2_pre_topc(X0)
    | r1_tmap_1(sK4,X0,sK5,X1)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_947,c_34,c_33,c_32,c_28])).

cnf(c_952,plain,
    ( r1_tmap_1(sK4,X0,sK5,X1)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_951])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2492,plain,
    ( r1_tmap_1(sK4,X0,sK5,X1)
    | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_connsp_2(X2,sK4,X1)
    | ~ r1_tarski(X2,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_952,c_36])).

cnf(c_2493,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ m1_connsp_2(X1,sK4,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_2492])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2497,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ r1_tarski(X1,u1_struct_0(sK6))
    | ~ m1_connsp_2(X1,sK4,X0)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | r1_tmap_1(sK4,sK3,sK5,X0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2493,c_37,c_35,c_29])).

cnf(c_2498,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ m1_connsp_2(X1,sK4,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_2497])).

cnf(c_10763,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0_55)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
    | ~ m1_connsp_2(X1_55,sK4,X0_55)
    | ~ r1_tarski(X1_55,u1_struct_0(sK6))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4)))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_2498])).

cnf(c_11011,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0_55)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
    | ~ m1_connsp_2(X1_55,sK4,X0_55)
    | ~ r1_tarski(X1_55,u1_struct_0(sK6))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(equality_resolution_simp,[status(thm)],[c_10763])).

cnf(c_13659,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0_55)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
    | ~ m1_connsp_2(sK2(sK4,u1_struct_0(sK6),sK7),sK4,X0_55)
    | ~ r1_tarski(sK2(sK4,u1_struct_0(sK6),sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK4,u1_struct_0(sK6),sK7),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_11011])).

cnf(c_14493,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK7)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK7)
    | ~ m1_connsp_2(sK2(sK4,u1_struct_0(sK6),sK7),sK4,sK7)
    | ~ r1_tarski(sK2(sK4,u1_struct_0(sK6),sK7),u1_struct_0(sK6))
    | ~ m1_subset_1(sK2(sK4,u1_struct_0(sK6),sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_13659])).

cnf(c_20,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
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
    inference(cnf_transformation,[],[f103])).

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
    inference(cnf_transformation,[],[f101])).

cnf(c_200,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X4,X0)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
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

cnf(c_623,plain,
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
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_201,c_30])).

cnf(c_624,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_628,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_31])).

cnf(c_629,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_628])).

cnf(c_664,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_629,c_4])).

cnf(c_994,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK4)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK4 != X2
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_664])).

cnf(c_995,plain,
    ( ~ r1_tmap_1(sK4,X0,sK5,X1)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK4)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_994])).

cnf(c_999,plain,
    ( ~ v2_pre_topc(X0)
    | ~ r1_tmap_1(sK4,X0,sK5,X1)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_995,c_34,c_33,c_32,c_28])).

cnf(c_1000,plain,
    ( ~ r1_tmap_1(sK4,X0,sK5,X1)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_999])).

cnf(c_2468,plain,
    ( ~ r1_tmap_1(sK4,X0,sK5,X1)
    | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1000,c_36])).

cnf(c_2469,plain,
    ( ~ r1_tmap_1(sK4,sK3,sK5,X0)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_2468])).

cnf(c_2473,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK6))
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ r1_tmap_1(sK4,sK3,sK5,X0)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2469,c_37,c_35,c_29])).

cnf(c_2474,plain,
    ( ~ r1_tmap_1(sK4,sK3,sK5,X0)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_2473])).

cnf(c_10764,plain,
    ( ~ r1_tmap_1(sK4,sK3,sK5,X0_55)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_2474])).

cnf(c_11898,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tmap_1(sK4,sK3,sK5,X0_55) != iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10764])).

cnf(c_12091,plain,
    ( r1_tmap_1(sK4,sK3,sK5,X0_55) != iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11898])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK3,sK5,sK7)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_10778,negated_conjecture,
    ( ~ r1_tmap_1(sK4,sK3,sK5,sK7)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_11883,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK7) != iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10778])).

cnf(c_23,negated_conjecture,
    ( sK7 = sK8 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_10776,negated_conjecture,
    ( sK7 = sK8 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_11974,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK8) != iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11883,c_10776])).

cnf(c_14433,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK8) != iProver_top
    | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12091,c_11974])).

cnf(c_14434,plain,
    ( ~ r1_tmap_1(sK4,sK3,sK5,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14433])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_10779,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | ~ r2_hidden(X2_55,X0_55)
    | ~ v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_12560,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X1_55,X0_55)
    | ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_10779])).

cnf(c_12819,plain,
    ( ~ m1_subset_1(sK0(sK6,sK8),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0_55,sK0(sK6,sK8))
    | ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_12560])).

cnf(c_13145,plain,
    ( ~ m1_subset_1(sK0(sK6,sK8),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK8,sK0(sK6,sK8))
    | ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_12819])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_10780,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | r2_hidden(X0_55,X1_55)
    | v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_13032,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | r2_hidden(sK7,u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_10780])).

cnf(c_10793,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | m1_subset_1(X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55 ),
    theory(equality)).

cnf(c_12497,plain,
    ( m1_subset_1(X0_55,X1_55)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | X1_55 != u1_struct_0(sK6)
    | X0_55 != sK8 ),
    inference(instantiation,[status(thm)],[c_10793])).

cnf(c_12596,plain,
    ( m1_subset_1(sK7,X0_55)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | X0_55 != u1_struct_0(sK6)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_12497])).

cnf(c_12905,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | u1_struct_0(sK6) != u1_struct_0(sK6)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_12596])).

cnf(c_12,plain,
    ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2396,plain,
    ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_33])).

cnf(c_2397,plain,
    ( m1_connsp_2(sK2(sK4,X0,X1),sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_2396])).

cnf(c_2401,plain,
    ( m1_connsp_2(sK2(sK4,X0,X1),sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2397,c_34,c_32])).

cnf(c_10767,plain,
    ( m1_connsp_2(sK2(sK4,X0_55,X1_55),sK4,X1_55)
    | ~ v3_pre_topc(X0_55,sK4)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_2401])).

cnf(c_12403,plain,
    ( m1_connsp_2(sK2(sK4,u1_struct_0(sK6),X0_55),sK4,X0_55)
    | ~ v3_pre_topc(u1_struct_0(sK6),sK4)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0_55,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_10767])).

cnf(c_12835,plain,
    ( m1_connsp_2(sK2(sK4,u1_struct_0(sK6),sK7),sK4,sK7)
    | ~ v3_pre_topc(u1_struct_0(sK6),sK4)
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r2_hidden(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_12403])).

cnf(c_10790,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_12710,plain,
    ( k2_tmap_1(sK4,sK3,sK5,sK6) = k2_tmap_1(sK4,sK3,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_10790])).

cnf(c_10799,plain,
    ( ~ r1_tmap_1(X0_56,X1_56,X0_55,X1_55)
    | r1_tmap_1(X0_56,X1_56,X2_55,X3_55)
    | X2_55 != X0_55
    | X3_55 != X1_55 ),
    theory(equality)).

cnf(c_12517,plain,
    ( r1_tmap_1(sK6,sK3,X0_55,X1_55)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8)
    | X0_55 != k2_tmap_1(sK4,sK3,sK5,sK6)
    | X1_55 != sK8 ),
    inference(instantiation,[status(thm)],[c_10799])).

cnf(c_12630,plain,
    ( r1_tmap_1(sK6,sK3,X0_55,sK7)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8)
    | X0_55 != k2_tmap_1(sK4,sK3,sK5,sK6)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_12517])).

cnf(c_12709,plain,
    ( r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK7)
    | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8)
    | k2_tmap_1(sK4,sK3,sK5,sK6) != k2_tmap_1(sK4,sK3,sK5,sK6)
    | sK7 != sK8 ),
    inference(instantiation,[status(thm)],[c_12630])).

cnf(c_12668,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_10790])).

cnf(c_11,plain,
    ( r1_tarski(sK2(X0,X1,X2),X1)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2423,plain,
    ( r1_tarski(sK2(X0,X1,X2),X1)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_33])).

cnf(c_2424,plain,
    ( r1_tarski(sK2(sK4,X0,X1),X0)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_2423])).

cnf(c_2428,plain,
    ( r1_tarski(sK2(sK4,X0,X1),X0)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2424,c_34,c_32])).

cnf(c_10766,plain,
    ( r1_tarski(sK2(sK4,X0_55,X1_55),X0_55)
    | ~ v3_pre_topc(X0_55,sK4)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_2428])).

cnf(c_12398,plain,
    ( r1_tarski(sK2(sK4,u1_struct_0(sK6),X0_55),u1_struct_0(sK6))
    | ~ v3_pre_topc(u1_struct_0(sK6),sK4)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0_55,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_10766])).

cnf(c_12655,plain,
    ( r1_tarski(sK2(sK4,u1_struct_0(sK6),sK7),u1_struct_0(sK6))
    | ~ v3_pre_topc(u1_struct_0(sK6),sK4)
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r2_hidden(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_12398])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2753,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_33])).

cnf(c_2754,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_2753])).

cnf(c_2758,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2754,c_34,c_32])).

cnf(c_10753,plain,
    ( ~ v3_pre_topc(X0_55,sK4)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK2(sK4,X0_55,X1_55),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_2758])).

cnf(c_12385,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK6),sK4)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK4))
    | m1_subset_1(sK2(sK4,u1_struct_0(sK6),X0_55),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0_55,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_10753])).

cnf(c_12649,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK6),sK4)
    | m1_subset_1(sK2(sK4,u1_struct_0(sK6),sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ r2_hidden(sK7,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_12385])).

cnf(c_7,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_5])).

cnf(c_229,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_228])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_935,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK4 != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_26])).

cnf(c_936,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_935])).

cnf(c_938,plain,
    ( v2_pre_topc(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_936,c_33,c_32])).

cnf(c_3008,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_229,c_938])).

cnf(c_3009,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X1,X0)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_3008])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_924,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK4 != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_925,plain,
    ( ~ l1_pre_topc(sK4)
    | l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_924])).

cnf(c_3013,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3009,c_32,c_28,c_925])).

cnf(c_10742,plain,
    ( ~ m1_connsp_2(X0_55,sK6,X1_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
    | r2_hidden(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_3013])).

cnf(c_12423,plain,
    ( ~ m1_connsp_2(X0_55,sK6,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | r2_hidden(sK8,X0_55) ),
    inference(instantiation,[status(thm)],[c_10742])).

cnf(c_12593,plain,
    ( ~ m1_connsp_2(sK0(sK6,sK8),sK6,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | r2_hidden(sK8,sK0(sK6,sK8)) ),
    inference(instantiation,[status(thm)],[c_12423])).

cnf(c_3125,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_938])).

cnf(c_3126,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_3125])).

cnf(c_3130,plain,
    ( ~ m1_connsp_2(X0,sK6,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3126,c_32,c_28,c_925])).

cnf(c_10737,plain,
    ( ~ m1_connsp_2(X0_55,sK6,X1_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_3130])).

cnf(c_12414,plain,
    ( ~ m1_connsp_2(X0_55,sK6,sK8)
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_10737])).

cnf(c_12581,plain,
    ( ~ m1_connsp_2(sK0(sK6,sK8),sK6,sK8)
    | m1_subset_1(sK0(sK6,sK8),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_12414])).

cnf(c_6,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2714,plain,
    ( m1_connsp_2(sK0(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_938])).

cnf(c_2715,plain,
    ( m1_connsp_2(sK0(sK6,X0),sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_2714])).

cnf(c_2719,plain,
    ( m1_connsp_2(sK0(sK6,X0),sK6,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2715,c_32,c_28,c_925])).

cnf(c_10755,plain,
    ( m1_connsp_2(sK0(sK6,X0_55),sK6,X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK6)) ),
    inference(subtyping,[status(esa)],[c_2719])).

cnf(c_12408,plain,
    ( m1_connsp_2(sK0(sK6,sK8),sK6,sK8)
    | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_10755])).

cnf(c_22,negated_conjecture,
    ( r1_tmap_1(sK4,sK3,sK5,sK7)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_10777,negated_conjecture,
    ( r1_tmap_1(sK4,sK3,sK5,sK7)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_11884,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK7) = iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10777])).

cnf(c_11963,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK8) = iProver_top
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11884,c_10776])).

cnf(c_12264,plain,
    ( r1_tmap_1(sK4,sK3,sK5,sK8)
    | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11963])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_895,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK4 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_896,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_895])).

cnf(c_16,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f100])).

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
    ( v1_tsep_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_509,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_209,c_27])).

cnf(c_510,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f93])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14493,c_14434,c_13145,c_13032,c_12905,c_12835,c_12710,c_12709,c_12668,c_12655,c_12649,c_12593,c_12581,c_12408,c_12264,c_10776,c_896,c_510,c_21,c_24,c_25,c_26,c_32,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:42:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.02/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.02/0.99  
% 3.02/0.99  ------  iProver source info
% 3.02/0.99  
% 3.02/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.02/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.02/0.99  git: non_committed_changes: false
% 3.02/0.99  git: last_make_outside_of_git: false
% 3.02/0.99  
% 3.02/0.99  ------ 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options
% 3.02/0.99  
% 3.02/0.99  --out_options                           all
% 3.02/0.99  --tptp_safe_out                         true
% 3.02/0.99  --problem_path                          ""
% 3.02/0.99  --include_path                          ""
% 3.02/0.99  --clausifier                            res/vclausify_rel
% 3.02/0.99  --clausifier_options                    --mode clausify
% 3.02/0.99  --stdin                                 false
% 3.02/0.99  --stats_out                             all
% 3.02/0.99  
% 3.02/0.99  ------ General Options
% 3.02/0.99  
% 3.02/0.99  --fof                                   false
% 3.02/0.99  --time_out_real                         305.
% 3.02/0.99  --time_out_virtual                      -1.
% 3.02/0.99  --symbol_type_check                     false
% 3.02/0.99  --clausify_out                          false
% 3.02/0.99  --sig_cnt_out                           false
% 3.02/0.99  --trig_cnt_out                          false
% 3.02/0.99  --trig_cnt_out_tolerance                1.
% 3.02/0.99  --trig_cnt_out_sk_spl                   false
% 3.02/0.99  --abstr_cl_out                          false
% 3.02/0.99  
% 3.02/0.99  ------ Global Options
% 3.02/0.99  
% 3.02/0.99  --schedule                              default
% 3.02/0.99  --add_important_lit                     false
% 3.02/0.99  --prop_solver_per_cl                    1000
% 3.02/0.99  --min_unsat_core                        false
% 3.02/0.99  --soft_assumptions                      false
% 3.02/0.99  --soft_lemma_size                       3
% 3.02/0.99  --prop_impl_unit_size                   0
% 3.02/0.99  --prop_impl_unit                        []
% 3.02/0.99  --share_sel_clauses                     true
% 3.02/0.99  --reset_solvers                         false
% 3.02/0.99  --bc_imp_inh                            [conj_cone]
% 3.02/0.99  --conj_cone_tolerance                   3.
% 3.02/0.99  --extra_neg_conj                        none
% 3.02/0.99  --large_theory_mode                     true
% 3.02/0.99  --prolific_symb_bound                   200
% 3.02/0.99  --lt_threshold                          2000
% 3.02/0.99  --clause_weak_htbl                      true
% 3.02/0.99  --gc_record_bc_elim                     false
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing Options
% 3.02/0.99  
% 3.02/0.99  --preprocessing_flag                    true
% 3.02/0.99  --time_out_prep_mult                    0.1
% 3.02/0.99  --splitting_mode                        input
% 3.02/0.99  --splitting_grd                         true
% 3.02/0.99  --splitting_cvd                         false
% 3.02/0.99  --splitting_cvd_svl                     false
% 3.02/0.99  --splitting_nvd                         32
% 3.02/0.99  --sub_typing                            true
% 3.02/0.99  --prep_gs_sim                           true
% 3.02/0.99  --prep_unflatten                        true
% 3.02/0.99  --prep_res_sim                          true
% 3.02/0.99  --prep_upred                            true
% 3.02/0.99  --prep_sem_filter                       exhaustive
% 3.02/0.99  --prep_sem_filter_out                   false
% 3.02/0.99  --pred_elim                             true
% 3.02/0.99  --res_sim_input                         true
% 3.02/0.99  --eq_ax_congr_red                       true
% 3.02/0.99  --pure_diseq_elim                       true
% 3.02/0.99  --brand_transform                       false
% 3.02/0.99  --non_eq_to_eq                          false
% 3.02/0.99  --prep_def_merge                        true
% 3.02/0.99  --prep_def_merge_prop_impl              false
% 3.02/0.99  --prep_def_merge_mbd                    true
% 3.02/0.99  --prep_def_merge_tr_red                 false
% 3.02/0.99  --prep_def_merge_tr_cl                  false
% 3.02/0.99  --smt_preprocessing                     true
% 3.02/0.99  --smt_ac_axioms                         fast
% 3.02/0.99  --preprocessed_out                      false
% 3.02/0.99  --preprocessed_stats                    false
% 3.02/0.99  
% 3.02/0.99  ------ Abstraction refinement Options
% 3.02/0.99  
% 3.02/0.99  --abstr_ref                             []
% 3.02/0.99  --abstr_ref_prep                        false
% 3.02/0.99  --abstr_ref_until_sat                   false
% 3.02/0.99  --abstr_ref_sig_restrict                funpre
% 3.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.99  --abstr_ref_under                       []
% 3.02/0.99  
% 3.02/0.99  ------ SAT Options
% 3.02/0.99  
% 3.02/0.99  --sat_mode                              false
% 3.02/0.99  --sat_fm_restart_options                ""
% 3.02/0.99  --sat_gr_def                            false
% 3.02/0.99  --sat_epr_types                         true
% 3.02/0.99  --sat_non_cyclic_types                  false
% 3.02/0.99  --sat_finite_models                     false
% 3.02/0.99  --sat_fm_lemmas                         false
% 3.02/0.99  --sat_fm_prep                           false
% 3.02/0.99  --sat_fm_uc_incr                        true
% 3.02/0.99  --sat_out_model                         small
% 3.02/0.99  --sat_out_clauses                       false
% 3.02/0.99  
% 3.02/0.99  ------ QBF Options
% 3.02/0.99  
% 3.02/0.99  --qbf_mode                              false
% 3.02/0.99  --qbf_elim_univ                         false
% 3.02/0.99  --qbf_dom_inst                          none
% 3.02/0.99  --qbf_dom_pre_inst                      false
% 3.02/0.99  --qbf_sk_in                             false
% 3.02/0.99  --qbf_pred_elim                         true
% 3.02/0.99  --qbf_split                             512
% 3.02/0.99  
% 3.02/0.99  ------ BMC1 Options
% 3.02/0.99  
% 3.02/0.99  --bmc1_incremental                      false
% 3.02/0.99  --bmc1_axioms                           reachable_all
% 3.02/0.99  --bmc1_min_bound                        0
% 3.02/0.99  --bmc1_max_bound                        -1
% 3.02/0.99  --bmc1_max_bound_default                -1
% 3.02/0.99  --bmc1_symbol_reachability              true
% 3.02/0.99  --bmc1_property_lemmas                  false
% 3.02/0.99  --bmc1_k_induction                      false
% 3.02/0.99  --bmc1_non_equiv_states                 false
% 3.02/0.99  --bmc1_deadlock                         false
% 3.02/0.99  --bmc1_ucm                              false
% 3.02/0.99  --bmc1_add_unsat_core                   none
% 3.02/0.99  --bmc1_unsat_core_children              false
% 3.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.99  --bmc1_out_stat                         full
% 3.02/0.99  --bmc1_ground_init                      false
% 3.02/0.99  --bmc1_pre_inst_next_state              false
% 3.02/0.99  --bmc1_pre_inst_state                   false
% 3.02/0.99  --bmc1_pre_inst_reach_state             false
% 3.02/0.99  --bmc1_out_unsat_core                   false
% 3.02/0.99  --bmc1_aig_witness_out                  false
% 3.02/0.99  --bmc1_verbose                          false
% 3.02/0.99  --bmc1_dump_clauses_tptp                false
% 3.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.99  --bmc1_dump_file                        -
% 3.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.99  --bmc1_ucm_extend_mode                  1
% 3.02/0.99  --bmc1_ucm_init_mode                    2
% 3.02/0.99  --bmc1_ucm_cone_mode                    none
% 3.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.99  --bmc1_ucm_relax_model                  4
% 3.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.99  --bmc1_ucm_layered_model                none
% 3.02/0.99  --bmc1_ucm_max_lemma_size               10
% 3.02/0.99  
% 3.02/0.99  ------ AIG Options
% 3.02/0.99  
% 3.02/0.99  --aig_mode                              false
% 3.02/0.99  
% 3.02/0.99  ------ Instantiation Options
% 3.02/0.99  
% 3.02/0.99  --instantiation_flag                    true
% 3.02/0.99  --inst_sos_flag                         false
% 3.02/0.99  --inst_sos_phase                        true
% 3.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel_side                     num_symb
% 3.02/0.99  --inst_solver_per_active                1400
% 3.02/0.99  --inst_solver_calls_frac                1.
% 3.02/0.99  --inst_passive_queue_type               priority_queues
% 3.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.99  --inst_passive_queues_freq              [25;2]
% 3.02/0.99  --inst_dismatching                      true
% 3.02/0.99  --inst_eager_unprocessed_to_passive     true
% 3.02/0.99  --inst_prop_sim_given                   true
% 3.02/0.99  --inst_prop_sim_new                     false
% 3.02/0.99  --inst_subs_new                         false
% 3.02/0.99  --inst_eq_res_simp                      false
% 3.02/0.99  --inst_subs_given                       false
% 3.02/0.99  --inst_orphan_elimination               true
% 3.02/0.99  --inst_learning_loop_flag               true
% 3.02/0.99  --inst_learning_start                   3000
% 3.02/0.99  --inst_learning_factor                  2
% 3.02/0.99  --inst_start_prop_sim_after_learn       3
% 3.02/0.99  --inst_sel_renew                        solver
% 3.02/0.99  --inst_lit_activity_flag                true
% 3.02/0.99  --inst_restr_to_given                   false
% 3.02/0.99  --inst_activity_threshold               500
% 3.02/0.99  --inst_out_proof                        true
% 3.02/0.99  
% 3.02/0.99  ------ Resolution Options
% 3.02/0.99  
% 3.02/0.99  --resolution_flag                       true
% 3.02/0.99  --res_lit_sel                           adaptive
% 3.02/0.99  --res_lit_sel_side                      none
% 3.02/0.99  --res_ordering                          kbo
% 3.02/0.99  --res_to_prop_solver                    active
% 3.02/0.99  --res_prop_simpl_new                    false
% 3.02/0.99  --res_prop_simpl_given                  true
% 3.02/0.99  --res_passive_queue_type                priority_queues
% 3.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.99  --res_passive_queues_freq               [15;5]
% 3.02/0.99  --res_forward_subs                      full
% 3.02/0.99  --res_backward_subs                     full
% 3.02/0.99  --res_forward_subs_resolution           true
% 3.02/0.99  --res_backward_subs_resolution          true
% 3.02/0.99  --res_orphan_elimination                true
% 3.02/0.99  --res_time_limit                        2.
% 3.02/0.99  --res_out_proof                         true
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Options
% 3.02/0.99  
% 3.02/0.99  --superposition_flag                    true
% 3.02/0.99  --sup_passive_queue_type                priority_queues
% 3.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.99  --demod_completeness_check              fast
% 3.02/0.99  --demod_use_ground                      true
% 3.02/0.99  --sup_to_prop_solver                    passive
% 3.02/0.99  --sup_prop_simpl_new                    true
% 3.02/0.99  --sup_prop_simpl_given                  true
% 3.02/0.99  --sup_fun_splitting                     false
% 3.02/0.99  --sup_smt_interval                      50000
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Simplification Setup
% 3.02/0.99  
% 3.02/0.99  --sup_indices_passive                   []
% 3.02/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_full_bw                           [BwDemod]
% 3.02/0.99  --sup_immed_triv                        [TrivRules]
% 3.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_immed_bw_main                     []
% 3.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  
% 3.02/0.99  ------ Combination Options
% 3.02/0.99  
% 3.02/0.99  --comb_res_mult                         3
% 3.02/0.99  --comb_sup_mult                         2
% 3.02/0.99  --comb_inst_mult                        10
% 3.02/0.99  
% 3.02/0.99  ------ Debug Options
% 3.02/0.99  
% 3.02/0.99  --dbg_backtrace                         false
% 3.02/0.99  --dbg_dump_prop_clauses                 false
% 3.02/0.99  --dbg_dump_prop_clauses_file            -
% 3.02/0.99  --dbg_out_stat                          false
% 3.02/0.99  ------ Parsing...
% 3.02/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.02/0.99  ------ Proving...
% 3.02/0.99  ------ Problem Properties 
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  clauses                                 48
% 3.02/0.99  conjectures                             6
% 3.02/0.99  EPR                                     2
% 3.02/0.99  Horn                                    40
% 3.02/0.99  unary                                   6
% 3.02/0.99  binary                                  6
% 3.02/0.99  lits                                    165
% 3.02/0.99  lits eq                                 7
% 3.02/0.99  fd_pure                                 0
% 3.02/0.99  fd_pseudo                               0
% 3.02/0.99  fd_cond                                 0
% 3.02/0.99  fd_pseudo_cond                          0
% 3.02/0.99  AC symbols                              0
% 3.02/0.99  
% 3.02/0.99  ------ Schedule dynamic 5 is on 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  ------ 
% 3.02/0.99  Current options:
% 3.02/0.99  ------ 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options
% 3.02/0.99  
% 3.02/0.99  --out_options                           all
% 3.02/0.99  --tptp_safe_out                         true
% 3.02/0.99  --problem_path                          ""
% 3.02/0.99  --include_path                          ""
% 3.02/0.99  --clausifier                            res/vclausify_rel
% 3.02/0.99  --clausifier_options                    --mode clausify
% 3.02/0.99  --stdin                                 false
% 3.02/0.99  --stats_out                             all
% 3.02/0.99  
% 3.02/0.99  ------ General Options
% 3.02/0.99  
% 3.02/0.99  --fof                                   false
% 3.02/0.99  --time_out_real                         305.
% 3.02/0.99  --time_out_virtual                      -1.
% 3.02/0.99  --symbol_type_check                     false
% 3.02/0.99  --clausify_out                          false
% 3.02/0.99  --sig_cnt_out                           false
% 3.02/0.99  --trig_cnt_out                          false
% 3.02/0.99  --trig_cnt_out_tolerance                1.
% 3.02/0.99  --trig_cnt_out_sk_spl                   false
% 3.02/0.99  --abstr_cl_out                          false
% 3.02/0.99  
% 3.02/0.99  ------ Global Options
% 3.02/0.99  
% 3.02/0.99  --schedule                              default
% 3.02/0.99  --add_important_lit                     false
% 3.02/0.99  --prop_solver_per_cl                    1000
% 3.02/0.99  --min_unsat_core                        false
% 3.02/0.99  --soft_assumptions                      false
% 3.02/0.99  --soft_lemma_size                       3
% 3.02/0.99  --prop_impl_unit_size                   0
% 3.02/0.99  --prop_impl_unit                        []
% 3.02/0.99  --share_sel_clauses                     true
% 3.02/0.99  --reset_solvers                         false
% 3.02/0.99  --bc_imp_inh                            [conj_cone]
% 3.02/0.99  --conj_cone_tolerance                   3.
% 3.02/0.99  --extra_neg_conj                        none
% 3.02/0.99  --large_theory_mode                     true
% 3.02/0.99  --prolific_symb_bound                   200
% 3.02/0.99  --lt_threshold                          2000
% 3.02/0.99  --clause_weak_htbl                      true
% 3.02/0.99  --gc_record_bc_elim                     false
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing Options
% 3.02/0.99  
% 3.02/0.99  --preprocessing_flag                    true
% 3.02/0.99  --time_out_prep_mult                    0.1
% 3.02/0.99  --splitting_mode                        input
% 3.02/0.99  --splitting_grd                         true
% 3.02/0.99  --splitting_cvd                         false
% 3.02/0.99  --splitting_cvd_svl                     false
% 3.02/0.99  --splitting_nvd                         32
% 3.02/0.99  --sub_typing                            true
% 3.02/0.99  --prep_gs_sim                           true
% 3.02/0.99  --prep_unflatten                        true
% 3.02/0.99  --prep_res_sim                          true
% 3.02/0.99  --prep_upred                            true
% 3.02/0.99  --prep_sem_filter                       exhaustive
% 3.02/0.99  --prep_sem_filter_out                   false
% 3.02/0.99  --pred_elim                             true
% 3.02/0.99  --res_sim_input                         true
% 3.02/0.99  --eq_ax_congr_red                       true
% 3.02/0.99  --pure_diseq_elim                       true
% 3.02/0.99  --brand_transform                       false
% 3.02/0.99  --non_eq_to_eq                          false
% 3.02/0.99  --prep_def_merge                        true
% 3.02/0.99  --prep_def_merge_prop_impl              false
% 3.02/0.99  --prep_def_merge_mbd                    true
% 3.02/0.99  --prep_def_merge_tr_red                 false
% 3.02/0.99  --prep_def_merge_tr_cl                  false
% 3.02/0.99  --smt_preprocessing                     true
% 3.02/0.99  --smt_ac_axioms                         fast
% 3.02/0.99  --preprocessed_out                      false
% 3.02/0.99  --preprocessed_stats                    false
% 3.02/0.99  
% 3.02/0.99  ------ Abstraction refinement Options
% 3.02/0.99  
% 3.02/0.99  --abstr_ref                             []
% 3.02/0.99  --abstr_ref_prep                        false
% 3.02/0.99  --abstr_ref_until_sat                   false
% 3.02/0.99  --abstr_ref_sig_restrict                funpre
% 3.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.99  --abstr_ref_under                       []
% 3.02/0.99  
% 3.02/0.99  ------ SAT Options
% 3.02/0.99  
% 3.02/0.99  --sat_mode                              false
% 3.02/0.99  --sat_fm_restart_options                ""
% 3.02/0.99  --sat_gr_def                            false
% 3.02/0.99  --sat_epr_types                         true
% 3.02/0.99  --sat_non_cyclic_types                  false
% 3.02/0.99  --sat_finite_models                     false
% 3.02/0.99  --sat_fm_lemmas                         false
% 3.02/0.99  --sat_fm_prep                           false
% 3.02/0.99  --sat_fm_uc_incr                        true
% 3.02/0.99  --sat_out_model                         small
% 3.02/0.99  --sat_out_clauses                       false
% 3.02/0.99  
% 3.02/0.99  ------ QBF Options
% 3.02/0.99  
% 3.02/0.99  --qbf_mode                              false
% 3.02/0.99  --qbf_elim_univ                         false
% 3.02/0.99  --qbf_dom_inst                          none
% 3.02/0.99  --qbf_dom_pre_inst                      false
% 3.02/0.99  --qbf_sk_in                             false
% 3.02/0.99  --qbf_pred_elim                         true
% 3.02/0.99  --qbf_split                             512
% 3.02/0.99  
% 3.02/0.99  ------ BMC1 Options
% 3.02/0.99  
% 3.02/0.99  --bmc1_incremental                      false
% 3.02/0.99  --bmc1_axioms                           reachable_all
% 3.02/0.99  --bmc1_min_bound                        0
% 3.02/0.99  --bmc1_max_bound                        -1
% 3.02/0.99  --bmc1_max_bound_default                -1
% 3.02/0.99  --bmc1_symbol_reachability              true
% 3.02/0.99  --bmc1_property_lemmas                  false
% 3.02/0.99  --bmc1_k_induction                      false
% 3.02/0.99  --bmc1_non_equiv_states                 false
% 3.02/0.99  --bmc1_deadlock                         false
% 3.02/0.99  --bmc1_ucm                              false
% 3.02/0.99  --bmc1_add_unsat_core                   none
% 3.02/0.99  --bmc1_unsat_core_children              false
% 3.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.99  --bmc1_out_stat                         full
% 3.02/0.99  --bmc1_ground_init                      false
% 3.02/0.99  --bmc1_pre_inst_next_state              false
% 3.02/0.99  --bmc1_pre_inst_state                   false
% 3.02/0.99  --bmc1_pre_inst_reach_state             false
% 3.02/0.99  --bmc1_out_unsat_core                   false
% 3.02/0.99  --bmc1_aig_witness_out                  false
% 3.02/0.99  --bmc1_verbose                          false
% 3.02/0.99  --bmc1_dump_clauses_tptp                false
% 3.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.99  --bmc1_dump_file                        -
% 3.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.99  --bmc1_ucm_extend_mode                  1
% 3.02/0.99  --bmc1_ucm_init_mode                    2
% 3.02/0.99  --bmc1_ucm_cone_mode                    none
% 3.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.99  --bmc1_ucm_relax_model                  4
% 3.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.99  --bmc1_ucm_layered_model                none
% 3.02/0.99  --bmc1_ucm_max_lemma_size               10
% 3.02/0.99  
% 3.02/0.99  ------ AIG Options
% 3.02/0.99  
% 3.02/0.99  --aig_mode                              false
% 3.02/0.99  
% 3.02/0.99  ------ Instantiation Options
% 3.02/0.99  
% 3.02/0.99  --instantiation_flag                    true
% 3.02/0.99  --inst_sos_flag                         false
% 3.02/0.99  --inst_sos_phase                        true
% 3.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel_side                     none
% 3.02/0.99  --inst_solver_per_active                1400
% 3.02/0.99  --inst_solver_calls_frac                1.
% 3.02/0.99  --inst_passive_queue_type               priority_queues
% 3.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.99  --inst_passive_queues_freq              [25;2]
% 3.02/0.99  --inst_dismatching                      true
% 3.02/0.99  --inst_eager_unprocessed_to_passive     true
% 3.02/0.99  --inst_prop_sim_given                   true
% 3.02/0.99  --inst_prop_sim_new                     false
% 3.02/0.99  --inst_subs_new                         false
% 3.02/0.99  --inst_eq_res_simp                      false
% 3.02/0.99  --inst_subs_given                       false
% 3.02/0.99  --inst_orphan_elimination               true
% 3.02/0.99  --inst_learning_loop_flag               true
% 3.02/0.99  --inst_learning_start                   3000
% 3.02/0.99  --inst_learning_factor                  2
% 3.02/0.99  --inst_start_prop_sim_after_learn       3
% 3.02/0.99  --inst_sel_renew                        solver
% 3.02/0.99  --inst_lit_activity_flag                true
% 3.02/0.99  --inst_restr_to_given                   false
% 3.02/0.99  --inst_activity_threshold               500
% 3.02/0.99  --inst_out_proof                        true
% 3.02/0.99  
% 3.02/0.99  ------ Resolution Options
% 3.02/0.99  
% 3.02/0.99  --resolution_flag                       false
% 3.02/0.99  --res_lit_sel                           adaptive
% 3.02/0.99  --res_lit_sel_side                      none
% 3.02/0.99  --res_ordering                          kbo
% 3.02/0.99  --res_to_prop_solver                    active
% 3.02/0.99  --res_prop_simpl_new                    false
% 3.02/0.99  --res_prop_simpl_given                  true
% 3.02/0.99  --res_passive_queue_type                priority_queues
% 3.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.99  --res_passive_queues_freq               [15;5]
% 3.02/0.99  --res_forward_subs                      full
% 3.02/0.99  --res_backward_subs                     full
% 3.02/0.99  --res_forward_subs_resolution           true
% 3.02/0.99  --res_backward_subs_resolution          true
% 3.02/0.99  --res_orphan_elimination                true
% 3.02/0.99  --res_time_limit                        2.
% 3.02/0.99  --res_out_proof                         true
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Options
% 3.02/0.99  
% 3.02/0.99  --superposition_flag                    true
% 3.02/0.99  --sup_passive_queue_type                priority_queues
% 3.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.99  --demod_completeness_check              fast
% 3.02/0.99  --demod_use_ground                      true
% 3.02/0.99  --sup_to_prop_solver                    passive
% 3.02/0.99  --sup_prop_simpl_new                    true
% 3.02/0.99  --sup_prop_simpl_given                  true
% 3.02/0.99  --sup_fun_splitting                     false
% 3.02/0.99  --sup_smt_interval                      50000
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Simplification Setup
% 3.02/0.99  
% 3.02/0.99  --sup_indices_passive                   []
% 3.02/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_full_bw                           [BwDemod]
% 3.02/0.99  --sup_immed_triv                        [TrivRules]
% 3.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_immed_bw_main                     []
% 3.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  
% 3.02/0.99  ------ Combination Options
% 3.02/0.99  
% 3.02/0.99  --comb_res_mult                         3
% 3.02/0.99  --comb_sup_mult                         2
% 3.02/0.99  --comb_inst_mult                        10
% 3.02/0.99  
% 3.02/0.99  ------ Debug Options
% 3.02/0.99  
% 3.02/0.99  --dbg_backtrace                         false
% 3.02/0.99  --dbg_dump_prop_clauses                 false
% 3.02/0.99  --dbg_dump_prop_clauses_file            -
% 3.02/0.99  --dbg_out_stat                          false
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  ------ Proving...
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  % SZS status Theorem for theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  fof(f14,conjecture,(
% 3.02/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f15,negated_conjecture,(
% 3.02/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 3.02/0.99    inference(negated_conjecture,[],[f14])).
% 3.02/0.99  
% 3.02/0.99  fof(f39,plain,(
% 3.02/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f15])).
% 3.02/0.99  
% 3.02/0.99  fof(f40,plain,(
% 3.02/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.02/0.99    inference(flattening,[],[f39])).
% 3.02/0.99  
% 3.02/0.99  fof(f51,plain,(
% 3.02/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.02/0.99    inference(nnf_transformation,[],[f40])).
% 3.02/0.99  
% 3.02/0.99  fof(f52,plain,(
% 3.02/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.02/0.99    inference(flattening,[],[f51])).
% 3.02/0.99  
% 3.02/0.99  fof(f58,plain,(
% 3.02/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK8) | r1_tmap_1(X1,X0,X2,X4)) & sK8 = X4 & m1_subset_1(sK8,u1_struct_0(X3)))) )),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f57,plain,(
% 3.02/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK7)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK7)) & sK7 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK7,u1_struct_0(X1)))) )),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f56,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK6,X0,k2_tmap_1(X1,X0,X2,sK6),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK6,X0,k2_tmap_1(X1,X0,X2,sK6),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK6))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK6,X1) & v1_tsep_1(sK6,X1) & ~v2_struct_0(sK6))) )),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f55,plain,(
% 3.02/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK5,X3),X5) | ~r1_tmap_1(X1,X0,sK5,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK5,X3),X5) | r1_tmap_1(X1,X0,sK5,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK5))) )),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f54,plain,(
% 3.02/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK4,X0,X2,X3),X5) | ~r1_tmap_1(sK4,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK4,X0,X2,X3),X5) | r1_tmap_1(sK4,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK4))) & m1_pre_topc(X3,sK4) & v1_tsep_1(X3,sK4) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))) )),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f53,plain,(
% 3.02/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK3,k2_tmap_1(X1,sK3,X2,X3),X5) | ~r1_tmap_1(X1,sK3,X2,X4)) & (r1_tmap_1(X3,sK3,k2_tmap_1(X1,sK3,X2,X3),X5) | r1_tmap_1(X1,sK3,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f59,plain,(
% 3.02/0.99    ((((((~r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) | ~r1_tmap_1(sK4,sK3,sK5,sK7)) & (r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) | r1_tmap_1(sK4,sK3,sK5,sK7)) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK6))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_pre_topc(sK6,sK4) & v1_tsep_1(sK6,sK4) & ~v2_struct_0(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f52,f58,f57,f56,f55,f54,f53])).
% 3.02/0.99  
% 3.02/0.99  fof(f92,plain,(
% 3.02/0.99    m1_pre_topc(sK6,sK4)),
% 3.02/0.99    inference(cnf_transformation,[],[f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f13,axiom,(
% 3.02/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f37,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f13])).
% 3.02/0.99  
% 3.02/0.99  fof(f38,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/0.99    inference(flattening,[],[f37])).
% 3.02/0.99  
% 3.02/0.99  fof(f50,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/0.99    inference(nnf_transformation,[],[f38])).
% 3.02/0.99  
% 3.02/0.99  fof(f80,plain,(
% 3.02/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f50])).
% 3.02/0.99  
% 3.02/0.99  fof(f102,plain,(
% 3.02/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/0.99    inference(equality_resolution,[],[f80])).
% 3.02/0.99  
% 3.02/0.99  fof(f88,plain,(
% 3.02/0.99    v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3))),
% 3.02/0.99    inference(cnf_transformation,[],[f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f87,plain,(
% 3.02/0.99    v1_funct_1(sK5)),
% 3.02/0.99    inference(cnf_transformation,[],[f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f5,axiom,(
% 3.02/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f22,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f5])).
% 3.02/0.99  
% 3.02/0.99  fof(f23,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/0.99    inference(flattening,[],[f22])).
% 3.02/0.99  
% 3.02/0.99  fof(f64,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f23])).
% 3.02/0.99  
% 3.02/0.99  fof(f84,plain,(
% 3.02/0.99    ~v2_struct_0(sK4)),
% 3.02/0.99    inference(cnf_transformation,[],[f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f85,plain,(
% 3.02/0.99    v2_pre_topc(sK4)),
% 3.02/0.99    inference(cnf_transformation,[],[f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f86,plain,(
% 3.02/0.99    l1_pre_topc(sK4)),
% 3.02/0.99    inference(cnf_transformation,[],[f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f90,plain,(
% 3.02/0.99    ~v2_struct_0(sK6)),
% 3.02/0.99    inference(cnf_transformation,[],[f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f82,plain,(
% 3.02/0.99    v2_pre_topc(sK3)),
% 3.02/0.99    inference(cnf_transformation,[],[f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f81,plain,(
% 3.02/0.99    ~v2_struct_0(sK3)),
% 3.02/0.99    inference(cnf_transformation,[],[f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f83,plain,(
% 3.02/0.99    l1_pre_topc(sK3)),
% 3.02/0.99    inference(cnf_transformation,[],[f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f89,plain,(
% 3.02/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 3.02/0.99    inference(cnf_transformation,[],[f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f79,plain,(
% 3.02/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f50])).
% 3.02/0.99  
% 3.02/0.99  fof(f103,plain,(
% 3.02/0.99    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/0.99    inference(equality_resolution,[],[f79])).
% 3.02/0.99  
% 3.02/0.99  fof(f12,axiom,(
% 3.02/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f35,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f12])).
% 3.02/0.99  
% 3.02/0.99  fof(f36,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/0.99    inference(flattening,[],[f35])).
% 3.02/0.99  
% 3.02/0.99  fof(f78,plain,(
% 3.02/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f36])).
% 3.02/0.99  
% 3.02/0.99  fof(f101,plain,(
% 3.02/0.99    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/0.99    inference(equality_resolution,[],[f78])).
% 3.02/0.99  
% 3.02/0.99  fof(f97,plain,(
% 3.02/0.99    ~r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) | ~r1_tmap_1(sK4,sK3,sK5,sK7)),
% 3.02/0.99    inference(cnf_transformation,[],[f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f95,plain,(
% 3.02/0.99    sK7 = sK8),
% 3.02/0.99    inference(cnf_transformation,[],[f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f2,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f18,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.02/0.99    inference(ennf_transformation,[],[f2])).
% 3.02/0.99  
% 3.02/0.99  fof(f61,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f18])).
% 3.02/0.99  
% 3.02/0.99  fof(f1,axiom,(
% 3.02/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f16,plain,(
% 3.02/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.02/0.99    inference(ennf_transformation,[],[f1])).
% 3.02/0.99  
% 3.02/0.99  fof(f17,plain,(
% 3.02/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.02/0.99    inference(flattening,[],[f16])).
% 3.02/0.99  
% 3.02/0.99  fof(f60,plain,(
% 3.02/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f17])).
% 3.02/0.99  
% 3.02/0.99  fof(f9,axiom,(
% 3.02/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f30,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f9])).
% 3.02/0.99  
% 3.02/0.99  fof(f31,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/0.99    inference(flattening,[],[f30])).
% 3.02/0.99  
% 3.02/0.99  fof(f43,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/0.99    inference(nnf_transformation,[],[f31])).
% 3.02/0.99  
% 3.02/0.99  fof(f44,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/0.99    inference(rectify,[],[f43])).
% 3.02/0.99  
% 3.02/0.99  fof(f46,plain,(
% 3.02/0.99    ! [X4,X1,X0] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK2(X0,X1,X4),X1) & m1_connsp_2(sK2(X0,X1,X4),X0,X4) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f45,plain,(
% 3.02/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK1(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f47,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK1(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X4] : ((r1_tarski(sK2(X0,X1,X4),X1) & m1_connsp_2(sK2(X0,X1,X4),X0,X4) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f44,f46,f45])).
% 3.02/0.99  
% 3.02/0.99  fof(f69,plain,(
% 3.02/0.99    ( ! [X4,X0,X1] : (m1_connsp_2(sK2(X0,X1,X4),X0,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f47])).
% 3.02/0.99  
% 3.02/0.99  fof(f70,plain,(
% 3.02/0.99    ( ! [X4,X0,X1] : (r1_tarski(sK2(X0,X1,X4),X1) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f47])).
% 3.02/0.99  
% 3.02/0.99  fof(f68,plain,(
% 3.02/0.99    ( ! [X4,X0,X1] : (m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f47])).
% 3.02/0.99  
% 3.02/0.99  fof(f8,axiom,(
% 3.02/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f28,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f8])).
% 3.02/0.99  
% 3.02/0.99  fof(f29,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/0.99    inference(flattening,[],[f28])).
% 3.02/0.99  
% 3.02/0.99  fof(f67,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f29])).
% 3.02/0.99  
% 3.02/0.99  fof(f6,axiom,(
% 3.02/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f24,plain,(
% 3.02/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f6])).
% 3.02/0.99  
% 3.02/0.99  fof(f25,plain,(
% 3.02/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/0.99    inference(flattening,[],[f24])).
% 3.02/0.99  
% 3.02/0.99  fof(f65,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f25])).
% 3.02/0.99  
% 3.02/0.99  fof(f3,axiom,(
% 3.02/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f19,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f3])).
% 3.02/0.99  
% 3.02/0.99  fof(f20,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.02/0.99    inference(flattening,[],[f19])).
% 3.02/0.99  
% 3.02/0.99  fof(f62,plain,(
% 3.02/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f20])).
% 3.02/0.99  
% 3.02/0.99  fof(f4,axiom,(
% 3.02/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f21,plain,(
% 3.02/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.02/1.00    inference(ennf_transformation,[],[f4])).
% 3.02/1.00  
% 3.02/1.00  fof(f63,plain,(
% 3.02/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f21])).
% 3.02/1.00  
% 3.02/1.00  fof(f7,axiom,(
% 3.02/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f26,plain,(
% 3.02/1.00    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.02/1.00    inference(ennf_transformation,[],[f7])).
% 3.02/1.00  
% 3.02/1.00  fof(f27,plain,(
% 3.02/1.00    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.00    inference(flattening,[],[f26])).
% 3.02/1.00  
% 3.02/1.00  fof(f41,plain,(
% 3.02/1.00    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK0(X0,X1),X0,X1))),
% 3.02/1.00    introduced(choice_axiom,[])).
% 3.02/1.00  
% 3.02/1.00  fof(f42,plain,(
% 3.02/1.00    ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.02/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f41])).
% 3.02/1.00  
% 3.02/1.00  fof(f66,plain,(
% 3.02/1.00    ( ! [X0,X1] : (m1_connsp_2(sK0(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f42])).
% 3.02/1.00  
% 3.02/1.00  fof(f96,plain,(
% 3.02/1.00    r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) | r1_tmap_1(sK4,sK3,sK5,sK7)),
% 3.02/1.00    inference(cnf_transformation,[],[f59])).
% 3.02/1.00  
% 3.02/1.00  fof(f11,axiom,(
% 3.02/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f34,plain,(
% 3.02/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.02/1.00    inference(ennf_transformation,[],[f11])).
% 3.02/1.00  
% 3.02/1.00  fof(f77,plain,(
% 3.02/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f34])).
% 3.02/1.00  
% 3.02/1.00  fof(f10,axiom,(
% 3.02/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f32,plain,(
% 3.02/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.02/1.00    inference(ennf_transformation,[],[f10])).
% 3.02/1.00  
% 3.02/1.00  fof(f33,plain,(
% 3.02/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.02/1.00    inference(flattening,[],[f32])).
% 3.02/1.00  
% 3.02/1.00  fof(f48,plain,(
% 3.02/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.02/1.00    inference(nnf_transformation,[],[f33])).
% 3.02/1.00  
% 3.02/1.00  fof(f49,plain,(
% 3.02/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.02/1.00    inference(flattening,[],[f48])).
% 3.02/1.00  
% 3.02/1.00  fof(f74,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f49])).
% 3.02/1.00  
% 3.02/1.00  fof(f100,plain,(
% 3.02/1.00    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.02/1.00    inference(equality_resolution,[],[f74])).
% 3.02/1.00  
% 3.02/1.00  fof(f91,plain,(
% 3.02/1.00    v1_tsep_1(sK6,sK4)),
% 3.02/1.00    inference(cnf_transformation,[],[f59])).
% 3.02/1.00  
% 3.02/1.00  fof(f94,plain,(
% 3.02/1.00    m1_subset_1(sK8,u1_struct_0(sK6))),
% 3.02/1.00    inference(cnf_transformation,[],[f59])).
% 3.02/1.00  
% 3.02/1.00  fof(f93,plain,(
% 3.02/1.00    m1_subset_1(sK7,u1_struct_0(sK4))),
% 3.02/1.00    inference(cnf_transformation,[],[f59])).
% 3.02/1.00  
% 3.02/1.00  cnf(c_26,negated_conjecture,
% 3.02/1.00      ( m1_pre_topc(sK6,sK4) ),
% 3.02/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_19,plain,
% 3.02/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.02/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.02/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.02/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 3.02/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.02/1.00      | ~ m1_pre_topc(X4,X0)
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.02/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.00      | ~ v1_funct_1(X2)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | v2_struct_0(X4)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_30,negated_conjecture,
% 3.02/1.00      ( v1_funct_2(sK5,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 3.02/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_680,plain,
% 3.02/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.02/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.02/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 3.02/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.02/1.00      | ~ m1_pre_topc(X4,X0)
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.02/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.00      | ~ v1_funct_1(X2)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X4)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X0)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.02/1.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.02/1.00      | sK5 != X2 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_681,plain,
% 3.02/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.02/1.00      | r1_tmap_1(X2,X1,sK5,X3)
% 3.02/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 3.02/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_pre_topc(X0,X2)
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.02/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.02/1.00      | ~ v1_funct_1(sK5)
% 3.02/1.00      | v2_struct_0(X2)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X2)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X2)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.02/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_680]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_31,negated_conjecture,
% 3.02/1.00      ( v1_funct_1(sK5) ),
% 3.02/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_685,plain,
% 3.02/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.02/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_pre_topc(X0,X2)
% 3.02/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 3.02/1.00      | r1_tmap_1(X2,X1,sK5,X3)
% 3.02/1.00      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.02/1.00      | v2_struct_0(X2)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X2)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X2)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.02/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_681,c_31]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_686,plain,
% 3.02/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.02/1.00      | r1_tmap_1(X2,X1,sK5,X3)
% 3.02/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 3.02/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_pre_topc(X0,X2)
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.02/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X2)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ l1_pre_topc(X2)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X2)
% 3.02/1.00      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.02/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_685]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4,plain,
% 3.02/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.02/1.00      | m1_subset_1(X2,u1_struct_0(X1))
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X1) ),
% 3.02/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_727,plain,
% 3.02/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.02/1.00      | r1_tmap_1(X2,X1,sK5,X3)
% 3.02/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 3.02/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_pre_topc(X0,X2)
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X2)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ l1_pre_topc(X2)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X2)
% 3.02/1.00      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.02/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_686,c_4]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_946,plain,
% 3.02/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.02/1.00      | r1_tmap_1(X2,X1,sK5,X3)
% 3.02/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 3.02/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | v2_struct_0(X2)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | ~ l1_pre_topc(X2)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X2)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.02/1.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.02/1.00      | sK4 != X2
% 3.02/1.00      | sK6 != X0 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_727]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_947,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,X0,sK5,X1)
% 3.02/1.00      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 3.02/1.00      | ~ m1_connsp_2(X2,sK4,X1)
% 3.02/1.00      | ~ r1_tarski(X2,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | v2_struct_0(sK4)
% 3.02/1.00      | v2_struct_0(sK6)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | ~ l1_pre_topc(sK4)
% 3.02/1.00      | ~ v2_pre_topc(X0)
% 3.02/1.00      | ~ v2_pre_topc(sK4)
% 3.02/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.02/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_946]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_34,negated_conjecture,
% 3.02/1.00      ( ~ v2_struct_0(sK4) ),
% 3.02/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_33,negated_conjecture,
% 3.02/1.00      ( v2_pre_topc(sK4) ),
% 3.02/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_32,negated_conjecture,
% 3.02/1.00      ( l1_pre_topc(sK4) ),
% 3.02/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_28,negated_conjecture,
% 3.02/1.00      ( ~ v2_struct_0(sK6) ),
% 3.02/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_951,plain,
% 3.02/1.00      ( ~ v2_pre_topc(X0)
% 3.02/1.00      | r1_tmap_1(sK4,X0,sK5,X1)
% 3.02/1.00      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 3.02/1.00      | ~ m1_connsp_2(X2,sK4,X1)
% 3.02/1.00      | ~ r1_tarski(X2,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.02/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_947,c_34,c_33,c_32,c_28]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_952,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,X0,sK5,X1)
% 3.02/1.00      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 3.02/1.00      | ~ m1_connsp_2(X2,sK4,X1)
% 3.02/1.00      | ~ r1_tarski(X2,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | ~ v2_pre_topc(X0)
% 3.02/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.02/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_951]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_36,negated_conjecture,
% 3.02/1.00      ( v2_pre_topc(sK3) ),
% 3.02/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2492,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,X0,sK5,X1)
% 3.02/1.00      | ~ r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 3.02/1.00      | ~ m1_connsp_2(X2,sK4,X1)
% 3.02/1.00      | ~ r1_tarski(X2,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.02/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.02/1.00      | sK3 != X0 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_952,c_36]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2493,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,sK3,sK5,X0)
% 3.02/1.00      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 3.02/1.00      | ~ m1_connsp_2(X1,sK4,X0)
% 3.02/1.00      | ~ r1_tarski(X1,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.02/1.00      | v2_struct_0(sK3)
% 3.02/1.00      | ~ l1_pre_topc(sK3)
% 3.02/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_2492]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_37,negated_conjecture,
% 3.02/1.00      ( ~ v2_struct_0(sK3) ),
% 3.02/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_35,negated_conjecture,
% 3.02/1.00      ( l1_pre_topc(sK3) ),
% 3.02/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_29,negated_conjecture,
% 3.02/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 3.02/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2497,plain,
% 3.02/1.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.02/1.00      | ~ r1_tarski(X1,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_connsp_2(X1,sK4,X0)
% 3.02/1.00      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 3.02/1.00      | r1_tmap_1(sK4,sK3,sK5,X0)
% 3.02/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2493,c_37,c_35,c_29]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2498,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,sK3,sK5,X0)
% 3.02/1.00      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 3.02/1.00      | ~ m1_connsp_2(X1,sK4,X0)
% 3.02/1.00      | ~ r1_tarski(X1,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_2497]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10763,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,sK3,sK5,X0_55)
% 3.02/1.00      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
% 3.02/1.00      | ~ m1_connsp_2(X1_55,sK4,X0_55)
% 3.02/1.00      | ~ r1_tarski(X1_55,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_2498]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_11011,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,sK3,sK5,X0_55)
% 3.02/1.00      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
% 3.02/1.00      | ~ m1_connsp_2(X1_55,sK4,X0_55)
% 3.02/1.00      | ~ r1_tarski(X1_55,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_10763]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_13659,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,sK3,sK5,X0_55)
% 3.02/1.00      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
% 3.02/1.00      | ~ m1_connsp_2(sK2(sK4,u1_struct_0(sK6),sK7),sK4,X0_55)
% 3.02/1.00      | ~ r1_tarski(sK2(sK4,u1_struct_0(sK6),sK7),u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(sK2(sK4,u1_struct_0(sK6),sK7),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_11011]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_14493,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,sK3,sK5,sK7)
% 3.02/1.00      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK7)
% 3.02/1.00      | ~ m1_connsp_2(sK2(sK4,u1_struct_0(sK6),sK7),sK4,sK7)
% 3.02/1.00      | ~ r1_tarski(sK2(sK4,u1_struct_0(sK6),sK7),u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(sK2(sK4,u1_struct_0(sK6),sK7),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK6)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_13659]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_20,plain,
% 3.02/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.02/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.02/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.02/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 3.02/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.02/1.00      | ~ m1_pre_topc(X4,X0)
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.02/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.00      | ~ v1_funct_1(X2)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | v2_struct_0(X4)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_18,plain,
% 3.02/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.02/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.02/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.02/1.00      | ~ m1_pre_topc(X4,X0)
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.02/1.00      | ~ v1_funct_1(X2)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | v2_struct_0(X4)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_200,plain,
% 3.02/1.00      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.02/1.00      | ~ m1_pre_topc(X4,X0)
% 3.02/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.02/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.02/1.00      | ~ r1_tmap_1(X0,X1,X2,X3)
% 3.02/1.00      | ~ v1_funct_1(X2)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | v2_struct_0(X4)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X0) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_20,c_18]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_201,plain,
% 3.02/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.02/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.02/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.02/1.00      | ~ m1_pre_topc(X4,X0)
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.02/1.00      | ~ v1_funct_1(X2)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X4)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X0)
% 3.02/1.00      | ~ v2_pre_topc(X1) ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_200]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_623,plain,
% 3.02/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.02/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.02/1.00      | ~ m1_pre_topc(X4,X0)
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.02/1.00      | ~ v1_funct_1(X2)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X4)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X0)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.02/1.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.02/1.00      | sK5 != X2 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_201,c_30]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_624,plain,
% 3.02/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.02/1.00      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 3.02/1.00      | ~ m1_pre_topc(X0,X2)
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.02/1.00      | ~ v1_funct_1(sK5)
% 3.02/1.00      | v2_struct_0(X2)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X2)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X2)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.02/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_623]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_628,plain,
% 3.02/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_pre_topc(X0,X2)
% 3.02/1.00      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 3.02/1.00      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.02/1.00      | v2_struct_0(X2)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X2)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X2)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.02/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_624,c_31]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_629,plain,
% 3.02/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.02/1.00      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 3.02/1.00      | ~ m1_pre_topc(X0,X2)
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X2)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ l1_pre_topc(X2)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X2)
% 3.02/1.00      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.02/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_628]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_664,plain,
% 3.02/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.02/1.00      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 3.02/1.00      | ~ m1_pre_topc(X0,X2)
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | v2_struct_0(X2)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ l1_pre_topc(X2)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X2)
% 3.02/1.00      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.02/1.00      | u1_struct_0(X1) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_629,c_4]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_994,plain,
% 3.02/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK5,X0),X3)
% 3.02/1.00      | ~ r1_tmap_1(X2,X1,sK5,X3)
% 3.02/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | v2_struct_0(X2)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | ~ l1_pre_topc(X2)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X2)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | u1_struct_0(X2) != u1_struct_0(sK4)
% 3.02/1.00      | u1_struct_0(X1) != u1_struct_0(sK3)
% 3.02/1.00      | sK4 != X2
% 3.02/1.00      | sK6 != X0 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_664]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_995,plain,
% 3.02/1.00      ( ~ r1_tmap_1(sK4,X0,sK5,X1)
% 3.02/1.00      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | v2_struct_0(sK4)
% 3.02/1.00      | v2_struct_0(sK6)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | ~ l1_pre_topc(sK4)
% 3.02/1.00      | ~ v2_pre_topc(X0)
% 3.02/1.00      | ~ v2_pre_topc(sK4)
% 3.02/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.02/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_994]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_999,plain,
% 3.02/1.00      ( ~ v2_pre_topc(X0)
% 3.02/1.00      | ~ r1_tmap_1(sK4,X0,sK5,X1)
% 3.02/1.00      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.02/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_995,c_34,c_33,c_32,c_28]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1000,plain,
% 3.02/1.00      ( ~ r1_tmap_1(sK4,X0,sK5,X1)
% 3.02/1.00      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | ~ v2_pre_topc(X0)
% 3.02/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.02/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_999]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2468,plain,
% 3.02/1.00      ( ~ r1_tmap_1(sK4,X0,sK5,X1)
% 3.02/1.00      | r1_tmap_1(sK6,X0,k2_tmap_1(sK4,X0,sK5,sK6),X1)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | u1_struct_0(X0) != u1_struct_0(sK3)
% 3.02/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.02/1.00      | sK3 != X0 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_1000,c_36]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2469,plain,
% 3.02/1.00      ( ~ r1_tmap_1(sK4,sK3,sK5,X0)
% 3.02/1.00      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 3.02/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 3.02/1.00      | v2_struct_0(sK3)
% 3.02/1.00      | ~ l1_pre_topc(sK3)
% 3.02/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_2468]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2473,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.02/1.00      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 3.02/1.00      | ~ r1_tmap_1(sK4,sK3,sK5,X0)
% 3.02/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2469,c_37,c_35,c_29]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2474,plain,
% 3.02/1.00      ( ~ r1_tmap_1(sK4,sK3,sK5,X0)
% 3.02/1.00      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0)
% 3.02/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.02/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_2473]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10764,plain,
% 3.02/1.00      ( ~ r1_tmap_1(sK4,sK3,sK5,X0_55)
% 3.02/1.00      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55)
% 3.02/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK6))
% 3.02/1.00      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_2474]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_11898,plain,
% 3.02/1.00      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.02/1.00      | r1_tmap_1(sK4,sK3,sK5,X0_55) != iProver_top
% 3.02/1.00      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55) = iProver_top
% 3.02/1.00      | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_10764]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12091,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,sK3,sK5,X0_55) != iProver_top
% 3.02/1.00      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),X0_55) = iProver_top
% 3.02/1.00      | m1_subset_1(X0_55,u1_struct_0(sK6)) != iProver_top ),
% 3.02/1.00      inference(equality_resolution_simp,[status(thm)],[c_11898]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_21,negated_conjecture,
% 3.02/1.00      ( ~ r1_tmap_1(sK4,sK3,sK5,sK7)
% 3.02/1.00      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
% 3.02/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10778,negated_conjecture,
% 3.02/1.00      ( ~ r1_tmap_1(sK4,sK3,sK5,sK7)
% 3.02/1.00      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_11883,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,sK3,sK5,sK7) != iProver_top
% 3.02/1.00      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_10778]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_23,negated_conjecture,
% 3.02/1.00      ( sK7 = sK8 ),
% 3.02/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10776,negated_conjecture,
% 3.02/1.00      ( sK7 = sK8 ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_11974,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,sK3,sK5,sK8) != iProver_top
% 3.02/1.00      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) != iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_11883,c_10776]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_14433,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,sK3,sK5,sK8) != iProver_top
% 3.02/1.00      | m1_subset_1(sK8,u1_struct_0(sK6)) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_12091,c_11974]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_14434,plain,
% 3.02/1.00      ( ~ r1_tmap_1(sK4,sK3,sK5,sK8)
% 3.02/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
% 3.02/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_14433]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.02/1.00      | ~ r2_hidden(X2,X0)
% 3.02/1.00      | ~ v1_xboole_0(X1) ),
% 3.02/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10779,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 3.02/1.00      | ~ r2_hidden(X2_55,X0_55)
% 3.02/1.00      | ~ v1_xboole_0(X1_55) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12560,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.02/1.00      | ~ r2_hidden(X1_55,X0_55)
% 3.02/1.00      | ~ v1_xboole_0(u1_struct_0(sK6)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_10779]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12819,plain,
% 3.02/1.00      ( ~ m1_subset_1(sK0(sK6,sK8),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.02/1.00      | ~ r2_hidden(X0_55,sK0(sK6,sK8))
% 3.02/1.00      | ~ v1_xboole_0(u1_struct_0(sK6)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_12560]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_13145,plain,
% 3.02/1.00      ( ~ m1_subset_1(sK0(sK6,sK8),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.02/1.00      | ~ r2_hidden(sK8,sK0(sK6,sK8))
% 3.02/1.00      | ~ v1_xboole_0(u1_struct_0(sK6)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_12819]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_0,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.02/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10780,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0_55,X1_55)
% 3.02/1.00      | r2_hidden(X0_55,X1_55)
% 3.02/1.00      | v1_xboole_0(X1_55) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_13032,plain,
% 3.02/1.00      ( ~ m1_subset_1(sK7,u1_struct_0(sK6))
% 3.02/1.00      | r2_hidden(sK7,u1_struct_0(sK6))
% 3.02/1.00      | v1_xboole_0(u1_struct_0(sK6)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_10780]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10793,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0_55,X1_55)
% 3.02/1.00      | m1_subset_1(X2_55,X3_55)
% 3.02/1.00      | X2_55 != X0_55
% 3.02/1.00      | X3_55 != X1_55 ),
% 3.02/1.00      theory(equality) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12497,plain,
% 3.02/1.00      ( m1_subset_1(X0_55,X1_55)
% 3.02/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK6))
% 3.02/1.00      | X1_55 != u1_struct_0(sK6)
% 3.02/1.00      | X0_55 != sK8 ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_10793]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12596,plain,
% 3.02/1.00      ( m1_subset_1(sK7,X0_55)
% 3.02/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK6))
% 3.02/1.00      | X0_55 != u1_struct_0(sK6)
% 3.02/1.00      | sK7 != sK8 ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_12497]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12905,plain,
% 3.02/1.00      ( m1_subset_1(sK7,u1_struct_0(sK6))
% 3.02/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK6))
% 3.02/1.00      | u1_struct_0(sK6) != u1_struct_0(sK6)
% 3.02/1.00      | sK7 != sK8 ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_12596]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12,plain,
% 3.02/1.00      ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
% 3.02/1.00      | ~ v3_pre_topc(X1,X0)
% 3.02/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.00      | ~ r2_hidden(X2,X1)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | ~ v2_pre_topc(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2396,plain,
% 3.02/1.00      ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
% 3.02/1.00      | ~ v3_pre_topc(X1,X0)
% 3.02/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.00      | ~ r2_hidden(X2,X1)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | sK4 != X0 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_33]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2397,plain,
% 3.02/1.00      ( m1_connsp_2(sK2(sK4,X0,X1),sK4,X1)
% 3.02/1.00      | ~ v3_pre_topc(X0,sK4)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ r2_hidden(X1,X0)
% 3.02/1.00      | v2_struct_0(sK4)
% 3.02/1.00      | ~ l1_pre_topc(sK4) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_2396]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2401,plain,
% 3.02/1.00      ( m1_connsp_2(sK2(sK4,X0,X1),sK4,X1)
% 3.02/1.00      | ~ v3_pre_topc(X0,sK4)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ r2_hidden(X1,X0) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2397,c_34,c_32]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10767,plain,
% 3.02/1.00      ( m1_connsp_2(sK2(sK4,X0_55,X1_55),sK4,X1_55)
% 3.02/1.00      | ~ v3_pre_topc(X0_55,sK4)
% 3.02/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
% 3.02/1.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ r2_hidden(X1_55,X0_55) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_2401]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12403,plain,
% 3.02/1.00      ( m1_connsp_2(sK2(sK4,u1_struct_0(sK6),X0_55),sK4,X0_55)
% 3.02/1.00      | ~ v3_pre_topc(u1_struct_0(sK6),sK4)
% 3.02/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK4))
% 3.02/1.00      | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ r2_hidden(X0_55,u1_struct_0(sK6)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_10767]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12835,plain,
% 3.02/1.00      ( m1_connsp_2(sK2(sK4,u1_struct_0(sK6),sK7),sK4,sK7)
% 3.02/1.00      | ~ v3_pre_topc(u1_struct_0(sK6),sK4)
% 3.02/1.00      | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 3.02/1.00      | ~ r2_hidden(sK7,u1_struct_0(sK6)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_12403]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10790,plain,( X0_55 = X0_55 ),theory(equality) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12710,plain,
% 3.02/1.00      ( k2_tmap_1(sK4,sK3,sK5,sK6) = k2_tmap_1(sK4,sK3,sK5,sK6) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_10790]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10799,plain,
% 3.02/1.00      ( ~ r1_tmap_1(X0_56,X1_56,X0_55,X1_55)
% 3.02/1.00      | r1_tmap_1(X0_56,X1_56,X2_55,X3_55)
% 3.02/1.00      | X2_55 != X0_55
% 3.02/1.00      | X3_55 != X1_55 ),
% 3.02/1.00      theory(equality) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12517,plain,
% 3.02/1.00      ( r1_tmap_1(sK6,sK3,X0_55,X1_55)
% 3.02/1.00      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8)
% 3.02/1.00      | X0_55 != k2_tmap_1(sK4,sK3,sK5,sK6)
% 3.02/1.00      | X1_55 != sK8 ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_10799]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12630,plain,
% 3.02/1.00      ( r1_tmap_1(sK6,sK3,X0_55,sK7)
% 3.02/1.00      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8)
% 3.02/1.00      | X0_55 != k2_tmap_1(sK4,sK3,sK5,sK6)
% 3.02/1.00      | sK7 != sK8 ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_12517]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12709,plain,
% 3.02/1.00      ( r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK7)
% 3.02/1.00      | ~ r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8)
% 3.02/1.00      | k2_tmap_1(sK4,sK3,sK5,sK6) != k2_tmap_1(sK4,sK3,sK5,sK6)
% 3.02/1.00      | sK7 != sK8 ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_12630]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12668,plain,
% 3.02/1.00      ( u1_struct_0(sK6) = u1_struct_0(sK6) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_10790]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_11,plain,
% 3.02/1.00      ( r1_tarski(sK2(X0,X1,X2),X1)
% 3.02/1.00      | ~ v3_pre_topc(X1,X0)
% 3.02/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.00      | ~ r2_hidden(X2,X1)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | ~ v2_pre_topc(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2423,plain,
% 3.02/1.00      ( r1_tarski(sK2(X0,X1,X2),X1)
% 3.02/1.00      | ~ v3_pre_topc(X1,X0)
% 3.02/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.02/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/1.00      | ~ r2_hidden(X2,X1)
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | sK4 != X0 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_33]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2424,plain,
% 3.02/1.00      ( r1_tarski(sK2(sK4,X0,X1),X0)
% 3.02/1.00      | ~ v3_pre_topc(X0,sK4)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ r2_hidden(X1,X0)
% 3.02/1.00      | v2_struct_0(sK4)
% 3.02/1.00      | ~ l1_pre_topc(sK4) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_2423]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2428,plain,
% 3.02/1.00      ( r1_tarski(sK2(sK4,X0,X1),X0)
% 3.02/1.00      | ~ v3_pre_topc(X0,sK4)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ r2_hidden(X1,X0) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2424,c_34,c_32]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10766,plain,
% 3.02/1.00      ( r1_tarski(sK2(sK4,X0_55,X1_55),X0_55)
% 3.02/1.00      | ~ v3_pre_topc(X0_55,sK4)
% 3.02/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
% 3.02/1.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ r2_hidden(X1_55,X0_55) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_2428]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12398,plain,
% 3.02/1.00      ( r1_tarski(sK2(sK4,u1_struct_0(sK6),X0_55),u1_struct_0(sK6))
% 3.02/1.00      | ~ v3_pre_topc(u1_struct_0(sK6),sK4)
% 3.02/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK4))
% 3.02/1.00      | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ r2_hidden(X0_55,u1_struct_0(sK6)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_10766]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12655,plain,
% 3.02/1.00      ( r1_tarski(sK2(sK4,u1_struct_0(sK6),sK7),u1_struct_0(sK6))
% 3.02/1.00      | ~ v3_pre_topc(u1_struct_0(sK6),sK4)
% 3.02/1.00      | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 3.02/1.00      | ~ r2_hidden(sK7,u1_struct_0(sK6)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_12398]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_13,plain,
% 3.02/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.02/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.00      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.00      | ~ r2_hidden(X2,X0)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X1) ),
% 3.02/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2753,plain,
% 3.02/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.02/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.00      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.00      | ~ r2_hidden(X2,X0)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | sK4 != X1 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_33]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2754,plain,
% 3.02/1.00      ( ~ v3_pre_topc(X0,sK4)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ r2_hidden(X1,X0)
% 3.02/1.00      | v2_struct_0(sK4)
% 3.02/1.00      | ~ l1_pre_topc(sK4) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_2753]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2758,plain,
% 3.02/1.00      ( ~ v3_pre_topc(X0,sK4)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ r2_hidden(X1,X0) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2754,c_34,c_32]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10753,plain,
% 3.02/1.00      ( ~ v3_pre_topc(X0_55,sK4)
% 3.02/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK4))
% 3.02/1.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | m1_subset_1(sK2(sK4,X0_55,X1_55),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ r2_hidden(X1_55,X0_55) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_2758]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12385,plain,
% 3.02/1.00      ( ~ v3_pre_topc(u1_struct_0(sK6),sK4)
% 3.02/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK4))
% 3.02/1.00      | m1_subset_1(sK2(sK4,u1_struct_0(sK6),X0_55),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ r2_hidden(X0_55,u1_struct_0(sK6)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_10753]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12649,plain,
% 3.02/1.00      ( ~ v3_pre_topc(u1_struct_0(sK6),sK4)
% 3.02/1.00      | m1_subset_1(sK2(sK4,u1_struct_0(sK6),sK7),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 3.02/1.00      | ~ r2_hidden(sK7,u1_struct_0(sK6)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_12385]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_7,plain,
% 3.02/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.02/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.00      | r2_hidden(X2,X0)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X1) ),
% 3.02/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_5,plain,
% 3.02/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.02/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X1) ),
% 3.02/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_228,plain,
% 3.02/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.02/1.00      | ~ m1_connsp_2(X0,X1,X2)
% 3.02/1.00      | r2_hidden(X2,X0)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X1) ),
% 3.02/1.00      inference(global_propositional_subsumption,[status(thm)],[c_7,c_5]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_229,plain,
% 3.02/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.02/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.02/1.00      | r2_hidden(X2,X0)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X1) ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_228]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2,plain,
% 3.02/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | v2_pre_topc(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_935,plain,
% 3.02/1.00      ( ~ l1_pre_topc(X0)
% 3.02/1.00      | ~ v2_pre_topc(X0)
% 3.02/1.00      | v2_pre_topc(X1)
% 3.02/1.00      | sK4 != X0
% 3.02/1.00      | sK6 != X1 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_26]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_936,plain,
% 3.02/1.00      ( ~ l1_pre_topc(sK4) | ~ v2_pre_topc(sK4) | v2_pre_topc(sK6) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_935]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_938,plain,
% 3.02/1.00      ( v2_pre_topc(sK6) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_936,c_33,c_32]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3008,plain,
% 3.02/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.02/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.02/1.00      | r2_hidden(X2,X0)
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | sK6 != X1 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_229,c_938]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3009,plain,
% 3.02/1.00      ( ~ m1_connsp_2(X0,sK6,X1)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.02/1.00      | r2_hidden(X1,X0)
% 3.02/1.00      | v2_struct_0(sK6)
% 3.02/1.00      | ~ l1_pre_topc(sK6) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_3008]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3,plain,
% 3.02/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_924,plain,
% 3.02/1.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK4 != X0 | sK6 != X1 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_26]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_925,plain,
% 3.02/1.00      ( ~ l1_pre_topc(sK4) | l1_pre_topc(sK6) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_924]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3013,plain,
% 3.02/1.00      ( ~ m1_connsp_2(X0,sK6,X1)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.02/1.00      | r2_hidden(X1,X0) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_3009,c_32,c_28,c_925]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10742,plain,
% 3.02/1.00      ( ~ m1_connsp_2(X0_55,sK6,X1_55)
% 3.02/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
% 3.02/1.00      | r2_hidden(X1_55,X0_55) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_3013]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12423,plain,
% 3.02/1.00      ( ~ m1_connsp_2(X0_55,sK6,sK8)
% 3.02/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK6))
% 3.02/1.00      | r2_hidden(sK8,X0_55) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_10742]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12593,plain,
% 3.02/1.00      ( ~ m1_connsp_2(sK0(sK6,sK8),sK6,sK8)
% 3.02/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK6))
% 3.02/1.00      | r2_hidden(sK8,sK0(sK6,sK8)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_12423]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3125,plain,
% 3.02/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.02/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.00      | v2_struct_0(X1)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | sK6 != X1 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_938]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3126,plain,
% 3.02/1.00      ( ~ m1_connsp_2(X0,sK6,X1)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.02/1.00      | v2_struct_0(sK6)
% 3.02/1.00      | ~ l1_pre_topc(sK6) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_3125]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3130,plain,
% 3.02/1.00      ( ~ m1_connsp_2(X0,sK6,X1)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.02/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_3126,c_32,c_28,c_925]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10737,plain,
% 3.02/1.00      ( ~ m1_connsp_2(X0_55,sK6,X1_55)
% 3.02/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK6))
% 3.02/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_3130]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12414,plain,
% 3.02/1.00      ( ~ m1_connsp_2(X0_55,sK6,sK8)
% 3.02/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.02/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_10737]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12581,plain,
% 3.02/1.00      ( ~ m1_connsp_2(sK0(sK6,sK8),sK6,sK8)
% 3.02/1.00      | m1_subset_1(sK0(sK6,sK8),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.02/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_12414]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_6,plain,
% 3.02/1.00      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | ~ v2_pre_topc(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2714,plain,
% 3.02/1.00      ( m1_connsp_2(sK0(X0,X1),X0,X1)
% 3.02/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.02/1.00      | v2_struct_0(X0)
% 3.02/1.00      | ~ l1_pre_topc(X0)
% 3.02/1.00      | sK6 != X0 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_938]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2715,plain,
% 3.02/1.00      ( m1_connsp_2(sK0(sK6,X0),sK6,X0)
% 3.02/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.02/1.00      | v2_struct_0(sK6)
% 3.02/1.00      | ~ l1_pre_topc(sK6) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_2714]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2719,plain,
% 3.02/1.00      ( m1_connsp_2(sK0(sK6,X0),sK6,X0)
% 3.02/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK6)) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2715,c_32,c_28,c_925]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10755,plain,
% 3.02/1.00      ( m1_connsp_2(sK0(sK6,X0_55),sK6,X0_55)
% 3.02/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK6)) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_2719]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12408,plain,
% 3.02/1.00      ( m1_connsp_2(sK0(sK6,sK8),sK6,sK8)
% 3.02/1.00      | ~ m1_subset_1(sK8,u1_struct_0(sK6)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_10755]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_22,negated_conjecture,
% 3.02/1.00      ( r1_tmap_1(sK4,sK3,sK5,sK7)
% 3.02/1.00      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
% 3.02/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10777,negated_conjecture,
% 3.02/1.00      ( r1_tmap_1(sK4,sK3,sK5,sK7)
% 3.02/1.00      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_11884,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,sK3,sK5,sK7) = iProver_top
% 3.02/1.00      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_10777]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_11963,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,sK3,sK5,sK8) = iProver_top
% 3.02/1.00      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) = iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_11884,c_10776]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12264,plain,
% 3.02/1.00      ( r1_tmap_1(sK4,sK3,sK5,sK8)
% 3.02/1.00      | r1_tmap_1(sK6,sK3,k2_tmap_1(sK4,sK3,sK5,sK6),sK8) ),
% 3.02/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_11963]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_17,plain,
% 3.02/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.00      | ~ l1_pre_topc(X1) ),
% 3.02/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_895,plain,
% 3.02/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | sK4 != X1
% 3.02/1.00      | sK6 != X0 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_896,plain,
% 3.02/1.00      ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/1.00      | ~ l1_pre_topc(sK4) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_895]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_16,plain,
% 3.02/1.00      ( ~ v1_tsep_1(X0,X1)
% 3.02/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.02/1.00      | ~ m1_pre_topc(X0,X1)
% 3.02/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X1) ),
% 3.02/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_208,plain,
% 3.02/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.02/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.02/1.00      | ~ v1_tsep_1(X0,X1)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X1) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_16,c_17]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_209,plain,
% 3.02/1.00      ( ~ v1_tsep_1(X0,X1)
% 3.02/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.02/1.00      | ~ m1_pre_topc(X0,X1)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X1) ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_208]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_27,negated_conjecture,
% 3.02/1.00      ( v1_tsep_1(sK6,sK4) ),
% 3.02/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_509,plain,
% 3.02/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.02/1.00      | ~ m1_pre_topc(X0,X1)
% 3.02/1.00      | ~ l1_pre_topc(X1)
% 3.02/1.00      | ~ v2_pre_topc(X1)
% 3.02/1.00      | sK4 != X1
% 3.02/1.00      | sK6 != X0 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_209,c_27]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_510,plain,
% 3.02/1.00      ( v3_pre_topc(u1_struct_0(sK6),sK4)
% 3.02/1.00      | ~ m1_pre_topc(sK6,sK4)
% 3.02/1.00      | ~ l1_pre_topc(sK4)
% 3.02/1.00      | ~ v2_pre_topc(sK4) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_509]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_24,negated_conjecture,
% 3.02/1.00      ( m1_subset_1(sK8,u1_struct_0(sK6)) ),
% 3.02/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_25,negated_conjecture,
% 3.02/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 3.02/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(contradiction,plain,
% 3.02/1.00      ( $false ),
% 3.02/1.00      inference(minisat,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_14493,c_14434,c_13145,c_13032,c_12905,c_12835,c_12710,
% 3.02/1.00                 c_12709,c_12668,c_12655,c_12649,c_12593,c_12581,c_12408,
% 3.02/1.00                 c_12264,c_10776,c_896,c_510,c_21,c_24,c_25,c_26,c_32,
% 3.02/1.00                 c_33]) ).
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.02/1.00  
% 3.02/1.00  ------                               Statistics
% 3.02/1.00  
% 3.02/1.00  ------ General
% 3.02/1.00  
% 3.02/1.00  abstr_ref_over_cycles:                  0
% 3.02/1.00  abstr_ref_under_cycles:                 0
% 3.02/1.00  gc_basic_clause_elim:                   0
% 3.02/1.00  forced_gc_time:                         0
% 3.02/1.00  parsing_time:                           0.013
% 3.02/1.00  unif_index_cands_time:                  0.
% 3.02/1.00  unif_index_add_time:                    0.
% 3.02/1.00  orderings_time:                         0.
% 3.02/1.00  out_proof_time:                         0.017
% 3.02/1.00  total_time:                             0.323
% 3.02/1.00  num_of_symbols:                         64
% 3.02/1.00  num_of_terms:                           7045
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing
% 3.02/1.00  
% 3.02/1.00  num_of_splits:                          4
% 3.02/1.00  num_of_split_atoms:                     4
% 3.02/1.00  num_of_reused_defs:                     0
% 3.02/1.00  num_eq_ax_congr_red:                    28
% 3.02/1.00  num_of_sem_filtered_clauses:            1
% 3.02/1.00  num_of_subtypes:                        2
% 3.02/1.00  monotx_restored_types:                  0
% 3.02/1.00  sat_num_of_epr_types:                   0
% 3.02/1.00  sat_num_of_non_cyclic_types:            0
% 3.02/1.00  sat_guarded_non_collapsed_types:        0
% 3.02/1.00  num_pure_diseq_elim:                    0
% 3.02/1.00  simp_replaced_by:                       0
% 3.02/1.00  res_preprocessed:                       156
% 3.02/1.00  prep_upred:                             0
% 3.02/1.00  prep_unflattend:                        464
% 3.02/1.00  smt_new_axioms:                         0
% 3.02/1.00  pred_elim_cands:                        14
% 3.02/1.00  pred_elim:                              7
% 3.02/1.00  pred_elim_cl:                           -7
% 3.02/1.00  pred_elim_cycles:                       18
% 3.02/1.00  merged_defs:                            6
% 3.02/1.00  merged_defs_ncl:                        0
% 3.02/1.00  bin_hyper_res:                          6
% 3.02/1.00  prep_cycles:                            3
% 3.02/1.00  pred_elim_time:                         0.186
% 3.02/1.00  splitting_time:                         0.
% 3.02/1.00  sem_filter_time:                        0.
% 3.02/1.00  monotx_time:                            0.
% 3.02/1.00  subtype_inf_time:                       0.
% 3.02/1.00  
% 3.02/1.00  ------ Problem properties
% 3.02/1.00  
% 3.02/1.00  clauses:                                48
% 3.02/1.00  conjectures:                            6
% 3.02/1.00  epr:                                    2
% 3.02/1.00  horn:                                   40
% 3.02/1.00  ground:                                 12
% 3.02/1.00  unary:                                  6
% 3.02/1.00  binary:                                 6
% 3.02/1.00  lits:                                   165
% 3.02/1.00  lits_eq:                                7
% 3.02/1.00  fd_pure:                                0
% 3.02/1.00  fd_pseudo:                              0
% 3.02/1.00  fd_cond:                                0
% 3.02/1.00  fd_pseudo_cond:                         0
% 3.02/1.00  ac_symbols:                             0
% 3.02/1.00  
% 3.02/1.00  ------ Propositional Solver
% 3.02/1.00  
% 3.02/1.00  prop_solver_calls:                      22
% 3.02/1.00  prop_fast_solver_calls:                 3965
% 3.02/1.00  smt_solver_calls:                       0
% 3.02/1.00  smt_fast_solver_calls:                  0
% 3.02/1.00  prop_num_of_clauses:                    2912
% 3.02/1.00  prop_preprocess_simplified:             6994
% 3.02/1.00  prop_fo_subsumed:                       162
% 3.02/1.00  prop_solver_time:                       0.
% 3.02/1.00  smt_solver_time:                        0.
% 3.02/1.00  smt_fast_solver_time:                   0.
% 3.02/1.00  prop_fast_solver_time:                  0.
% 3.02/1.00  prop_unsat_core_time:                   0.
% 3.02/1.00  
% 3.02/1.00  ------ QBF
% 3.02/1.00  
% 3.02/1.00  qbf_q_res:                              0
% 3.02/1.00  qbf_num_tautologies:                    0
% 3.02/1.00  qbf_prep_cycles:                        0
% 3.02/1.00  
% 3.02/1.00  ------ BMC1
% 3.02/1.00  
% 3.02/1.00  bmc1_current_bound:                     -1
% 3.02/1.00  bmc1_last_solved_bound:                 -1
% 3.02/1.00  bmc1_unsat_core_size:                   -1
% 3.02/1.00  bmc1_unsat_core_parents_size:           -1
% 3.02/1.00  bmc1_merge_next_fun:                    0
% 3.02/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.02/1.00  
% 3.02/1.00  ------ Instantiation
% 3.02/1.00  
% 3.02/1.00  inst_num_of_clauses:                    396
% 3.02/1.00  inst_num_in_passive:                    53
% 3.02/1.00  inst_num_in_active:                     277
% 3.02/1.00  inst_num_in_unprocessed:                65
% 3.02/1.00  inst_num_of_loops:                      296
% 3.02/1.00  inst_num_of_learning_restarts:          0
% 3.02/1.00  inst_num_moves_active_passive:          14
% 3.02/1.00  inst_lit_activity:                      0
% 3.02/1.00  inst_lit_activity_moves:                0
% 3.02/1.00  inst_num_tautologies:                   0
% 3.02/1.00  inst_num_prop_implied:                  0
% 3.02/1.00  inst_num_existing_simplified:           0
% 3.02/1.00  inst_num_eq_res_simplified:             0
% 3.02/1.00  inst_num_child_elim:                    0
% 3.02/1.00  inst_num_of_dismatching_blockings:      9
% 3.02/1.00  inst_num_of_non_proper_insts:           366
% 3.02/1.00  inst_num_of_duplicates:                 0
% 3.02/1.00  inst_inst_num_from_inst_to_res:         0
% 3.02/1.00  inst_dismatching_checking_time:         0.
% 3.02/1.00  
% 3.02/1.00  ------ Resolution
% 3.02/1.00  
% 3.02/1.00  res_num_of_clauses:                     0
% 3.02/1.00  res_num_in_passive:                     0
% 3.02/1.00  res_num_in_active:                      0
% 3.02/1.00  res_num_of_loops:                       159
% 3.02/1.00  res_forward_subset_subsumed:            50
% 3.02/1.00  res_backward_subset_subsumed:           2
% 3.02/1.00  res_forward_subsumed:                   5
% 3.02/1.00  res_backward_subsumed:                  4
% 3.02/1.00  res_forward_subsumption_resolution:     26
% 3.02/1.00  res_backward_subsumption_resolution:    6
% 3.02/1.00  res_clause_to_clause_subsumption:       673
% 3.02/1.00  res_orphan_elimination:                 0
% 3.02/1.00  res_tautology_del:                      89
% 3.02/1.00  res_num_eq_res_simplified:              2
% 3.02/1.00  res_num_sel_changes:                    0
% 3.02/1.00  res_moves_from_active_to_pass:          0
% 3.02/1.00  
% 3.02/1.00  ------ Superposition
% 3.02/1.00  
% 3.02/1.00  sup_time_total:                         0.
% 3.02/1.00  sup_time_generating:                    0.
% 3.02/1.00  sup_time_sim_full:                      0.
% 3.02/1.00  sup_time_sim_immed:                     0.
% 3.02/1.00  
% 3.02/1.00  sup_num_of_clauses:                     81
% 3.02/1.00  sup_num_in_active:                      56
% 3.02/1.00  sup_num_in_passive:                     25
% 3.02/1.00  sup_num_of_loops:                       58
% 3.02/1.00  sup_fw_superposition:                   21
% 3.02/1.00  sup_bw_superposition:                   21
% 3.02/1.00  sup_immediate_simplified:               3
% 3.02/1.00  sup_given_eliminated:                   0
% 3.02/1.00  comparisons_done:                       0
% 3.02/1.00  comparisons_avoided:                    0
% 3.02/1.00  
% 3.02/1.00  ------ Simplifications
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  sim_fw_subset_subsumed:                 1
% 3.02/1.00  sim_bw_subset_subsumed:                 3
% 3.02/1.00  sim_fw_subsumed:                        2
% 3.02/1.00  sim_bw_subsumed:                        0
% 3.02/1.00  sim_fw_subsumption_res:                 0
% 3.02/1.00  sim_bw_subsumption_res:                 0
% 3.02/1.00  sim_tautology_del:                      1
% 3.02/1.00  sim_eq_tautology_del:                   0
% 3.02/1.00  sim_eq_res_simp:                        2
% 3.02/1.00  sim_fw_demodulated:                     0
% 3.02/1.00  sim_bw_demodulated:                     0
% 3.02/1.00  sim_light_normalised:                   3
% 3.02/1.00  sim_joinable_taut:                      0
% 3.02/1.00  sim_joinable_simp:                      0
% 3.02/1.00  sim_ac_normalised:                      0
% 3.02/1.00  sim_smt_subsumption:                    0
% 3.02/1.00  
%------------------------------------------------------------------------------
