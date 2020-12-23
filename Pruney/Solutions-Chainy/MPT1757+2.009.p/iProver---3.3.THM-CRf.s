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
% DateTime   : Thu Dec  3 12:22:42 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  236 (1168 expanded)
%              Number of clauses        :  137 ( 200 expanded)
%              Number of leaves         :   24 ( 458 expanded)
%              Depth                    :   27
%              Number of atoms          : 1668 (18210 expanded)
%              Number of equality atoms :  127 (1285 expanded)
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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(nnf_transformation,[],[f38])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | ~ r1_tmap_1(X1,X0,X2,X4) )
          & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
            | r1_tmap_1(X1,X0,X2,X4) )
          & X4 = X5
          & m1_subset_1(X5,u1_struct_0(X3)) )
     => ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK9)
          | ~ r1_tmap_1(X1,X0,X2,X4) )
        & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK9)
          | r1_tmap_1(X1,X0,X2,X4) )
        & sK9 = X4
        & m1_subset_1(sK9,u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
              | ~ r1_tmap_1(X1,X0,X2,sK8) )
            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
              | r1_tmap_1(X1,X0,X2,sK8) )
            & sK8 = X5
            & m1_subset_1(X5,u1_struct_0(X3)) )
        & m1_subset_1(sK8,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
                ( ( ~ r1_tmap_1(sK7,X0,k2_tmap_1(X1,X0,X2,sK7),X5)
                  | ~ r1_tmap_1(X1,X0,X2,X4) )
                & ( r1_tmap_1(sK7,X0,k2_tmap_1(X1,X0,X2,sK7),X5)
                  | r1_tmap_1(X1,X0,X2,X4) )
                & X4 = X5
                & m1_subset_1(X5,u1_struct_0(sK7)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_pre_topc(sK7,X1)
        & v1_tsep_1(sK7,X1)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
                    ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK6,X3),X5)
                      | ~ r1_tmap_1(X1,X0,sK6,X4) )
                    & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK6,X3),X5)
                      | r1_tmap_1(X1,X0,sK6,X4) )
                    & X4 = X5
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_pre_topc(X3,X1)
            & v1_tsep_1(X3,X1)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK6,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
                        ( ( ~ r1_tmap_1(X3,X0,k2_tmap_1(sK5,X0,X2,X3),X5)
                          | ~ r1_tmap_1(sK5,X0,X2,X4) )
                        & ( r1_tmap_1(X3,X0,k2_tmap_1(sK5,X0,X2,X3),X5)
                          | r1_tmap_1(sK5,X0,X2,X4) )
                        & X4 = X5
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_subset_1(X4,u1_struct_0(sK5)) )
                & m1_pre_topc(X3,sK5)
                & v1_tsep_1(X3,sK5)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK5)
        & v2_pre_topc(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
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
                          ( ( ~ r1_tmap_1(X3,sK4,k2_tmap_1(X1,sK4,X2,X3),X5)
                            | ~ r1_tmap_1(X1,sK4,X2,X4) )
                          & ( r1_tmap_1(X3,sK4,k2_tmap_1(X1,sK4,X2,X3),X5)
                            | r1_tmap_1(X1,sK4,X2,X4) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK4))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ( ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
      | ~ r1_tmap_1(sK5,sK4,sK6,sK8) )
    & ( r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
      | r1_tmap_1(sK5,sK4,sK6,sK8) )
    & sK8 = sK9
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & m1_subset_1(sK8,u1_struct_0(sK5))
    & m1_pre_topc(sK7,sK5)
    & v1_tsep_1(sK7,sK5)
    & ~ v2_struct_0(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))
    & v1_funct_1(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f55,f61,f60,f59,f58,f57,f56])).

fof(f98,plain,(
    m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f62])).

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
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f108,plain,(
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
    inference(equality_resolution,[],[f86])).

fof(f94,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f62])).

fof(f93,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f62])).

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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f90,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f91,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f92,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f96,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f88,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f87,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f89,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f95,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f62])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f109,plain,(
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
    inference(equality_resolution,[],[f85])).

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
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f107,plain,(
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
    inference(equality_resolution,[],[f84])).

fof(f103,plain,
    ( ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
    | ~ r1_tmap_1(sK5,sK4,sK6,sK8) ),
    inference(cnf_transformation,[],[f62])).

fof(f101,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f62])).

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

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f49,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(X5,X1)
          & m1_connsp_2(X5,X0,X4)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_tarski(sK3(X0,X1,X4),X1)
        & m1_connsp_2(sK3(X0,X1,X4),X0,X4)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
            | ~ m1_connsp_2(X3,X0,sK2(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ( ! [X3] :
                    ( ~ r1_tarski(X3,X1)
                    | ~ m1_connsp_2(X3,X0,sK2(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ( r1_tarski(sK3(X0,X1,X4),X1)
                    & m1_connsp_2(sK3(X0,X1,X4),X0,X4)
                    & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f47,f49,f48])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( m1_connsp_2(sK3(X0,X1,X4),X0,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK3(X0,X1,X4),X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
     => m1_connsp_2(sK1(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK1(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f44])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK1(X0,X1),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f99,plain,(
    m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f62])).

fof(f102,plain,
    ( r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
    | r1_tmap_1(sK5,sK4,sK6,sK8) ),
    inference(cnf_transformation,[],[f62])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f97,plain,(
    v1_tsep_1(sK7,sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f100,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK7,sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_22,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_605,plain,
    ( r1_tmap_1(X0,X1,X2,X3)
    | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_606,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
    | r1_tmap_1(X2,X1,sK6,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_610,plain,
    ( ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK6,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_606,c_34])).

cnf(c_611,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
    | r1_tmap_1(X2,X1,sK6,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_610])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_652,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
    | r1_tmap_1(X2,X1,sK6,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_611,c_7])).

cnf(c_773,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
    | r1_tmap_1(X2,X1,sK6,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | sK5 != X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_652])).

cnf(c_774,plain,
    ( r1_tmap_1(sK5,X0,sK6,X1)
    | ~ r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
    | ~ m1_connsp_2(X2,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_773])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_778,plain,
    ( ~ v2_pre_topc(X0)
    | r1_tmap_1(sK5,X0,sK6,X1)
    | ~ r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
    | ~ m1_connsp_2(X2,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_774,c_37,c_36,c_35,c_31])).

cnf(c_779,plain,
    ( r1_tmap_1(sK5,X0,sK6,X1)
    | ~ r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
    | ~ m1_connsp_2(X2,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(renaming,[status(thm)],[c_778])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2219,plain,
    ( r1_tmap_1(sK5,X0,sK6,X1)
    | ~ r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
    | ~ m1_connsp_2(X2,sK5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | ~ r1_tarski(X2,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_779,c_39])).

cnf(c_2220,plain,
    ( r1_tmap_1(sK5,sK4,sK6,X0)
    | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0)
    | ~ m1_connsp_2(X1,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | ~ r1_tarski(X1,u1_struct_0(sK7))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_2219])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2224,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_connsp_2(X1,sK5,X0)
    | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0)
    | r1_tmap_1(sK5,sK4,sK6,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK7))
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2220,c_40,c_38,c_32])).

cnf(c_2225,plain,
    ( r1_tmap_1(sK5,sK4,sK6,X0)
    | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0)
    | ~ m1_connsp_2(X1,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X1,u1_struct_0(sK7))
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_2224])).

cnf(c_9543,plain,
    ( r1_tmap_1(sK5,sK4,sK6,X0_55)
    | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0_55)
    | ~ m1_connsp_2(X1_55,sK5,X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X1_55,u1_struct_0(sK7))
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_2225])).

cnf(c_9805,plain,
    ( r1_tmap_1(sK5,sK4,sK6,X0_55)
    | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0_55)
    | ~ m1_connsp_2(X1_55,sK5,X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X1_55,u1_struct_0(sK7)) ),
    inference(equality_resolution_simp,[status(thm)],[c_9543])).

cnf(c_11299,plain,
    ( r1_tmap_1(sK5,sK4,sK6,sK9)
    | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
    | ~ m1_connsp_2(X0_55,sK5,sK9)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ r1_tarski(X0_55,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_9805])).

cnf(c_13496,plain,
    ( r1_tmap_1(sK5,sK4,sK6,sK9)
    | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
    | ~ m1_connsp_2(sK3(sK5,u1_struct_0(sK7),sK9),sK5,sK9)
    | ~ m1_subset_1(sK3(sK5,u1_struct_0(sK7),sK9),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ r1_tarski(sK3(sK5,u1_struct_0(sK7),sK9),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_11299])).

cnf(c_23,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_connsp_2(X5,X0,X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X5,u1_struct_0(X4))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f107])).

cnf(c_216,plain,
    ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ r1_tmap_1(X0,X1,X2,X3)
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
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_21])).

cnf(c_217,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_216])).

cnf(c_548,plain,
    ( ~ r1_tmap_1(X0,X1,X2,X3)
    | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
    | ~ m1_pre_topc(X4,X0)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v1_funct_1(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X0) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_217,c_33])).

cnf(c_549,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK6,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK6)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_553,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK6,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_34])).

cnf(c_554,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK6,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_553])).

cnf(c_589,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK6,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_554,c_7])).

cnf(c_821,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK6,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK5)
    | u1_struct_0(X1) != u1_struct_0(sK4)
    | sK5 != X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_589])).

cnf(c_822,plain,
    ( ~ r1_tmap_1(sK5,X0,sK6,X1)
    | r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK5)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(unflattening,[status(thm)],[c_821])).

cnf(c_826,plain,
    ( ~ v2_pre_topc(X0)
    | ~ r1_tmap_1(sK5,X0,sK6,X1)
    | r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_822,c_37,c_36,c_35,c_31])).

cnf(c_827,plain,
    ( ~ r1_tmap_1(sK5,X0,sK6,X1)
    | r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(renaming,[status(thm)],[c_826])).

cnf(c_2195,plain,
    ( ~ r1_tmap_1(sK5,X0,sK6,X1)
    | r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK5)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_827,c_39])).

cnf(c_2196,plain,
    ( ~ r1_tmap_1(sK5,sK4,sK6,X0)
    | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_2195])).

cnf(c_2200,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0)
    | ~ r1_tmap_1(sK5,sK4,sK6,X0)
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2196,c_40,c_38,c_32])).

cnf(c_2201,plain,
    ( ~ r1_tmap_1(sK5,sK4,sK6,X0)
    | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(renaming,[status(thm)],[c_2200])).

cnf(c_9544,plain,
    ( ~ r1_tmap_1(sK5,sK4,sK6,X0_55)
    | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
    | u1_struct_0(sK4) != u1_struct_0(sK4) ),
    inference(subtyping,[status(esa)],[c_2201])).

cnf(c_10752,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | r1_tmap_1(sK5,sK4,sK6,X0_55) != iProver_top
    | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0_55) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9544])).

cnf(c_10956,plain,
    ( r1_tmap_1(sK5,sK4,sK6,X0_55) != iProver_top
    | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0_55) = iProver_top
    | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10752])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tmap_1(sK5,sK4,sK6,sK8)
    | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_9557,negated_conjecture,
    ( ~ r1_tmap_1(sK5,sK4,sK6,sK8)
    | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_10738,plain,
    ( r1_tmap_1(sK5,sK4,sK6,sK8) != iProver_top
    | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9557])).

cnf(c_26,negated_conjecture,
    ( sK8 = sK9 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_9555,negated_conjecture,
    ( sK8 = sK9 ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_10839,plain,
    ( r1_tmap_1(sK5,sK4,sK6,sK9) != iProver_top
    | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10738,c_9555])).

cnf(c_13354,plain,
    ( r1_tmap_1(sK5,sK4,sK6,sK9) != iProver_top
    | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10956,c_10839])).

cnf(c_13355,plain,
    ( ~ r1_tmap_1(sK5,sK4,sK6,sK9)
    | ~ m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13354])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_9558,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | r1_tarski(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_11542,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK7)))
    | r1_tarski(X0_55,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_9558])).

cnf(c_12983,plain,
    ( ~ m1_subset_1(sK1(sK7,sK9),k1_zfmisc_1(u1_struct_0(sK7)))
    | r1_tarski(sK1(sK7,sK9),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_11542])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_9560,plain,
    ( ~ r2_hidden(X0_55,X1_55)
    | r2_hidden(X0_55,X2_55)
    | ~ r1_tarski(X1_55,X2_55) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_11666,plain,
    ( r2_hidden(sK9,X0_55)
    | ~ r2_hidden(sK9,sK1(sK7,sK9))
    | ~ r1_tarski(sK1(sK7,sK9),X0_55) ),
    inference(instantiation,[status(thm)],[c_9560])).

cnf(c_12213,plain,
    ( ~ r2_hidden(sK9,sK1(sK7,sK9))
    | r2_hidden(sK9,u1_struct_0(sK7))
    | ~ r1_tarski(sK1(sK7,sK9),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_11666])).

cnf(c_15,plain,
    ( m1_connsp_2(sK3(X0,X1,X2),X0,X2)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2150,plain,
    ( m1_connsp_2(sK3(X0,X1,X2),X0,X2)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_36])).

cnf(c_2151,plain,
    ( m1_connsp_2(sK3(sK5,X0,X1),sK5,X1)
    | ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_2150])).

cnf(c_2155,plain,
    ( m1_connsp_2(sK3(sK5,X0,X1),sK5,X1)
    | ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2151,c_37,c_35])).

cnf(c_9546,plain,
    ( m1_connsp_2(sK3(sK5,X0_55,X1_55),sK5,X1_55)
    | ~ v3_pre_topc(X0_55,sK5)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK5))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_2155])).

cnf(c_11274,plain,
    ( m1_connsp_2(sK3(sK5,u1_struct_0(sK7),X0_55),sK5,X0_55)
    | ~ v3_pre_topc(u1_struct_0(sK7),sK5)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0_55,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_9546])).

cnf(c_11734,plain,
    ( m1_connsp_2(sK3(sK5,u1_struct_0(sK7),sK9),sK5,sK9)
    | ~ v3_pre_topc(u1_struct_0(sK7),sK5)
    | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK5))
    | ~ r2_hidden(sK9,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_11274])).

cnf(c_14,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r1_tarski(sK3(X1,X0,X2),X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2453,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r1_tarski(sK3(X1,X0,X2),X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_36])).

cnf(c_2454,plain,
    ( ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X0)
    | r1_tarski(sK3(sK5,X0,X1),X0)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_2453])).

cnf(c_2458,plain,
    ( ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X0)
    | r1_tarski(sK3(sK5,X0,X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2454,c_37,c_35])).

cnf(c_9534,plain,
    ( ~ v3_pre_topc(X0_55,sK5)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK5))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1_55,X0_55)
    | r1_tarski(sK3(sK5,X0_55,X1_55),X0_55) ),
    inference(subtyping,[status(esa)],[c_2458])).

cnf(c_11269,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK7),sK5)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0_55,u1_struct_0(sK7))
    | r1_tarski(sK3(sK5,u1_struct_0(sK7),X0_55),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_9534])).

cnf(c_11720,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK7),sK5)
    | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK5))
    | ~ r2_hidden(sK9,u1_struct_0(sK7))
    | r1_tarski(sK3(sK5,u1_struct_0(sK7),sK9),u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_11269])).

cnf(c_16,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2426,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_36])).

cnf(c_2427,plain,
    ( ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK3(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_2426])).

cnf(c_2431,plain,
    ( ~ v3_pre_topc(X0,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK3(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2427,c_37,c_35])).

cnf(c_9535,plain,
    ( ~ v3_pre_topc(X0_55,sK5)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK5))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK3(sK5,X0_55,X1_55),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_2431])).

cnf(c_11256,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK7),sK5)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
    | m1_subset_1(sK3(sK5,u1_struct_0(sK7),X0_55),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0_55,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_9535])).

cnf(c_11714,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK7),sK5)
    | m1_subset_1(sK3(sK5,u1_struct_0(sK7),sK9),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK5))
    | ~ r2_hidden(sK9,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_11256])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_8,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_244,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_8])).

cnf(c_245,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_244])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_762,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK5 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_29])).

cnf(c_763,plain,
    ( ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5)
    | v2_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_765,plain,
    ( v2_pre_topc(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_763,c_36,c_35])).

cnf(c_2735,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_245,c_765])).

cnf(c_2736,plain,
    ( ~ m1_connsp_2(X0,sK7,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(X1,X0)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_2735])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_751,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK5 != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_29])).

cnf(c_752,plain,
    ( ~ l1_pre_topc(sK5)
    | l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_751])).

cnf(c_2740,plain,
    ( ~ m1_connsp_2(X0,sK7,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2736,c_35,c_31,c_752])).

cnf(c_9522,plain,
    ( ~ m1_connsp_2(X0_55,sK7,X1_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7))
    | r2_hidden(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_2740])).

cnf(c_11294,plain,
    ( ~ m1_connsp_2(X0_55,sK7,sK9)
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | r2_hidden(sK9,X0_55) ),
    inference(instantiation,[status(thm)],[c_9522])).

cnf(c_11432,plain,
    ( ~ m1_connsp_2(sK1(sK7,sK9),sK7,sK9)
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | r2_hidden(sK9,sK1(sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_11294])).

cnf(c_2879,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_765])).

cnf(c_2880,plain,
    ( ~ m1_connsp_2(X0,sK7,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_2879])).

cnf(c_2884,plain,
    ( ~ m1_connsp_2(X0,sK7,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2880,c_35,c_31,c_752])).

cnf(c_9516,plain,
    ( ~ m1_connsp_2(X0_55,sK7,X1_55)
    | ~ m1_subset_1(X1_55,u1_struct_0(sK7))
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(subtyping,[status(esa)],[c_2884])).

cnf(c_11285,plain,
    ( ~ m1_connsp_2(X0_55,sK7,sK9)
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_9516])).

cnf(c_11421,plain,
    ( ~ m1_connsp_2(sK1(sK7,sK9),sK7,sK9)
    | m1_subset_1(sK1(sK7,sK9),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_11285])).

cnf(c_9,plain,
    ( m1_connsp_2(sK1(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2387,plain,
    ( m1_connsp_2(sK1(X0,X1),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_765])).

cnf(c_2388,plain,
    ( m1_connsp_2(sK1(sK7,X0),sK7,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_2387])).

cnf(c_2392,plain,
    ( m1_connsp_2(sK1(sK7,X0),sK7,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2388,c_35,c_31,c_752])).

cnf(c_9537,plain,
    ( m1_connsp_2(sK1(sK7,X0_55),sK7,X0_55)
    | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
    inference(subtyping,[status(esa)],[c_2392])).

cnf(c_11279,plain,
    ( m1_connsp_2(sK1(sK7,sK9),sK7,sK9)
    | ~ m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_9537])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_9553,negated_conjecture,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_10741,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9553])).

cnf(c_10787,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10741,c_9555])).

cnf(c_11150,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10787])).

cnf(c_25,negated_conjecture,
    ( r1_tmap_1(sK5,sK4,sK6,sK8)
    | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_9556,negated_conjecture,
    ( r1_tmap_1(sK5,sK4,sK6,sK8)
    | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_10739,plain,
    ( r1_tmap_1(sK5,sK4,sK6,sK8) = iProver_top
    | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9556])).

cnf(c_10834,plain,
    ( r1_tmap_1(sK5,sK4,sK6,sK9) = iProver_top
    | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10739,c_9555])).

cnf(c_11134,plain,
    ( r1_tmap_1(sK5,sK4,sK6,sK9)
    | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10834])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_722,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK5 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_723,plain,
    ( m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_722])).

cnf(c_19,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_224,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_20])).

cnf(c_225,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_224])).

cnf(c_30,negated_conjecture,
    ( v1_tsep_1(sK7,sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_535,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK5 != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_225,c_30])).

cnf(c_536,plain,
    ( v3_pre_topc(u1_struct_0(sK7),sK5)
    | ~ m1_pre_topc(sK7,sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f100])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13496,c_13355,c_12983,c_12213,c_11734,c_11720,c_11714,c_11432,c_11421,c_11279,c_11150,c_11134,c_723,c_536,c_27,c_29,c_35,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:06 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  % Running in FOF mode
% 3.27/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.00  
% 3.27/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.27/1.00  
% 3.27/1.00  ------  iProver source info
% 3.27/1.00  
% 3.27/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.27/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.27/1.00  git: non_committed_changes: false
% 3.27/1.00  git: last_make_outside_of_git: false
% 3.27/1.00  
% 3.27/1.00  ------ 
% 3.27/1.00  
% 3.27/1.00  ------ Input Options
% 3.27/1.00  
% 3.27/1.00  --out_options                           all
% 3.27/1.00  --tptp_safe_out                         true
% 3.27/1.00  --problem_path                          ""
% 3.27/1.00  --include_path                          ""
% 3.27/1.00  --clausifier                            res/vclausify_rel
% 3.27/1.00  --clausifier_options                    --mode clausify
% 3.27/1.00  --stdin                                 false
% 3.27/1.00  --stats_out                             all
% 3.27/1.00  
% 3.27/1.00  ------ General Options
% 3.27/1.00  
% 3.27/1.00  --fof                                   false
% 3.27/1.00  --time_out_real                         305.
% 3.27/1.00  --time_out_virtual                      -1.
% 3.27/1.00  --symbol_type_check                     false
% 3.27/1.00  --clausify_out                          false
% 3.27/1.00  --sig_cnt_out                           false
% 3.27/1.00  --trig_cnt_out                          false
% 3.27/1.00  --trig_cnt_out_tolerance                1.
% 3.27/1.00  --trig_cnt_out_sk_spl                   false
% 3.27/1.00  --abstr_cl_out                          false
% 3.27/1.00  
% 3.27/1.00  ------ Global Options
% 3.27/1.00  
% 3.27/1.00  --schedule                              default
% 3.27/1.00  --add_important_lit                     false
% 3.27/1.00  --prop_solver_per_cl                    1000
% 3.27/1.00  --min_unsat_core                        false
% 3.27/1.00  --soft_assumptions                      false
% 3.27/1.00  --soft_lemma_size                       3
% 3.27/1.00  --prop_impl_unit_size                   0
% 3.27/1.00  --prop_impl_unit                        []
% 3.27/1.00  --share_sel_clauses                     true
% 3.27/1.00  --reset_solvers                         false
% 3.27/1.00  --bc_imp_inh                            [conj_cone]
% 3.27/1.00  --conj_cone_tolerance                   3.
% 3.27/1.00  --extra_neg_conj                        none
% 3.27/1.00  --large_theory_mode                     true
% 3.27/1.00  --prolific_symb_bound                   200
% 3.27/1.00  --lt_threshold                          2000
% 3.27/1.00  --clause_weak_htbl                      true
% 3.27/1.00  --gc_record_bc_elim                     false
% 3.27/1.00  
% 3.27/1.00  ------ Preprocessing Options
% 3.27/1.00  
% 3.27/1.00  --preprocessing_flag                    true
% 3.27/1.00  --time_out_prep_mult                    0.1
% 3.27/1.00  --splitting_mode                        input
% 3.27/1.00  --splitting_grd                         true
% 3.27/1.00  --splitting_cvd                         false
% 3.27/1.00  --splitting_cvd_svl                     false
% 3.27/1.00  --splitting_nvd                         32
% 3.27/1.00  --sub_typing                            true
% 3.27/1.00  --prep_gs_sim                           true
% 3.27/1.00  --prep_unflatten                        true
% 3.27/1.00  --prep_res_sim                          true
% 3.27/1.00  --prep_upred                            true
% 3.27/1.00  --prep_sem_filter                       exhaustive
% 3.27/1.00  --prep_sem_filter_out                   false
% 3.27/1.00  --pred_elim                             true
% 3.27/1.00  --res_sim_input                         true
% 3.27/1.00  --eq_ax_congr_red                       true
% 3.27/1.00  --pure_diseq_elim                       true
% 3.27/1.00  --brand_transform                       false
% 3.27/1.00  --non_eq_to_eq                          false
% 3.27/1.00  --prep_def_merge                        true
% 3.27/1.00  --prep_def_merge_prop_impl              false
% 3.27/1.00  --prep_def_merge_mbd                    true
% 3.27/1.00  --prep_def_merge_tr_red                 false
% 3.27/1.00  --prep_def_merge_tr_cl                  false
% 3.27/1.00  --smt_preprocessing                     true
% 3.27/1.00  --smt_ac_axioms                         fast
% 3.27/1.00  --preprocessed_out                      false
% 3.27/1.00  --preprocessed_stats                    false
% 3.27/1.00  
% 3.27/1.00  ------ Abstraction refinement Options
% 3.27/1.00  
% 3.27/1.00  --abstr_ref                             []
% 3.27/1.00  --abstr_ref_prep                        false
% 3.27/1.00  --abstr_ref_until_sat                   false
% 3.27/1.00  --abstr_ref_sig_restrict                funpre
% 3.27/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/1.00  --abstr_ref_under                       []
% 3.27/1.00  
% 3.27/1.00  ------ SAT Options
% 3.27/1.00  
% 3.27/1.00  --sat_mode                              false
% 3.27/1.00  --sat_fm_restart_options                ""
% 3.27/1.00  --sat_gr_def                            false
% 3.27/1.00  --sat_epr_types                         true
% 3.27/1.00  --sat_non_cyclic_types                  false
% 3.27/1.00  --sat_finite_models                     false
% 3.27/1.00  --sat_fm_lemmas                         false
% 3.27/1.00  --sat_fm_prep                           false
% 3.27/1.00  --sat_fm_uc_incr                        true
% 3.27/1.00  --sat_out_model                         small
% 3.27/1.00  --sat_out_clauses                       false
% 3.27/1.00  
% 3.27/1.00  ------ QBF Options
% 3.27/1.00  
% 3.27/1.00  --qbf_mode                              false
% 3.27/1.00  --qbf_elim_univ                         false
% 3.27/1.00  --qbf_dom_inst                          none
% 3.27/1.00  --qbf_dom_pre_inst                      false
% 3.27/1.00  --qbf_sk_in                             false
% 3.27/1.00  --qbf_pred_elim                         true
% 3.27/1.00  --qbf_split                             512
% 3.27/1.00  
% 3.27/1.00  ------ BMC1 Options
% 3.27/1.00  
% 3.27/1.00  --bmc1_incremental                      false
% 3.27/1.00  --bmc1_axioms                           reachable_all
% 3.27/1.00  --bmc1_min_bound                        0
% 3.27/1.00  --bmc1_max_bound                        -1
% 3.27/1.00  --bmc1_max_bound_default                -1
% 3.27/1.00  --bmc1_symbol_reachability              true
% 3.27/1.00  --bmc1_property_lemmas                  false
% 3.27/1.00  --bmc1_k_induction                      false
% 3.27/1.00  --bmc1_non_equiv_states                 false
% 3.27/1.00  --bmc1_deadlock                         false
% 3.27/1.00  --bmc1_ucm                              false
% 3.27/1.00  --bmc1_add_unsat_core                   none
% 3.27/1.00  --bmc1_unsat_core_children              false
% 3.27/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/1.00  --bmc1_out_stat                         full
% 3.27/1.00  --bmc1_ground_init                      false
% 3.27/1.00  --bmc1_pre_inst_next_state              false
% 3.27/1.00  --bmc1_pre_inst_state                   false
% 3.27/1.00  --bmc1_pre_inst_reach_state             false
% 3.27/1.00  --bmc1_out_unsat_core                   false
% 3.27/1.00  --bmc1_aig_witness_out                  false
% 3.27/1.00  --bmc1_verbose                          false
% 3.27/1.00  --bmc1_dump_clauses_tptp                false
% 3.27/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.27/1.00  --bmc1_dump_file                        -
% 3.27/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.27/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.27/1.00  --bmc1_ucm_extend_mode                  1
% 3.27/1.00  --bmc1_ucm_init_mode                    2
% 3.27/1.00  --bmc1_ucm_cone_mode                    none
% 3.27/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.27/1.00  --bmc1_ucm_relax_model                  4
% 3.27/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.27/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/1.00  --bmc1_ucm_layered_model                none
% 3.27/1.00  --bmc1_ucm_max_lemma_size               10
% 3.27/1.00  
% 3.27/1.00  ------ AIG Options
% 3.27/1.00  
% 3.27/1.00  --aig_mode                              false
% 3.27/1.00  
% 3.27/1.00  ------ Instantiation Options
% 3.27/1.00  
% 3.27/1.00  --instantiation_flag                    true
% 3.27/1.00  --inst_sos_flag                         false
% 3.27/1.00  --inst_sos_phase                        true
% 3.27/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/1.00  --inst_lit_sel_side                     num_symb
% 3.27/1.00  --inst_solver_per_active                1400
% 3.27/1.00  --inst_solver_calls_frac                1.
% 3.27/1.00  --inst_passive_queue_type               priority_queues
% 3.27/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/1.00  --inst_passive_queues_freq              [25;2]
% 3.27/1.00  --inst_dismatching                      true
% 3.27/1.00  --inst_eager_unprocessed_to_passive     true
% 3.27/1.00  --inst_prop_sim_given                   true
% 3.27/1.00  --inst_prop_sim_new                     false
% 3.27/1.00  --inst_subs_new                         false
% 3.27/1.00  --inst_eq_res_simp                      false
% 3.27/1.00  --inst_subs_given                       false
% 3.27/1.00  --inst_orphan_elimination               true
% 3.27/1.00  --inst_learning_loop_flag               true
% 3.27/1.00  --inst_learning_start                   3000
% 3.27/1.00  --inst_learning_factor                  2
% 3.27/1.00  --inst_start_prop_sim_after_learn       3
% 3.27/1.00  --inst_sel_renew                        solver
% 3.27/1.00  --inst_lit_activity_flag                true
% 3.27/1.00  --inst_restr_to_given                   false
% 3.27/1.00  --inst_activity_threshold               500
% 3.27/1.00  --inst_out_proof                        true
% 3.27/1.00  
% 3.27/1.00  ------ Resolution Options
% 3.27/1.00  
% 3.27/1.00  --resolution_flag                       true
% 3.27/1.00  --res_lit_sel                           adaptive
% 3.27/1.00  --res_lit_sel_side                      none
% 3.27/1.00  --res_ordering                          kbo
% 3.27/1.00  --res_to_prop_solver                    active
% 3.27/1.00  --res_prop_simpl_new                    false
% 3.27/1.00  --res_prop_simpl_given                  true
% 3.27/1.00  --res_passive_queue_type                priority_queues
% 3.27/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/1.00  --res_passive_queues_freq               [15;5]
% 3.27/1.00  --res_forward_subs                      full
% 3.27/1.00  --res_backward_subs                     full
% 3.27/1.00  --res_forward_subs_resolution           true
% 3.27/1.00  --res_backward_subs_resolution          true
% 3.27/1.00  --res_orphan_elimination                true
% 3.27/1.00  --res_time_limit                        2.
% 3.27/1.00  --res_out_proof                         true
% 3.27/1.00  
% 3.27/1.00  ------ Superposition Options
% 3.27/1.00  
% 3.27/1.00  --superposition_flag                    true
% 3.27/1.00  --sup_passive_queue_type                priority_queues
% 3.27/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.27/1.00  --demod_completeness_check              fast
% 3.27/1.00  --demod_use_ground                      true
% 3.27/1.00  --sup_to_prop_solver                    passive
% 3.27/1.00  --sup_prop_simpl_new                    true
% 3.27/1.00  --sup_prop_simpl_given                  true
% 3.27/1.00  --sup_fun_splitting                     false
% 3.27/1.00  --sup_smt_interval                      50000
% 3.27/1.00  
% 3.27/1.00  ------ Superposition Simplification Setup
% 3.27/1.00  
% 3.27/1.00  --sup_indices_passive                   []
% 3.27/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/1.00  --sup_full_bw                           [BwDemod]
% 3.27/1.00  --sup_immed_triv                        [TrivRules]
% 3.27/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/1.00  --sup_immed_bw_main                     []
% 3.27/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/1.00  
% 3.27/1.00  ------ Combination Options
% 3.27/1.00  
% 3.27/1.00  --comb_res_mult                         3
% 3.27/1.00  --comb_sup_mult                         2
% 3.27/1.00  --comb_inst_mult                        10
% 3.27/1.00  
% 3.27/1.00  ------ Debug Options
% 3.27/1.00  
% 3.27/1.00  --dbg_backtrace                         false
% 3.27/1.00  --dbg_dump_prop_clauses                 false
% 3.27/1.00  --dbg_dump_prop_clauses_file            -
% 3.27/1.00  --dbg_out_stat                          false
% 3.27/1.00  ------ Parsing...
% 3.27/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.27/1.00  
% 3.27/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 3.27/1.00  
% 3.27/1.00  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.27/1.00  
% 3.27/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.27/1.00  ------ Proving...
% 3.27/1.00  ------ Problem Properties 
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  clauses                                 51
% 3.27/1.00  conjectures                             6
% 3.27/1.00  EPR                                     2
% 3.27/1.00  Horn                                    43
% 3.27/1.00  unary                                   6
% 3.27/1.00  binary                                  10
% 3.27/1.00  lits                                    170
% 3.27/1.00  lits eq                                 7
% 3.27/1.00  fd_pure                                 0
% 3.27/1.00  fd_pseudo                               0
% 3.27/1.00  fd_cond                                 0
% 3.27/1.00  fd_pseudo_cond                          0
% 3.27/1.00  AC symbols                              0
% 3.27/1.00  
% 3.27/1.00  ------ Schedule dynamic 5 is on 
% 3.27/1.00  
% 3.27/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  ------ 
% 3.27/1.00  Current options:
% 3.27/1.00  ------ 
% 3.27/1.00  
% 3.27/1.00  ------ Input Options
% 3.27/1.00  
% 3.27/1.00  --out_options                           all
% 3.27/1.00  --tptp_safe_out                         true
% 3.27/1.00  --problem_path                          ""
% 3.27/1.00  --include_path                          ""
% 3.27/1.00  --clausifier                            res/vclausify_rel
% 3.27/1.00  --clausifier_options                    --mode clausify
% 3.27/1.00  --stdin                                 false
% 3.27/1.00  --stats_out                             all
% 3.27/1.00  
% 3.27/1.00  ------ General Options
% 3.27/1.00  
% 3.27/1.00  --fof                                   false
% 3.27/1.00  --time_out_real                         305.
% 3.27/1.00  --time_out_virtual                      -1.
% 3.27/1.00  --symbol_type_check                     false
% 3.27/1.00  --clausify_out                          false
% 3.27/1.00  --sig_cnt_out                           false
% 3.27/1.00  --trig_cnt_out                          false
% 3.27/1.00  --trig_cnt_out_tolerance                1.
% 3.27/1.00  --trig_cnt_out_sk_spl                   false
% 3.27/1.00  --abstr_cl_out                          false
% 3.27/1.00  
% 3.27/1.00  ------ Global Options
% 3.27/1.00  
% 3.27/1.00  --schedule                              default
% 3.27/1.00  --add_important_lit                     false
% 3.27/1.00  --prop_solver_per_cl                    1000
% 3.27/1.00  --min_unsat_core                        false
% 3.27/1.00  --soft_assumptions                      false
% 3.27/1.00  --soft_lemma_size                       3
% 3.27/1.00  --prop_impl_unit_size                   0
% 3.27/1.00  --prop_impl_unit                        []
% 3.27/1.00  --share_sel_clauses                     true
% 3.27/1.00  --reset_solvers                         false
% 3.27/1.00  --bc_imp_inh                            [conj_cone]
% 3.27/1.00  --conj_cone_tolerance                   3.
% 3.27/1.00  --extra_neg_conj                        none
% 3.27/1.00  --large_theory_mode                     true
% 3.27/1.00  --prolific_symb_bound                   200
% 3.27/1.00  --lt_threshold                          2000
% 3.27/1.00  --clause_weak_htbl                      true
% 3.27/1.00  --gc_record_bc_elim                     false
% 3.27/1.00  
% 3.27/1.00  ------ Preprocessing Options
% 3.27/1.00  
% 3.27/1.00  --preprocessing_flag                    true
% 3.27/1.00  --time_out_prep_mult                    0.1
% 3.27/1.00  --splitting_mode                        input
% 3.27/1.00  --splitting_grd                         true
% 3.27/1.00  --splitting_cvd                         false
% 3.27/1.00  --splitting_cvd_svl                     false
% 3.27/1.00  --splitting_nvd                         32
% 3.27/1.00  --sub_typing                            true
% 3.27/1.00  --prep_gs_sim                           true
% 3.27/1.00  --prep_unflatten                        true
% 3.27/1.00  --prep_res_sim                          true
% 3.27/1.00  --prep_upred                            true
% 3.27/1.00  --prep_sem_filter                       exhaustive
% 3.27/1.00  --prep_sem_filter_out                   false
% 3.27/1.00  --pred_elim                             true
% 3.27/1.00  --res_sim_input                         true
% 3.27/1.00  --eq_ax_congr_red                       true
% 3.27/1.00  --pure_diseq_elim                       true
% 3.27/1.00  --brand_transform                       false
% 3.27/1.00  --non_eq_to_eq                          false
% 3.27/1.00  --prep_def_merge                        true
% 3.27/1.00  --prep_def_merge_prop_impl              false
% 3.27/1.00  --prep_def_merge_mbd                    true
% 3.27/1.00  --prep_def_merge_tr_red                 false
% 3.27/1.00  --prep_def_merge_tr_cl                  false
% 3.27/1.00  --smt_preprocessing                     true
% 3.27/1.00  --smt_ac_axioms                         fast
% 3.27/1.00  --preprocessed_out                      false
% 3.27/1.00  --preprocessed_stats                    false
% 3.27/1.00  
% 3.27/1.00  ------ Abstraction refinement Options
% 3.27/1.00  
% 3.27/1.00  --abstr_ref                             []
% 3.27/1.00  --abstr_ref_prep                        false
% 3.27/1.00  --abstr_ref_until_sat                   false
% 3.27/1.00  --abstr_ref_sig_restrict                funpre
% 3.27/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/1.00  --abstr_ref_under                       []
% 3.27/1.00  
% 3.27/1.00  ------ SAT Options
% 3.27/1.00  
% 3.27/1.00  --sat_mode                              false
% 3.27/1.00  --sat_fm_restart_options                ""
% 3.27/1.00  --sat_gr_def                            false
% 3.27/1.00  --sat_epr_types                         true
% 3.27/1.00  --sat_non_cyclic_types                  false
% 3.27/1.00  --sat_finite_models                     false
% 3.27/1.00  --sat_fm_lemmas                         false
% 3.27/1.00  --sat_fm_prep                           false
% 3.27/1.00  --sat_fm_uc_incr                        true
% 3.27/1.00  --sat_out_model                         small
% 3.27/1.00  --sat_out_clauses                       false
% 3.27/1.00  
% 3.27/1.00  ------ QBF Options
% 3.27/1.00  
% 3.27/1.00  --qbf_mode                              false
% 3.27/1.00  --qbf_elim_univ                         false
% 3.27/1.00  --qbf_dom_inst                          none
% 3.27/1.00  --qbf_dom_pre_inst                      false
% 3.27/1.00  --qbf_sk_in                             false
% 3.27/1.00  --qbf_pred_elim                         true
% 3.27/1.00  --qbf_split                             512
% 3.27/1.00  
% 3.27/1.00  ------ BMC1 Options
% 3.27/1.00  
% 3.27/1.00  --bmc1_incremental                      false
% 3.27/1.00  --bmc1_axioms                           reachable_all
% 3.27/1.00  --bmc1_min_bound                        0
% 3.27/1.00  --bmc1_max_bound                        -1
% 3.27/1.00  --bmc1_max_bound_default                -1
% 3.27/1.00  --bmc1_symbol_reachability              true
% 3.27/1.00  --bmc1_property_lemmas                  false
% 3.27/1.00  --bmc1_k_induction                      false
% 3.27/1.00  --bmc1_non_equiv_states                 false
% 3.27/1.00  --bmc1_deadlock                         false
% 3.27/1.00  --bmc1_ucm                              false
% 3.27/1.00  --bmc1_add_unsat_core                   none
% 3.27/1.00  --bmc1_unsat_core_children              false
% 3.27/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/1.00  --bmc1_out_stat                         full
% 3.27/1.00  --bmc1_ground_init                      false
% 3.27/1.00  --bmc1_pre_inst_next_state              false
% 3.27/1.00  --bmc1_pre_inst_state                   false
% 3.27/1.00  --bmc1_pre_inst_reach_state             false
% 3.27/1.00  --bmc1_out_unsat_core                   false
% 3.27/1.00  --bmc1_aig_witness_out                  false
% 3.27/1.00  --bmc1_verbose                          false
% 3.27/1.00  --bmc1_dump_clauses_tptp                false
% 3.27/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.27/1.00  --bmc1_dump_file                        -
% 3.27/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.27/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.27/1.00  --bmc1_ucm_extend_mode                  1
% 3.27/1.00  --bmc1_ucm_init_mode                    2
% 3.27/1.00  --bmc1_ucm_cone_mode                    none
% 3.27/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.27/1.00  --bmc1_ucm_relax_model                  4
% 3.27/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.27/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/1.00  --bmc1_ucm_layered_model                none
% 3.27/1.00  --bmc1_ucm_max_lemma_size               10
% 3.27/1.00  
% 3.27/1.00  ------ AIG Options
% 3.27/1.00  
% 3.27/1.00  --aig_mode                              false
% 3.27/1.00  
% 3.27/1.00  ------ Instantiation Options
% 3.27/1.00  
% 3.27/1.00  --instantiation_flag                    true
% 3.27/1.00  --inst_sos_flag                         false
% 3.27/1.00  --inst_sos_phase                        true
% 3.27/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/1.00  --inst_lit_sel_side                     none
% 3.27/1.00  --inst_solver_per_active                1400
% 3.27/1.00  --inst_solver_calls_frac                1.
% 3.27/1.00  --inst_passive_queue_type               priority_queues
% 3.27/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/1.00  --inst_passive_queues_freq              [25;2]
% 3.27/1.00  --inst_dismatching                      true
% 3.27/1.00  --inst_eager_unprocessed_to_passive     true
% 3.27/1.00  --inst_prop_sim_given                   true
% 3.27/1.00  --inst_prop_sim_new                     false
% 3.27/1.00  --inst_subs_new                         false
% 3.27/1.00  --inst_eq_res_simp                      false
% 3.27/1.00  --inst_subs_given                       false
% 3.27/1.00  --inst_orphan_elimination               true
% 3.27/1.00  --inst_learning_loop_flag               true
% 3.27/1.00  --inst_learning_start                   3000
% 3.27/1.00  --inst_learning_factor                  2
% 3.27/1.00  --inst_start_prop_sim_after_learn       3
% 3.27/1.00  --inst_sel_renew                        solver
% 3.27/1.00  --inst_lit_activity_flag                true
% 3.27/1.00  --inst_restr_to_given                   false
% 3.27/1.00  --inst_activity_threshold               500
% 3.27/1.00  --inst_out_proof                        true
% 3.27/1.00  
% 3.27/1.00  ------ Resolution Options
% 3.27/1.00  
% 3.27/1.00  --resolution_flag                       false
% 3.27/1.00  --res_lit_sel                           adaptive
% 3.27/1.00  --res_lit_sel_side                      none
% 3.27/1.00  --res_ordering                          kbo
% 3.27/1.00  --res_to_prop_solver                    active
% 3.27/1.00  --res_prop_simpl_new                    false
% 3.27/1.00  --res_prop_simpl_given                  true
% 3.27/1.00  --res_passive_queue_type                priority_queues
% 3.27/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/1.00  --res_passive_queues_freq               [15;5]
% 3.27/1.00  --res_forward_subs                      full
% 3.27/1.00  --res_backward_subs                     full
% 3.27/1.00  --res_forward_subs_resolution           true
% 3.27/1.00  --res_backward_subs_resolution          true
% 3.27/1.00  --res_orphan_elimination                true
% 3.27/1.00  --res_time_limit                        2.
% 3.27/1.00  --res_out_proof                         true
% 3.27/1.00  
% 3.27/1.00  ------ Superposition Options
% 3.27/1.00  
% 3.27/1.00  --superposition_flag                    true
% 3.27/1.00  --sup_passive_queue_type                priority_queues
% 3.27/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.27/1.00  --demod_completeness_check              fast
% 3.27/1.00  --demod_use_ground                      true
% 3.27/1.00  --sup_to_prop_solver                    passive
% 3.27/1.00  --sup_prop_simpl_new                    true
% 3.27/1.00  --sup_prop_simpl_given                  true
% 3.27/1.00  --sup_fun_splitting                     false
% 3.27/1.00  --sup_smt_interval                      50000
% 3.27/1.00  
% 3.27/1.00  ------ Superposition Simplification Setup
% 3.27/1.00  
% 3.27/1.00  --sup_indices_passive                   []
% 3.27/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/1.00  --sup_full_bw                           [BwDemod]
% 3.27/1.00  --sup_immed_triv                        [TrivRules]
% 3.27/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/1.00  --sup_immed_bw_main                     []
% 3.27/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/1.00  
% 3.27/1.00  ------ Combination Options
% 3.27/1.00  
% 3.27/1.00  --comb_res_mult                         3
% 3.27/1.00  --comb_sup_mult                         2
% 3.27/1.00  --comb_inst_mult                        10
% 3.27/1.00  
% 3.27/1.00  ------ Debug Options
% 3.27/1.00  
% 3.27/1.00  --dbg_backtrace                         false
% 3.27/1.00  --dbg_dump_prop_clauses                 false
% 3.27/1.00  --dbg_dump_prop_clauses_file            -
% 3.27/1.00  --dbg_out_stat                          false
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  ------ Proving...
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  % SZS status Theorem for theBenchmark.p
% 3.27/1.00  
% 3.27/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.27/1.00  
% 3.27/1.00  fof(f14,conjecture,(
% 3.27/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f15,negated_conjecture,(
% 3.27/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 3.27/1.00    inference(negated_conjecture,[],[f14])).
% 3.27/1.00  
% 3.27/1.00  fof(f37,plain,(
% 3.27/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.27/1.00    inference(ennf_transformation,[],[f15])).
% 3.27/1.00  
% 3.27/1.00  fof(f38,plain,(
% 3.27/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.27/1.00    inference(flattening,[],[f37])).
% 3.27/1.00  
% 3.27/1.00  fof(f54,plain,(
% 3.27/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.27/1.00    inference(nnf_transformation,[],[f38])).
% 3.27/1.00  
% 3.27/1.00  fof(f55,plain,(
% 3.27/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.27/1.00    inference(flattening,[],[f54])).
% 3.27/1.00  
% 3.27/1.00  fof(f61,plain,(
% 3.27/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK9) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK9) | r1_tmap_1(X1,X0,X2,X4)) & sK9 = X4 & m1_subset_1(sK9,u1_struct_0(X3)))) )),
% 3.27/1.00    introduced(choice_axiom,[])).
% 3.27/1.00  
% 3.27/1.00  fof(f60,plain,(
% 3.27/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK8)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK8)) & sK8 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK8,u1_struct_0(X1)))) )),
% 3.27/1.00    introduced(choice_axiom,[])).
% 3.27/1.00  
% 3.27/1.00  fof(f59,plain,(
% 3.27/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK7,X0,k2_tmap_1(X1,X0,X2,sK7),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK7,X0,k2_tmap_1(X1,X0,X2,sK7),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK7))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK7,X1) & v1_tsep_1(sK7,X1) & ~v2_struct_0(sK7))) )),
% 3.27/1.00    introduced(choice_axiom,[])).
% 3.27/1.00  
% 3.27/1.00  fof(f58,plain,(
% 3.27/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK6,X3),X5) | ~r1_tmap_1(X1,X0,sK6,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK6,X3),X5) | r1_tmap_1(X1,X0,sK6,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK6,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK6))) )),
% 3.27/1.00    introduced(choice_axiom,[])).
% 3.27/1.00  
% 3.27/1.00  fof(f57,plain,(
% 3.27/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK5,X0,X2,X3),X5) | ~r1_tmap_1(sK5,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK5,X0,X2,X3),X5) | r1_tmap_1(sK5,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK5))) & m1_pre_topc(X3,sK5) & v1_tsep_1(X3,sK5) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK5),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))) )),
% 3.27/1.00    introduced(choice_axiom,[])).
% 3.27/1.00  
% 3.27/1.00  fof(f56,plain,(
% 3.27/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK4,k2_tmap_1(X1,sK4,X2,X3),X5) | ~r1_tmap_1(X1,sK4,X2,X4)) & (r1_tmap_1(X3,sK4,k2_tmap_1(X1,sK4,X2,X3),X5) | r1_tmap_1(X1,sK4,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK4)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK4)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 3.27/1.00    introduced(choice_axiom,[])).
% 3.27/1.00  
% 3.27/1.00  fof(f62,plain,(
% 3.27/1.00    ((((((~r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) | ~r1_tmap_1(sK5,sK4,sK6,sK8)) & (r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) | r1_tmap_1(sK5,sK4,sK6,sK8)) & sK8 = sK9 & m1_subset_1(sK9,u1_struct_0(sK7))) & m1_subset_1(sK8,u1_struct_0(sK5))) & m1_pre_topc(sK7,sK5) & v1_tsep_1(sK7,sK5) & ~v2_struct_0(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) & v1_funct_1(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 3.27/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f55,f61,f60,f59,f58,f57,f56])).
% 3.27/1.00  
% 3.27/1.00  fof(f98,plain,(
% 3.27/1.00    m1_pre_topc(sK7,sK5)),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f13,axiom,(
% 3.27/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f35,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.27/1.00    inference(ennf_transformation,[],[f13])).
% 3.27/1.00  
% 3.27/1.00  fof(f36,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/1.00    inference(flattening,[],[f35])).
% 3.27/1.00  
% 3.27/1.00  fof(f53,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/1.00    inference(nnf_transformation,[],[f36])).
% 3.27/1.00  
% 3.27/1.00  fof(f86,plain,(
% 3.27/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f53])).
% 3.27/1.00  
% 3.27/1.00  fof(f108,plain,(
% 3.27/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/1.00    inference(equality_resolution,[],[f86])).
% 3.27/1.00  
% 3.27/1.00  fof(f94,plain,(
% 3.27/1.00    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4))),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f93,plain,(
% 3.27/1.00    v1_funct_1(sK6)),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f5,axiom,(
% 3.27/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f20,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.27/1.00    inference(ennf_transformation,[],[f5])).
% 3.27/1.00  
% 3.27/1.00  fof(f21,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/1.00    inference(flattening,[],[f20])).
% 3.27/1.00  
% 3.27/1.00  fof(f70,plain,(
% 3.27/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f21])).
% 3.27/1.00  
% 3.27/1.00  fof(f90,plain,(
% 3.27/1.00    ~v2_struct_0(sK5)),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f91,plain,(
% 3.27/1.00    v2_pre_topc(sK5)),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f92,plain,(
% 3.27/1.00    l1_pre_topc(sK5)),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f96,plain,(
% 3.27/1.00    ~v2_struct_0(sK7)),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f88,plain,(
% 3.27/1.00    v2_pre_topc(sK4)),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f87,plain,(
% 3.27/1.00    ~v2_struct_0(sK4)),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f89,plain,(
% 3.27/1.00    l1_pre_topc(sK4)),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f95,plain,(
% 3.27/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f85,plain,(
% 3.27/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f53])).
% 3.27/1.00  
% 3.27/1.00  fof(f109,plain,(
% 3.27/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/1.00    inference(equality_resolution,[],[f85])).
% 3.27/1.00  
% 3.27/1.00  fof(f12,axiom,(
% 3.27/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f33,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.27/1.00    inference(ennf_transformation,[],[f12])).
% 3.27/1.00  
% 3.27/1.00  fof(f34,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/1.00    inference(flattening,[],[f33])).
% 3.27/1.00  
% 3.27/1.00  fof(f84,plain,(
% 3.27/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f34])).
% 3.27/1.00  
% 3.27/1.00  fof(f107,plain,(
% 3.27/1.00    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/1.00    inference(equality_resolution,[],[f84])).
% 3.27/1.00  
% 3.27/1.00  fof(f103,plain,(
% 3.27/1.00    ~r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) | ~r1_tmap_1(sK5,sK4,sK6,sK8)),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f101,plain,(
% 3.27/1.00    sK8 = sK9),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f2,axiom,(
% 3.27/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f43,plain,(
% 3.27/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.27/1.00    inference(nnf_transformation,[],[f2])).
% 3.27/1.00  
% 3.27/1.00  fof(f66,plain,(
% 3.27/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.27/1.00    inference(cnf_transformation,[],[f43])).
% 3.27/1.00  
% 3.27/1.00  fof(f1,axiom,(
% 3.27/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f16,plain,(
% 3.27/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.27/1.00    inference(ennf_transformation,[],[f1])).
% 3.27/1.00  
% 3.27/1.00  fof(f39,plain,(
% 3.27/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.27/1.00    inference(nnf_transformation,[],[f16])).
% 3.27/1.00  
% 3.27/1.00  fof(f40,plain,(
% 3.27/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.27/1.00    inference(rectify,[],[f39])).
% 3.27/1.00  
% 3.27/1.00  fof(f41,plain,(
% 3.27/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.27/1.00    introduced(choice_axiom,[])).
% 3.27/1.00  
% 3.27/1.00  fof(f42,plain,(
% 3.27/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.27/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.27/1.00  
% 3.27/1.00  fof(f63,plain,(
% 3.27/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f42])).
% 3.27/1.00  
% 3.27/1.00  fof(f9,axiom,(
% 3.27/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f28,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.27/1.00    inference(ennf_transformation,[],[f9])).
% 3.27/1.00  
% 3.27/1.00  fof(f29,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/1.00    inference(flattening,[],[f28])).
% 3.27/1.00  
% 3.27/1.00  fof(f46,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/1.00    inference(nnf_transformation,[],[f29])).
% 3.27/1.00  
% 3.27/1.00  fof(f47,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/1.00    inference(rectify,[],[f46])).
% 3.27/1.00  
% 3.27/1.00  fof(f49,plain,(
% 3.27/1.00    ! [X4,X1,X0] : (? [X5] : (r1_tarski(X5,X1) & m1_connsp_2(X5,X0,X4) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(sK3(X0,X1,X4),X1) & m1_connsp_2(sK3(X0,X1,X4),X0,X4) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.27/1.00    introduced(choice_axiom,[])).
% 3.27/1.00  
% 3.27/1.00  fof(f48,plain,(
% 3.27/1.00    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK2(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 3.27/1.00    introduced(choice_axiom,[])).
% 3.27/1.00  
% 3.27/1.00  fof(f50,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | (! [X3] : (~r1_tarski(X3,X1) | ~m1_connsp_2(X3,X0,sK2(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : ((r1_tarski(sK3(X0,X1,X4),X1) & m1_connsp_2(sK3(X0,X1,X4),X0,X4) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f47,f49,f48])).
% 3.27/1.00  
% 3.27/1.00  fof(f75,plain,(
% 3.27/1.00    ( ! [X4,X0,X1] : (m1_connsp_2(sK3(X0,X1,X4),X0,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f50])).
% 3.27/1.00  
% 3.27/1.00  fof(f76,plain,(
% 3.27/1.00    ( ! [X4,X0,X1] : (r1_tarski(sK3(X0,X1,X4),X1) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f50])).
% 3.27/1.00  
% 3.27/1.00  fof(f74,plain,(
% 3.27/1.00    ( ! [X4,X0,X1] : (m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f50])).
% 3.27/1.00  
% 3.27/1.00  fof(f8,axiom,(
% 3.27/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f26,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.27/1.00    inference(ennf_transformation,[],[f8])).
% 3.27/1.00  
% 3.27/1.00  fof(f27,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/1.00    inference(flattening,[],[f26])).
% 3.27/1.00  
% 3.27/1.00  fof(f73,plain,(
% 3.27/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f27])).
% 3.27/1.00  
% 3.27/1.00  fof(f6,axiom,(
% 3.27/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f22,plain,(
% 3.27/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.27/1.00    inference(ennf_transformation,[],[f6])).
% 3.27/1.00  
% 3.27/1.00  fof(f23,plain,(
% 3.27/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/1.00    inference(flattening,[],[f22])).
% 3.27/1.00  
% 3.27/1.00  fof(f71,plain,(
% 3.27/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f23])).
% 3.27/1.00  
% 3.27/1.00  fof(f3,axiom,(
% 3.27/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f17,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.27/1.00    inference(ennf_transformation,[],[f3])).
% 3.27/1.00  
% 3.27/1.00  fof(f18,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.27/1.00    inference(flattening,[],[f17])).
% 3.27/1.00  
% 3.27/1.00  fof(f68,plain,(
% 3.27/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f18])).
% 3.27/1.00  
% 3.27/1.00  fof(f4,axiom,(
% 3.27/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f19,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.27/1.00    inference(ennf_transformation,[],[f4])).
% 3.27/1.00  
% 3.27/1.00  fof(f69,plain,(
% 3.27/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f19])).
% 3.27/1.00  
% 3.27/1.00  fof(f7,axiom,(
% 3.27/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f24,plain,(
% 3.27/1.00    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.27/1.00    inference(ennf_transformation,[],[f7])).
% 3.27/1.00  
% 3.27/1.00  fof(f25,plain,(
% 3.27/1.00    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/1.00    inference(flattening,[],[f24])).
% 3.27/1.00  
% 3.27/1.00  fof(f44,plain,(
% 3.27/1.00    ! [X1,X0] : (? [X2] : m1_connsp_2(X2,X0,X1) => m1_connsp_2(sK1(X0,X1),X0,X1))),
% 3.27/1.00    introduced(choice_axiom,[])).
% 3.27/1.00  
% 3.27/1.00  fof(f45,plain,(
% 3.27/1.00    ! [X0,X1] : (m1_connsp_2(sK1(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.27/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f44])).
% 3.27/1.00  
% 3.27/1.00  fof(f72,plain,(
% 3.27/1.00    ( ! [X0,X1] : (m1_connsp_2(sK1(X0,X1),X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f45])).
% 3.27/1.00  
% 3.27/1.00  fof(f99,plain,(
% 3.27/1.00    m1_subset_1(sK8,u1_struct_0(sK5))),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f102,plain,(
% 3.27/1.00    r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) | r1_tmap_1(sK5,sK4,sK6,sK8)),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f11,axiom,(
% 3.27/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f32,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.27/1.00    inference(ennf_transformation,[],[f11])).
% 3.27/1.00  
% 3.27/1.00  fof(f83,plain,(
% 3.27/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f32])).
% 3.27/1.00  
% 3.27/1.00  fof(f10,axiom,(
% 3.27/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f30,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.27/1.00    inference(ennf_transformation,[],[f10])).
% 3.27/1.00  
% 3.27/1.00  fof(f31,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.27/1.00    inference(flattening,[],[f30])).
% 3.27/1.00  
% 3.27/1.00  fof(f51,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.27/1.00    inference(nnf_transformation,[],[f31])).
% 3.27/1.00  
% 3.27/1.00  fof(f52,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.27/1.00    inference(flattening,[],[f51])).
% 3.27/1.00  
% 3.27/1.00  fof(f80,plain,(
% 3.27/1.00    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f52])).
% 3.27/1.00  
% 3.27/1.00  fof(f106,plain,(
% 3.27/1.00    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/1.00    inference(equality_resolution,[],[f80])).
% 3.27/1.00  
% 3.27/1.00  fof(f97,plain,(
% 3.27/1.00    v1_tsep_1(sK7,sK5)),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  fof(f100,plain,(
% 3.27/1.00    m1_subset_1(sK9,u1_struct_0(sK7))),
% 3.27/1.00    inference(cnf_transformation,[],[f62])).
% 3.27/1.00  
% 3.27/1.00  cnf(c_29,negated_conjecture,
% 3.27/1.00      ( m1_pre_topc(sK7,sK5) ),
% 3.27/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_22,plain,
% 3.27/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.27/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.27/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.27/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 3.27/1.00      | ~ m1_pre_topc(X4,X0)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.27/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.27/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.27/1.00      | ~ v1_funct_1(X2)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | v2_struct_0(X4)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_33,negated_conjecture,
% 3.27/1.00      ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK4)) ),
% 3.27/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_605,plain,
% 3.27/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 3.27/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.27/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 3.27/1.00      | ~ m1_pre_topc(X4,X0)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.27/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.27/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.27/1.00      | ~ v1_funct_1(X2)
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X4)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X0)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK5)
% 3.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.27/1.00      | sK6 != X2 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_606,plain,
% 3.27/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
% 3.27/1.00      | r1_tmap_1(X2,X1,sK6,X3)
% 3.27/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 3.27/1.00      | ~ m1_pre_topc(X0,X2)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.27/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.27/1.00      | ~ v1_funct_1(sK6)
% 3.27/1.00      | v2_struct_0(X2)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | ~ l1_pre_topc(X2)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X2)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_605]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_34,negated_conjecture,
% 3.27/1.00      ( v1_funct_1(sK6) ),
% 3.27/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_610,plain,
% 3.27/1.00      ( ~ r1_tarski(X4,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.27/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.27/1.00      | ~ m1_pre_topc(X0,X2)
% 3.27/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 3.27/1.00      | r1_tmap_1(X2,X1,sK6,X3)
% 3.27/1.00      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
% 3.27/1.00      | v2_struct_0(X2)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | ~ l1_pre_topc(X2)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X2)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_606,c_34]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_611,plain,
% 3.27/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
% 3.27/1.00      | r1_tmap_1(X2,X1,sK6,X3)
% 3.27/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 3.27/1.00      | ~ m1_pre_topc(X0,X2)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.27/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.27/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X2)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ l1_pre_topc(X2)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X2)
% 3.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_610]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_7,plain,
% 3.27/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/1.00      | m1_subset_1(X2,u1_struct_0(X1))
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | ~ l1_pre_topc(X1) ),
% 3.27/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_652,plain,
% 3.27/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
% 3.27/1.00      | r1_tmap_1(X2,X1,sK6,X3)
% 3.27/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 3.27/1.00      | ~ m1_pre_topc(X0,X2)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.27/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X2)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ l1_pre_topc(X2)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X2)
% 3.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_611,c_7]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_773,plain,
% 3.27/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
% 3.27/1.00      | r1_tmap_1(X2,X1,sK6,X3)
% 3.27/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.27/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | v2_struct_0(X2)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | ~ l1_pre_topc(X2)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X2)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.27/1.00      | sK5 != X2
% 3.27/1.00      | sK7 != X0 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_652]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_774,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,X0,sK6,X1)
% 3.27/1.00      | ~ r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
% 3.27/1.00      | ~ m1_connsp_2(X2,sK5,X1)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 3.27/1.00      | ~ r1_tarski(X2,u1_struct_0(sK7))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | v2_struct_0(sK5)
% 3.27/1.00      | v2_struct_0(sK7)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | ~ l1_pre_topc(sK5)
% 3.27/1.00      | ~ v2_pre_topc(X0)
% 3.27/1.00      | ~ v2_pre_topc(sK5)
% 3.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.27/1.00      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_773]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_37,negated_conjecture,
% 3.27/1.00      ( ~ v2_struct_0(sK5) ),
% 3.27/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_36,negated_conjecture,
% 3.27/1.00      ( v2_pre_topc(sK5) ),
% 3.27/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_35,negated_conjecture,
% 3.27/1.00      ( l1_pre_topc(sK5) ),
% 3.27/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_31,negated_conjecture,
% 3.27/1.00      ( ~ v2_struct_0(sK7) ),
% 3.27/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_778,plain,
% 3.27/1.00      ( ~ v2_pre_topc(X0)
% 3.27/1.00      | r1_tmap_1(sK5,X0,sK6,X1)
% 3.27/1.00      | ~ r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
% 3.27/1.00      | ~ m1_connsp_2(X2,sK5,X1)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 3.27/1.00      | ~ r1_tarski(X2,u1_struct_0(sK7))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.27/1.00      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_774,c_37,c_36,c_35,c_31]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_779,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,X0,sK6,X1)
% 3.27/1.00      | ~ r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
% 3.27/1.00      | ~ m1_connsp_2(X2,sK5,X1)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 3.27/1.00      | ~ r1_tarski(X2,u1_struct_0(sK7))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | ~ v2_pre_topc(X0)
% 3.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.27/1.00      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_778]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_39,negated_conjecture,
% 3.27/1.00      ( v2_pre_topc(sK4) ),
% 3.27/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2219,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,X0,sK6,X1)
% 3.27/1.00      | ~ r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
% 3.27/1.00      | ~ m1_connsp_2(X2,sK5,X1)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 3.27/1.00      | ~ r1_tarski(X2,u1_struct_0(sK7))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.27/1.00      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 3.27/1.00      | sK4 != X0 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_779,c_39]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2220,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,sK4,sK6,X0)
% 3.27/1.00      | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0)
% 3.27/1.00      | ~ m1_connsp_2(X1,sK5,X0)
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.27/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 3.27/1.00      | ~ r1_tarski(X1,u1_struct_0(sK7))
% 3.27/1.00      | v2_struct_0(sK4)
% 3.27/1.00      | ~ l1_pre_topc(sK4)
% 3.27/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_2219]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_40,negated_conjecture,
% 3.27/1.00      ( ~ v2_struct_0(sK4) ),
% 3.27/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_38,negated_conjecture,
% 3.27/1.00      ( l1_pre_topc(sK4) ),
% 3.27/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_32,negated_conjecture,
% 3.27/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4)))) ),
% 3.27/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2224,plain,
% 3.27/1.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.27/1.00      | ~ m1_connsp_2(X1,sK5,X0)
% 3.27/1.00      | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0)
% 3.27/1.00      | r1_tmap_1(sK5,sK4,sK6,X0)
% 3.27/1.00      | ~ r1_tarski(X1,u1_struct_0(sK7))
% 3.27/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_2220,c_40,c_38,c_32]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2225,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,sK4,sK6,X0)
% 3.27/1.00      | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0)
% 3.27/1.00      | ~ m1_connsp_2(X1,sK5,X0)
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.27/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ r1_tarski(X1,u1_struct_0(sK7))
% 3.27/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_2224]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9543,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,sK4,sK6,X0_55)
% 3.27/1.00      | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0_55)
% 3.27/1.00      | ~ m1_connsp_2(X1_55,sK5,X0_55)
% 3.27/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 3.27/1.00      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ r1_tarski(X1_55,u1_struct_0(sK7))
% 3.27/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_2225]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9805,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,sK4,sK6,X0_55)
% 3.27/1.00      | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0_55)
% 3.27/1.00      | ~ m1_connsp_2(X1_55,sK5,X0_55)
% 3.27/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 3.27/1.00      | ~ m1_subset_1(X1_55,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ r1_tarski(X1_55,u1_struct_0(sK7)) ),
% 3.27/1.00      inference(equality_resolution_simp,[status(thm)],[c_9543]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11299,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,sK4,sK6,sK9)
% 3.27/1.00      | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
% 3.27/1.00      | ~ m1_connsp_2(X0_55,sK5,sK9)
% 3.27/1.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK7))
% 3.27/1.00      | ~ r1_tarski(X0_55,u1_struct_0(sK7)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_9805]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_13496,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,sK4,sK6,sK9)
% 3.27/1.00      | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9)
% 3.27/1.00      | ~ m1_connsp_2(sK3(sK5,u1_struct_0(sK7),sK9),sK5,sK9)
% 3.27/1.00      | ~ m1_subset_1(sK3(sK5,u1_struct_0(sK7),sK9),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK7))
% 3.27/1.00      | ~ r1_tarski(sK3(sK5,u1_struct_0(sK7),sK9),u1_struct_0(sK7)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_11299]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_23,plain,
% 3.27/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.27/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.27/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.27/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 3.27/1.00      | ~ m1_pre_topc(X4,X0)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.27/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 3.27/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 3.27/1.00      | ~ v1_funct_1(X2)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | v2_struct_0(X4)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_21,plain,
% 3.27/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.27/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.27/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.27/1.00      | ~ m1_pre_topc(X4,X0)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.27/1.00      | ~ v1_funct_1(X2)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | v2_struct_0(X4)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_216,plain,
% 3.27/1.00      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.27/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.27/1.00      | ~ r1_tmap_1(X0,X1,X2,X3)
% 3.27/1.00      | ~ m1_pre_topc(X4,X0)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.27/1.00      | ~ v1_funct_1(X2)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | v2_struct_0(X4)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X0) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_23,c_21]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_217,plain,
% 3.27/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.27/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.27/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.27/1.00      | ~ m1_pre_topc(X4,X0)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.27/1.00      | ~ v1_funct_1(X2)
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X4)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X0)
% 3.27/1.00      | ~ v2_pre_topc(X1) ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_216]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_548,plain,
% 3.27/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 3.27/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 3.27/1.00      | ~ m1_pre_topc(X4,X0)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 3.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.27/1.00      | ~ v1_funct_1(X2)
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X4)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X0)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK5)
% 3.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.27/1.00      | sK6 != X2 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_217,c_33]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_549,plain,
% 3.27/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
% 3.27/1.00      | ~ r1_tmap_1(X2,X1,sK6,X3)
% 3.27/1.00      | ~ m1_pre_topc(X0,X2)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.27/1.00      | ~ v1_funct_1(sK6)
% 3.27/1.00      | v2_struct_0(X2)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | ~ l1_pre_topc(X2)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X2)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_548]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_553,plain,
% 3.27/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.27/1.00      | ~ m1_pre_topc(X0,X2)
% 3.27/1.00      | ~ r1_tmap_1(X2,X1,sK6,X3)
% 3.27/1.00      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
% 3.27/1.00      | v2_struct_0(X2)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | ~ l1_pre_topc(X2)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X2)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_549,c_34]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_554,plain,
% 3.27/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
% 3.27/1.00      | ~ r1_tmap_1(X2,X1,sK6,X3)
% 3.27/1.00      | ~ m1_pre_topc(X0,X2)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X2)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ l1_pre_topc(X2)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X2)
% 3.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_553]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_589,plain,
% 3.27/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
% 3.27/1.00      | ~ r1_tmap_1(X2,X1,sK6,X3)
% 3.27/1.00      | ~ m1_pre_topc(X0,X2)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | v2_struct_0(X2)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ l1_pre_topc(X2)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X2)
% 3.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_554,c_7]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_821,plain,
% 3.27/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK6,X0),X3)
% 3.27/1.00      | ~ r1_tmap_1(X2,X1,sK6,X3)
% 3.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | v2_struct_0(X2)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | ~ l1_pre_topc(X2)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X2)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK5)
% 3.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK4)
% 3.27/1.00      | sK5 != X2
% 3.27/1.00      | sK7 != X0 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_589]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_822,plain,
% 3.27/1.00      ( ~ r1_tmap_1(sK5,X0,sK6,X1)
% 3.27/1.00      | r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | v2_struct_0(sK5)
% 3.27/1.00      | v2_struct_0(sK7)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | ~ l1_pre_topc(sK5)
% 3.27/1.00      | ~ v2_pre_topc(X0)
% 3.27/1.00      | ~ v2_pre_topc(sK5)
% 3.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.27/1.00      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_821]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_826,plain,
% 3.27/1.00      ( ~ v2_pre_topc(X0)
% 3.27/1.00      | ~ r1_tmap_1(sK5,X0,sK6,X1)
% 3.27/1.00      | r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.27/1.00      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_822,c_37,c_36,c_35,c_31]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_827,plain,
% 3.27/1.00      ( ~ r1_tmap_1(sK5,X0,sK6,X1)
% 3.27/1.00      | r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | ~ v2_pre_topc(X0)
% 3.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.27/1.00      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_826]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2195,plain,
% 3.27/1.00      ( ~ r1_tmap_1(sK5,X0,sK6,X1)
% 3.27/1.00      | r1_tmap_1(sK7,X0,k2_tmap_1(sK5,X0,sK6,sK7),X1)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0))))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK4)
% 3.27/1.00      | u1_struct_0(sK5) != u1_struct_0(sK5)
% 3.27/1.00      | sK4 != X0 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_827,c_39]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2196,plain,
% 3.27/1.00      ( ~ r1_tmap_1(sK5,sK4,sK6,X0)
% 3.27/1.00      | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0)
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.27/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK4))))
% 3.27/1.00      | v2_struct_0(sK4)
% 3.27/1.00      | ~ l1_pre_topc(sK4)
% 3.27/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_2195]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2200,plain,
% 3.27/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.27/1.00      | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0)
% 3.27/1.00      | ~ r1_tmap_1(sK5,sK4,sK6,X0)
% 3.27/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_2196,c_40,c_38,c_32]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2201,plain,
% 3.27/1.00      ( ~ r1_tmap_1(sK5,sK4,sK6,X0)
% 3.27/1.00      | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0)
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.27/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_2200]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9544,plain,
% 3.27/1.00      ( ~ r1_tmap_1(sK5,sK4,sK6,X0_55)
% 3.27/1.00      | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0_55)
% 3.27/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7))
% 3.27/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4) ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_2201]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_10752,plain,
% 3.27/1.00      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.27/1.00      | r1_tmap_1(sK5,sK4,sK6,X0_55) != iProver_top
% 3.27/1.00      | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0_55) = iProver_top
% 3.27/1.00      | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_9544]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_10956,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,sK4,sK6,X0_55) != iProver_top
% 3.27/1.00      | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),X0_55) = iProver_top
% 3.27/1.00      | m1_subset_1(X0_55,u1_struct_0(sK7)) != iProver_top ),
% 3.27/1.00      inference(equality_resolution_simp,[status(thm)],[c_10752]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_24,negated_conjecture,
% 3.27/1.00      ( ~ r1_tmap_1(sK5,sK4,sK6,sK8)
% 3.27/1.00      | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) ),
% 3.27/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9557,negated_conjecture,
% 3.27/1.00      ( ~ r1_tmap_1(sK5,sK4,sK6,sK8)
% 3.27/1.00      | ~ r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_10738,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,sK4,sK6,sK8) != iProver_top
% 3.27/1.00      | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_9557]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_26,negated_conjecture,
% 3.27/1.00      ( sK8 = sK9 ),
% 3.27/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9555,negated_conjecture,
% 3.27/1.00      ( sK8 = sK9 ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_26]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_10839,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,sK4,sK6,sK9) != iProver_top
% 3.27/1.00      | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) != iProver_top ),
% 3.27/1.00      inference(light_normalisation,[status(thm)],[c_10738,c_9555]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_13354,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,sK4,sK6,sK9) != iProver_top
% 3.27/1.00      | m1_subset_1(sK9,u1_struct_0(sK7)) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_10956,c_10839]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_13355,plain,
% 3.27/1.00      ( ~ r1_tmap_1(sK5,sK4,sK6,sK9)
% 3.27/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 3.27/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_13354]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4,plain,
% 3.27/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.27/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9558,plain,
% 3.27/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 3.27/1.00      | r1_tarski(X0_55,X1_55) ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11542,plain,
% 3.27/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK7)))
% 3.27/1.00      | r1_tarski(X0_55,u1_struct_0(sK7)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_9558]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_12983,plain,
% 3.27/1.00      ( ~ m1_subset_1(sK1(sK7,sK9),k1_zfmisc_1(u1_struct_0(sK7)))
% 3.27/1.00      | r1_tarski(sK1(sK7,sK9),u1_struct_0(sK7)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_11542]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2,plain,
% 3.27/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.27/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9560,plain,
% 3.27/1.00      ( ~ r2_hidden(X0_55,X1_55)
% 3.27/1.00      | r2_hidden(X0_55,X2_55)
% 3.27/1.00      | ~ r1_tarski(X1_55,X2_55) ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11666,plain,
% 3.27/1.00      ( r2_hidden(sK9,X0_55)
% 3.27/1.00      | ~ r2_hidden(sK9,sK1(sK7,sK9))
% 3.27/1.00      | ~ r1_tarski(sK1(sK7,sK9),X0_55) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_9560]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_12213,plain,
% 3.27/1.00      ( ~ r2_hidden(sK9,sK1(sK7,sK9))
% 3.27/1.00      | r2_hidden(sK9,u1_struct_0(sK7))
% 3.27/1.00      | ~ r1_tarski(sK1(sK7,sK9),u1_struct_0(sK7)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_11666]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_15,plain,
% 3.27/1.00      ( m1_connsp_2(sK3(X0,X1,X2),X0,X2)
% 3.27/1.00      | ~ v3_pre_topc(X1,X0)
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.27/1.00      | ~ r2_hidden(X2,X1)
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | ~ v2_pre_topc(X0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2150,plain,
% 3.27/1.00      ( m1_connsp_2(sK3(X0,X1,X2),X0,X2)
% 3.27/1.00      | ~ v3_pre_topc(X1,X0)
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.27/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.27/1.00      | ~ r2_hidden(X2,X1)
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | sK5 != X0 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_36]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2151,plain,
% 3.27/1.00      ( m1_connsp_2(sK3(sK5,X0,X1),sK5,X1)
% 3.27/1.00      | ~ v3_pre_topc(X0,sK5)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ r2_hidden(X1,X0)
% 3.27/1.00      | v2_struct_0(sK5)
% 3.27/1.00      | ~ l1_pre_topc(sK5) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_2150]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2155,plain,
% 3.27/1.00      ( m1_connsp_2(sK3(sK5,X0,X1),sK5,X1)
% 3.27/1.00      | ~ v3_pre_topc(X0,sK5)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ r2_hidden(X1,X0) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_2151,c_37,c_35]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9546,plain,
% 3.27/1.00      ( m1_connsp_2(sK3(sK5,X0_55,X1_55),sK5,X1_55)
% 3.27/1.00      | ~ v3_pre_topc(X0_55,sK5)
% 3.27/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK5))
% 3.27/1.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ r2_hidden(X1_55,X0_55) ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_2155]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11274,plain,
% 3.27/1.00      ( m1_connsp_2(sK3(sK5,u1_struct_0(sK7),X0_55),sK5,X0_55)
% 3.27/1.00      | ~ v3_pre_topc(u1_struct_0(sK7),sK5)
% 3.27/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 3.27/1.00      | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ r2_hidden(X0_55,u1_struct_0(sK7)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_9546]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11734,plain,
% 3.27/1.00      ( m1_connsp_2(sK3(sK5,u1_struct_0(sK7),sK9),sK5,sK9)
% 3.27/1.00      | ~ v3_pre_topc(u1_struct_0(sK7),sK5)
% 3.27/1.00      | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK5))
% 3.27/1.00      | ~ r2_hidden(sK9,u1_struct_0(sK7)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_11274]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_14,plain,
% 3.27/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.27/1.00      | ~ r2_hidden(X2,X0)
% 3.27/1.00      | r1_tarski(sK3(X1,X0,X2),X0)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X1) ),
% 3.27/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2453,plain,
% 3.27/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.27/1.00      | ~ r2_hidden(X2,X0)
% 3.27/1.00      | r1_tarski(sK3(X1,X0,X2),X0)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | sK5 != X1 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_36]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2454,plain,
% 3.27/1.00      ( ~ v3_pre_topc(X0,sK5)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ r2_hidden(X1,X0)
% 3.27/1.00      | r1_tarski(sK3(sK5,X0,X1),X0)
% 3.27/1.00      | v2_struct_0(sK5)
% 3.27/1.00      | ~ l1_pre_topc(sK5) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_2453]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2458,plain,
% 3.27/1.00      ( ~ v3_pre_topc(X0,sK5)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ r2_hidden(X1,X0)
% 3.27/1.00      | r1_tarski(sK3(sK5,X0,X1),X0) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_2454,c_37,c_35]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9534,plain,
% 3.27/1.00      ( ~ v3_pre_topc(X0_55,sK5)
% 3.27/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK5))
% 3.27/1.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ r2_hidden(X1_55,X0_55)
% 3.27/1.00      | r1_tarski(sK3(sK5,X0_55,X1_55),X0_55) ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_2458]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11269,plain,
% 3.27/1.00      ( ~ v3_pre_topc(u1_struct_0(sK7),sK5)
% 3.27/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 3.27/1.00      | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ r2_hidden(X0_55,u1_struct_0(sK7))
% 3.27/1.00      | r1_tarski(sK3(sK5,u1_struct_0(sK7),X0_55),u1_struct_0(sK7)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_9534]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11720,plain,
% 3.27/1.00      ( ~ v3_pre_topc(u1_struct_0(sK7),sK5)
% 3.27/1.00      | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK5))
% 3.27/1.00      | ~ r2_hidden(sK9,u1_struct_0(sK7))
% 3.27/1.00      | r1_tarski(sK3(sK5,u1_struct_0(sK7),sK9),u1_struct_0(sK7)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_11269]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_16,plain,
% 3.27/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.27/1.00      | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.27/1.00      | ~ r2_hidden(X2,X0)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X1) ),
% 3.27/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2426,plain,
% 3.27/1.00      ( ~ v3_pre_topc(X0,X1)
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.27/1.00      | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.27/1.00      | ~ r2_hidden(X2,X0)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | sK5 != X1 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_36]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2427,plain,
% 3.27/1.00      ( ~ v3_pre_topc(X0,sK5)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | m1_subset_1(sK3(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ r2_hidden(X1,X0)
% 3.27/1.00      | v2_struct_0(sK5)
% 3.27/1.00      | ~ l1_pre_topc(sK5) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_2426]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2431,plain,
% 3.27/1.00      ( ~ v3_pre_topc(X0,sK5)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK5))
% 3.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | m1_subset_1(sK3(sK5,X0,X1),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ r2_hidden(X1,X0) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_2427,c_37,c_35]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9535,plain,
% 3.27/1.00      ( ~ v3_pre_topc(X0_55,sK5)
% 3.27/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK5))
% 3.27/1.00      | ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | m1_subset_1(sK3(sK5,X0_55,X1_55),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ r2_hidden(X1_55,X0_55) ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_2431]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11256,plain,
% 3.27/1.00      ( ~ v3_pre_topc(u1_struct_0(sK7),sK5)
% 3.27/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK5))
% 3.27/1.00      | m1_subset_1(sK3(sK5,u1_struct_0(sK7),X0_55),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ r2_hidden(X0_55,u1_struct_0(sK7)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_9535]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11714,plain,
% 3.27/1.00      ( ~ v3_pre_topc(u1_struct_0(sK7),sK5)
% 3.27/1.00      | m1_subset_1(sK3(sK5,u1_struct_0(sK7),sK9),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK5))
% 3.27/1.00      | ~ r2_hidden(sK9,u1_struct_0(sK7)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_11256]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_10,plain,
% 3.27/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.27/1.00      | r2_hidden(X2,X0)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X1) ),
% 3.27/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_8,plain,
% 3.27/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.27/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X1) ),
% 3.27/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_244,plain,
% 3.27/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.27/1.00      | ~ m1_connsp_2(X0,X1,X2)
% 3.27/1.00      | r2_hidden(X2,X0)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X1) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_10,c_8]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_245,plain,
% 3.27/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.27/1.00      | r2_hidden(X2,X0)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X1) ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_244]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_5,plain,
% 3.27/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | v2_pre_topc(X0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_762,plain,
% 3.27/1.00      ( ~ l1_pre_topc(X0)
% 3.27/1.00      | ~ v2_pre_topc(X0)
% 3.27/1.00      | v2_pre_topc(X1)
% 3.27/1.00      | sK5 != X0
% 3.27/1.00      | sK7 != X1 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_29]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_763,plain,
% 3.27/1.00      ( ~ l1_pre_topc(sK5) | ~ v2_pre_topc(sK5) | v2_pre_topc(sK7) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_762]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_765,plain,
% 3.27/1.00      ( v2_pre_topc(sK7) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_763,c_36,c_35]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2735,plain,
% 3.27/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.27/1.00      | r2_hidden(X2,X0)
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | sK7 != X1 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_245,c_765]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2736,plain,
% 3.27/1.00      ( ~ m1_connsp_2(X0,sK7,X1)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.27/1.00      | r2_hidden(X1,X0)
% 3.27/1.00      | v2_struct_0(sK7)
% 3.27/1.00      | ~ l1_pre_topc(sK7) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_2735]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_6,plain,
% 3.27/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_751,plain,
% 3.27/1.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK5 != X0 | sK7 != X1 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_29]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_752,plain,
% 3.27/1.00      ( ~ l1_pre_topc(sK5) | l1_pre_topc(sK7) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_751]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2740,plain,
% 3.27/1.00      ( ~ m1_connsp_2(X0,sK7,X1)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.27/1.00      | r2_hidden(X1,X0) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_2736,c_35,c_31,c_752]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9522,plain,
% 3.27/1.00      ( ~ m1_connsp_2(X0_55,sK7,X1_55)
% 3.27/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK7))
% 3.27/1.00      | r2_hidden(X1_55,X0_55) ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_2740]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11294,plain,
% 3.27/1.00      ( ~ m1_connsp_2(X0_55,sK7,sK9)
% 3.27/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK7))
% 3.27/1.00      | r2_hidden(sK9,X0_55) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_9522]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11432,plain,
% 3.27/1.00      ( ~ m1_connsp_2(sK1(sK7,sK9),sK7,sK9)
% 3.27/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK7))
% 3.27/1.00      | r2_hidden(sK9,sK1(sK7,sK9)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_11294]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2879,plain,
% 3.27/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 3.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.27/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.27/1.00      | v2_struct_0(X1)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | sK7 != X1 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_765]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2880,plain,
% 3.27/1.00      ( ~ m1_connsp_2(X0,sK7,X1)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.27/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
% 3.27/1.00      | v2_struct_0(sK7)
% 3.27/1.00      | ~ l1_pre_topc(sK7) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_2879]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2884,plain,
% 3.27/1.00      ( ~ m1_connsp_2(X0,sK7,X1)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 3.27/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7))) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_2880,c_35,c_31,c_752]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9516,plain,
% 3.27/1.00      ( ~ m1_connsp_2(X0_55,sK7,X1_55)
% 3.27/1.00      | ~ m1_subset_1(X1_55,u1_struct_0(sK7))
% 3.27/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK7))) ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_2884]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11285,plain,
% 3.27/1.00      ( ~ m1_connsp_2(X0_55,sK7,sK9)
% 3.27/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK7)))
% 3.27/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_9516]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11421,plain,
% 3.27/1.00      ( ~ m1_connsp_2(sK1(sK7,sK9),sK7,sK9)
% 3.27/1.00      | m1_subset_1(sK1(sK7,sK9),k1_zfmisc_1(u1_struct_0(sK7)))
% 3.27/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_11285]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9,plain,
% 3.27/1.00      ( m1_connsp_2(sK1(X0,X1),X0,X1)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | ~ v2_pre_topc(X0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2387,plain,
% 3.27/1.00      ( m1_connsp_2(sK1(X0,X1),X0,X1)
% 3.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.27/1.00      | v2_struct_0(X0)
% 3.27/1.00      | ~ l1_pre_topc(X0)
% 3.27/1.00      | sK7 != X0 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_765]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2388,plain,
% 3.27/1.00      ( m1_connsp_2(sK1(sK7,X0),sK7,X0)
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 3.27/1.00      | v2_struct_0(sK7)
% 3.27/1.00      | ~ l1_pre_topc(sK7) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_2387]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2392,plain,
% 3.27/1.00      ( m1_connsp_2(sK1(sK7,X0),sK7,X0)
% 3.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK7)) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_2388,c_35,c_31,c_752]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9537,plain,
% 3.27/1.00      ( m1_connsp_2(sK1(sK7,X0_55),sK7,X0_55)
% 3.27/1.00      | ~ m1_subset_1(X0_55,u1_struct_0(sK7)) ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_2392]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11279,plain,
% 3.27/1.00      ( m1_connsp_2(sK1(sK7,sK9),sK7,sK9)
% 3.27/1.00      | ~ m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_9537]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_28,negated_conjecture,
% 3.27/1.00      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 3.27/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9553,negated_conjecture,
% 3.27/1.00      ( m1_subset_1(sK8,u1_struct_0(sK5)) ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_28]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_10741,plain,
% 3.27/1.00      ( m1_subset_1(sK8,u1_struct_0(sK5)) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_9553]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_10787,plain,
% 3.27/1.00      ( m1_subset_1(sK9,u1_struct_0(sK5)) = iProver_top ),
% 3.27/1.00      inference(light_normalisation,[status(thm)],[c_10741,c_9555]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11150,plain,
% 3.27/1.00      ( m1_subset_1(sK9,u1_struct_0(sK5)) ),
% 3.27/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_10787]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_25,negated_conjecture,
% 3.27/1.00      ( r1_tmap_1(sK5,sK4,sK6,sK8)
% 3.27/1.00      | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) ),
% 3.27/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9556,negated_conjecture,
% 3.27/1.00      ( r1_tmap_1(sK5,sK4,sK6,sK8)
% 3.27/1.00      | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) ),
% 3.27/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_10739,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,sK4,sK6,sK8) = iProver_top
% 3.27/1.00      | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_9556]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_10834,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,sK4,sK6,sK9) = iProver_top
% 3.27/1.00      | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) = iProver_top ),
% 3.27/1.00      inference(light_normalisation,[status(thm)],[c_10739,c_9555]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11134,plain,
% 3.27/1.00      ( r1_tmap_1(sK5,sK4,sK6,sK9)
% 3.27/1.00      | r1_tmap_1(sK7,sK4,k2_tmap_1(sK5,sK4,sK6,sK7),sK9) ),
% 3.27/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_10834]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_20,plain,
% 3.27/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.27/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.27/1.00      | ~ l1_pre_topc(X1) ),
% 3.27/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_722,plain,
% 3.27/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | sK5 != X1
% 3.27/1.00      | sK7 != X0 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_723,plain,
% 3.27/1.00      ( m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.27/1.00      | ~ l1_pre_topc(sK5) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_722]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_19,plain,
% 3.27/1.00      ( ~ v1_tsep_1(X0,X1)
% 3.27/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.27/1.00      | ~ m1_pre_topc(X0,X1)
% 3.27/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X1) ),
% 3.27/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_224,plain,
% 3.27/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.27/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.27/1.00      | ~ v1_tsep_1(X0,X1)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X1) ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_19,c_20]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_225,plain,
% 3.27/1.00      ( ~ v1_tsep_1(X0,X1)
% 3.27/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 3.27/1.00      | ~ m1_pre_topc(X0,X1)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X1) ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_224]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_30,negated_conjecture,
% 3.27/1.00      ( v1_tsep_1(sK7,sK5) ),
% 3.27/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_535,plain,
% 3.27/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 3.27/1.00      | ~ m1_pre_topc(X0,X1)
% 3.27/1.00      | ~ l1_pre_topc(X1)
% 3.27/1.00      | ~ v2_pre_topc(X1)
% 3.27/1.00      | sK5 != X1
% 3.27/1.00      | sK7 != X0 ),
% 3.27/1.00      inference(resolution_lifted,[status(thm)],[c_225,c_30]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_536,plain,
% 3.27/1.00      ( v3_pre_topc(u1_struct_0(sK7),sK5)
% 3.27/1.00      | ~ m1_pre_topc(sK7,sK5)
% 3.27/1.00      | ~ l1_pre_topc(sK5)
% 3.27/1.00      | ~ v2_pre_topc(sK5) ),
% 3.27/1.00      inference(unflattening,[status(thm)],[c_535]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_27,negated_conjecture,
% 3.27/1.00      ( m1_subset_1(sK9,u1_struct_0(sK7)) ),
% 3.27/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(contradiction,plain,
% 3.27/1.00      ( $false ),
% 3.27/1.00      inference(minisat,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_13496,c_13355,c_12983,c_12213,c_11734,c_11720,c_11714,
% 3.27/1.00                 c_11432,c_11421,c_11279,c_11150,c_11134,c_723,c_536,
% 3.27/1.00                 c_27,c_29,c_35,c_36]) ).
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.27/1.00  
% 3.27/1.00  ------                               Statistics
% 3.27/1.00  
% 3.27/1.00  ------ General
% 3.27/1.00  
% 3.27/1.00  abstr_ref_over_cycles:                  0
% 3.27/1.00  abstr_ref_under_cycles:                 0
% 3.27/1.00  gc_basic_clause_elim:                   0
% 3.27/1.00  forced_gc_time:                         0
% 3.27/1.00  parsing_time:                           0.014
% 3.27/1.00  unif_index_cands_time:                  0.
% 3.27/1.00  unif_index_add_time:                    0.
% 3.27/1.00  orderings_time:                         0.
% 3.27/1.00  out_proof_time:                         0.016
% 3.27/1.00  total_time:                             0.333
% 3.27/1.00  num_of_symbols:                         64
% 3.27/1.00  num_of_terms:                           6605
% 3.27/1.00  
% 3.27/1.00  ------ Preprocessing
% 3.27/1.00  
% 3.27/1.00  num_of_splits:                          4
% 3.27/1.00  num_of_split_atoms:                     4
% 3.27/1.00  num_of_reused_defs:                     0
% 3.27/1.00  num_eq_ax_congr_red:                    30
% 3.27/1.00  num_of_sem_filtered_clauses:            1
% 3.27/1.00  num_of_subtypes:                        2
% 3.27/1.00  monotx_restored_types:                  0
% 3.27/1.00  sat_num_of_epr_types:                   0
% 3.27/1.00  sat_num_of_non_cyclic_types:            0
% 3.27/1.00  sat_guarded_non_collapsed_types:        0
% 3.27/1.00  num_pure_diseq_elim:                    0
% 3.27/1.00  simp_replaced_by:                       0
% 3.27/1.00  res_preprocessed:                       165
% 3.27/1.00  prep_upred:                             0
% 3.27/1.00  prep_unflattend:                        404
% 3.27/1.00  smt_new_axioms:                         0
% 3.27/1.00  pred_elim_cands:                        13
% 3.27/1.00  pred_elim:                              7
% 3.27/1.00  pred_elim_cl:                           -7
% 3.27/1.00  pred_elim_cycles:                       13
% 3.27/1.00  merged_defs:                            12
% 3.27/1.00  merged_defs_ncl:                        0
% 3.27/1.00  bin_hyper_res:                          12
% 3.27/1.00  prep_cycles:                            3
% 3.27/1.00  pred_elim_time:                         0.182
% 3.27/1.00  splitting_time:                         0.
% 3.27/1.00  sem_filter_time:                        0.
% 3.27/1.00  monotx_time:                            0.
% 3.27/1.00  subtype_inf_time:                       0.
% 3.27/1.00  
% 3.27/1.00  ------ Problem properties
% 3.27/1.00  
% 3.27/1.00  clauses:                                51
% 3.27/1.00  conjectures:                            6
% 3.27/1.00  epr:                                    2
% 3.27/1.00  horn:                                   43
% 3.27/1.00  ground:                                 12
% 3.27/1.00  unary:                                  6
% 3.27/1.00  binary:                                 10
% 3.27/1.00  lits:                                   170
% 3.27/1.00  lits_eq:                                7
% 3.27/1.00  fd_pure:                                0
% 3.27/1.00  fd_pseudo:                              0
% 3.27/1.00  fd_cond:                                0
% 3.27/1.00  fd_pseudo_cond:                         0
% 3.27/1.00  ac_symbols:                             0
% 3.27/1.00  
% 3.27/1.00  ------ Propositional Solver
% 3.27/1.00  
% 3.27/1.00  prop_solver_calls:                      23
% 3.27/1.00  prop_fast_solver_calls:                 3713
% 3.27/1.00  smt_solver_calls:                       0
% 3.27/1.00  smt_fast_solver_calls:                  0
% 3.27/1.00  prop_num_of_clauses:                    2758
% 3.27/1.00  prop_preprocess_simplified:             7496
% 3.27/1.00  prop_fo_subsumed:                       153
% 3.27/1.00  prop_solver_time:                       0.
% 3.27/1.00  smt_solver_time:                        0.
% 3.27/1.00  smt_fast_solver_time:                   0.
% 3.27/1.00  prop_fast_solver_time:                  0.
% 3.27/1.00  prop_unsat_core_time:                   0.
% 3.27/1.00  
% 3.27/1.00  ------ QBF
% 3.27/1.00  
% 3.27/1.00  qbf_q_res:                              0
% 3.27/1.00  qbf_num_tautologies:                    0
% 3.27/1.00  qbf_prep_cycles:                        0
% 3.27/1.00  
% 3.27/1.00  ------ BMC1
% 3.27/1.00  
% 3.27/1.00  bmc1_current_bound:                     -1
% 3.27/1.00  bmc1_last_solved_bound:                 -1
% 3.27/1.00  bmc1_unsat_core_size:                   -1
% 3.27/1.00  bmc1_unsat_core_parents_size:           -1
% 3.27/1.00  bmc1_merge_next_fun:                    0
% 3.27/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.27/1.00  
% 3.27/1.00  ------ Instantiation
% 3.27/1.00  
% 3.27/1.00  inst_num_of_clauses:                    387
% 3.27/1.00  inst_num_in_passive:                    66
% 3.27/1.00  inst_num_in_active:                     284
% 3.27/1.00  inst_num_in_unprocessed:                36
% 3.27/1.00  inst_num_of_loops:                      355
% 3.27/1.00  inst_num_of_learning_restarts:          0
% 3.27/1.00  inst_num_moves_active_passive:          67
% 3.27/1.00  inst_lit_activity:                      0
% 3.27/1.00  inst_lit_activity_moves:                0
% 3.27/1.00  inst_num_tautologies:                   0
% 3.27/1.00  inst_num_prop_implied:                  0
% 3.27/1.00  inst_num_existing_simplified:           0
% 3.27/1.00  inst_num_eq_res_simplified:             0
% 3.27/1.00  inst_num_child_elim:                    0
% 3.27/1.00  inst_num_of_dismatching_blockings:      51
% 3.27/1.00  inst_num_of_non_proper_insts:           333
% 3.27/1.00  inst_num_of_duplicates:                 0
% 3.27/1.00  inst_inst_num_from_inst_to_res:         0
% 3.27/1.00  inst_dismatching_checking_time:         0.
% 3.27/1.00  
% 3.27/1.00  ------ Resolution
% 3.27/1.00  
% 3.27/1.00  res_num_of_clauses:                     0
% 3.27/1.00  res_num_in_passive:                     0
% 3.27/1.00  res_num_in_active:                      0
% 3.27/1.00  res_num_of_loops:                       168
% 3.27/1.00  res_forward_subset_subsumed:            44
% 3.27/1.00  res_backward_subset_subsumed:           2
% 3.27/1.00  res_forward_subsumed:                   5
% 3.27/1.00  res_backward_subsumed:                  4
% 3.27/1.00  res_forward_subsumption_resolution:     17
% 3.27/1.00  res_backward_subsumption_resolution:    6
% 3.27/1.00  res_clause_to_clause_subsumption:       1572
% 3.27/1.00  res_orphan_elimination:                 0
% 3.27/1.00  res_tautology_del:                      79
% 3.27/1.00  res_num_eq_res_simplified:              2
% 3.27/1.00  res_num_sel_changes:                    0
% 3.27/1.00  res_moves_from_active_to_pass:          0
% 3.27/1.00  
% 3.27/1.00  ------ Superposition
% 3.27/1.00  
% 3.27/1.00  sup_time_total:                         0.
% 3.27/1.00  sup_time_generating:                    0.
% 3.27/1.00  sup_time_sim_full:                      0.
% 3.27/1.00  sup_time_sim_immed:                     0.
% 3.27/1.00  
% 3.27/1.00  sup_num_of_clauses:                     100
% 3.27/1.00  sup_num_in_active:                      69
% 3.27/1.00  sup_num_in_passive:                     31
% 3.27/1.00  sup_num_of_loops:                       70
% 3.27/1.00  sup_fw_superposition:                   30
% 3.27/1.00  sup_bw_superposition:                   33
% 3.27/1.00  sup_immediate_simplified:               1
% 3.27/1.00  sup_given_eliminated:                   0
% 3.27/1.00  comparisons_done:                       0
% 3.27/1.00  comparisons_avoided:                    0
% 3.27/1.00  
% 3.27/1.00  ------ Simplifications
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  sim_fw_subset_subsumed:                 1
% 3.27/1.00  sim_bw_subset_subsumed:                 2
% 3.27/1.00  sim_fw_subsumed:                        0
% 3.27/1.00  sim_bw_subsumed:                        0
% 3.27/1.00  sim_fw_subsumption_res:                 0
% 3.27/1.00  sim_bw_subsumption_res:                 0
% 3.27/1.00  sim_tautology_del:                      3
% 3.27/1.00  sim_eq_tautology_del:                   0
% 3.27/1.00  sim_eq_res_simp:                        2
% 3.27/1.00  sim_fw_demodulated:                     0
% 3.27/1.00  sim_bw_demodulated:                     0
% 3.27/1.00  sim_light_normalised:                   3
% 3.27/1.00  sim_joinable_taut:                      0
% 3.27/1.00  sim_joinable_simp:                      0
% 3.27/1.00  sim_ac_normalised:                      0
% 3.27/1.00  sim_smt_subsumption:                    0
% 3.27/1.00  
%------------------------------------------------------------------------------
