%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:42 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  263 (1335 expanded)
%              Number of clauses        :  168 ( 253 expanded)
%              Number of leaves         :   26 ( 517 expanded)
%              Depth                    :   27
%              Number of atoms          : 1709 (20749 expanded)
%              Number of equality atoms :  196 (1537 expanded)
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

fof(f49,plain,(
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
    inference(flattening,[],[f49])).

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,
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

fof(f57,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f50,f56,f55,f54,f53,f52,f51])).

fof(f90,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f57])).

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
    inference(flattening,[],[f40])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f41])).

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
    inference(cnf_transformation,[],[f48])).

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
    inference(cnf_transformation,[],[f57])).

fof(f85,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f83,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f84,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f80,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

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

fof(f59,plain,(
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

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
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
    inference(equality_resolution,[],[f77])).

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
    inference(cnf_transformation,[],[f39])).

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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f44])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK0(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK0(X0,X1,X2),X0,X1)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f31,plain,(
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
    inference(flattening,[],[f31])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f60,plain,(
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

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | r1_tmap_1(sK2,sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f57])).

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

fof(f75,plain,(
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

fof(f46,plain,(
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
    inference(flattening,[],[f46])).

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
    inference(cnf_transformation,[],[f47])).

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
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,
    ( ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ r1_tmap_1(sK2,sK1,sK3,sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f90])).

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
    inference(cnf_transformation,[],[f100])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_883,plain,
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
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_884,plain,
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
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_883])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_888,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_connsp_2(X4,X2,X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_884,c_31])).

cnf(c_889,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_888])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_930,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_889,c_4])).

cnf(c_1099,plain,
    ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_connsp_2(X4,X2,X3)
    | ~ r1_tarski(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_930])).

cnf(c_1100,plain,
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
    inference(unflattening,[status(thm)],[c_1099])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1104,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1100,c_34,c_33,c_32,c_28])).

cnf(c_1105,plain,
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
    inference(renaming,[status(thm)],[c_1104])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1344,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1105,c_36])).

cnf(c_1345,plain,
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
    inference(unflattening,[status(thm)],[c_1344])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1349,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | ~ m1_connsp_2(X1,sK2,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | r1_tmap_1(sK2,sK1,sK3,X0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1345,c_37,c_35,c_29])).

cnf(c_1350,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_connsp_2(X1,sK2,X0)
    | ~ r1_tarski(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1349])).

cnf(c_3389,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0_54)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
    | ~ m1_connsp_2(X1_54,sK2,X0_54)
    | ~ r1_tarski(X1_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_1350])).

cnf(c_3635,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0_54)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
    | ~ m1_connsp_2(X1_54,sK2,X0_54)
    | ~ r1_tarski(X1_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(equality_resolution_simp,[status(thm)],[c_3389])).

cnf(c_5987,plain,
    ( r1_tmap_1(sK2,sK1,sK3,X0_54)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
    | ~ m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,X0_54)
    | ~ r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK2,sK5,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3635])).

cnf(c_6419,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
    | ~ m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,sK5)
    | ~ r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK2,sK5,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5987])).

cnf(c_6420,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5) != iProver_top
    | m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,sK5) != iProver_top
    | r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK0(sK2,sK5,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6419])).

cnf(c_3423,plain,
    ( ~ r1_tmap_1(X0_55,X1_55,X0_54,X1_54)
    | r1_tmap_1(X0_55,X1_55,X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_5143,plain,
    ( r1_tmap_1(sK4,sK1,X0_54,X1_54)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | X0_54 != k2_tmap_1(sK2,sK1,sK3,sK4)
    | X1_54 != sK6 ),
    inference(instantiation,[status(thm)],[c_3423])).

cnf(c_5337,plain,
    ( r1_tmap_1(sK4,sK1,X0_54,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | X0_54 != k2_tmap_1(sK2,sK1,sK3,sK4)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_5143])).

cnf(c_6406,plain,
    ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | k2_tmap_1(sK2,sK1,sK3,sK4) != k2_tmap_1(sK2,sK1,sK3,sK4)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_5337])).

cnf(c_6408,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK4) != k2_tmap_1(sK2,sK1,sK3,sK4)
    | sK5 != sK6
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6406])).

cnf(c_3422,plain,
    ( X0_54 != X1_54
    | k2_tmap_1(X0_55,X1_55,X0_54,X2_55) = k2_tmap_1(X0_55,X1_55,X1_54,X2_55) ),
    theory(equality)).

cnf(c_5721,plain,
    ( X0_54 != sK3
    | k2_tmap_1(sK2,sK1,X0_54,sK4) = k2_tmap_1(sK2,sK1,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3422])).

cnf(c_5724,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK4) = k2_tmap_1(sK2,sK1,sK3,sK4)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_5721])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3402,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ r2_hidden(X2_54,X0_54)
    | ~ v1_xboole_0(X1_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_5225,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1_54,X0_54)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3402])).

cnf(c_5454,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0_54,k1_connsp_2(sK4,sK6))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5225])).

cnf(c_5703,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK6,k1_connsp_2(sK4,sK6))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5454])).

cnf(c_5704,plain,
    ( m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK6,k1_connsp_2(sK4,sK6)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5703])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3403,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | r2_hidden(X0_54,X1_54)
    | v1_xboole_0(X1_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_5656,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | r2_hidden(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3403])).

cnf(c_5657,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5656])).

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
    inference(cnf_transformation,[],[f101])).

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
    inference(cnf_transformation,[],[f99])).

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

cnf(c_826,plain,
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
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_201,c_30])).

cnf(c_827,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(sK3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_826])).

cnf(c_831,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X2)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_827,c_31])).

cnf(c_832,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_831])).

cnf(c_867,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_832,c_4])).

cnf(c_1147,plain,
    ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
    | ~ r1_tmap_1(X2,X1,sK3,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | sK2 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_867])).

cnf(c_1148,plain,
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
    inference(unflattening,[status(thm)],[c_1147])).

cnf(c_1152,plain,
    ( ~ v2_pre_topc(X0)
    | ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1148,c_34,c_33,c_32,c_28])).

cnf(c_1153,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1152])).

cnf(c_1320,plain,
    ( ~ r1_tmap_1(sK2,X0,sK3,X1)
    | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1153,c_36])).

cnf(c_1321,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1320])).

cnf(c_1325,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1321,c_37,c_35,c_29])).

cnf(c_1326,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1325])).

cnf(c_3390,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0_54)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_1326])).

cnf(c_3631,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,X0_54)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
    inference(equality_resolution_simp,[status(thm)],[c_3390])).

cnf(c_5615,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3631])).

cnf(c_5623,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5615])).

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
    inference(cnf_transformation,[],[f64])).

cnf(c_250,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_6])).

cnf(c_251,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_250])).

cnf(c_1440,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r1_tarski(sK0(X1,X2,X0),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_251,c_33])).

cnf(c_1441,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | r1_tarski(sK0(sK2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1440])).

cnf(c_1445,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | r1_tarski(sK0(sK2,X1,X0),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1441,c_34,c_32])).

cnf(c_3386,plain,
    ( ~ m1_connsp_2(X0_54,sK2,X1_54)
    | r1_tarski(sK0(sK2,X1_54,X0_54),X0_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1445])).

cnf(c_4993,plain,
    ( ~ m1_connsp_2(X0_54,sK2,sK5)
    | r1_tarski(sK0(sK2,sK5,X0_54),X0_54)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3386])).

cnf(c_5575,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK5)
    | r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4993])).

cnf(c_5589,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK2,sK5) != iProver_top
    | r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5575])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_6])).

cnf(c_237,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_236])).

cnf(c_1482,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_237,c_33])).

cnf(c_1483,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | m1_connsp_2(sK0(sK2,X1,X0),sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1482])).

cnf(c_1487,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | m1_connsp_2(sK0(sK2,X1,X0),sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1483,c_34,c_32])).

cnf(c_3384,plain,
    ( ~ m1_connsp_2(X0_54,sK2,X1_54)
    | m1_connsp_2(sK0(sK2,X1_54,X0_54),sK2,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_1487])).

cnf(c_4988,plain,
    ( ~ m1_connsp_2(X0_54,sK2,sK5)
    | m1_connsp_2(sK0(sK2,sK5,X0_54),sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3384])).

cnf(c_5576,plain,
    ( m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,sK5)
    | ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4988])).

cnf(c_5587,plain,
    ( m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,sK5) = iProver_top
    | m1_connsp_2(u1_struct_0(sK4),sK2,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5576])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_6])).

cnf(c_230,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_1503,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_230,c_33])).

cnf(c_1504,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1503])).

cnf(c_1508,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1504,c_34,c_32])).

cnf(c_3383,plain,
    ( ~ m1_connsp_2(X0_54,sK2,X1_54)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X1_54,X0_54),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_1508])).

cnf(c_4978,plain,
    ( ~ m1_connsp_2(X0_54,sK2,sK5)
    | m1_subset_1(sK0(sK2,sK5,X0_54),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3383])).

cnf(c_5578,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK5)
    | m1_subset_1(sK0(sK2,sK5,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4978])).

cnf(c_5583,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK2,sK5) != iProver_top
    | m1_subset_1(sK0(sK2,sK5,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5578])).

cnf(c_8,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1545,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_33])).

cnf(c_1546,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1545])).

cnf(c_1550,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1546,c_34,c_32])).

cnf(c_3381,plain,
    ( m1_connsp_2(X0_54,sK2,X1_54)
    | ~ v3_pre_topc(X0_54,sK2)
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_1550])).

cnf(c_5006,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK2,X0_54)
    | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0_54,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3381])).

cnf(c_5502,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK2,sK5)
    | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ r2_hidden(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5006])).

cnf(c_5503,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK2,sK5) = iProver_top
    | v3_pre_topc(u1_struct_0(sK4),sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5502])).

cnf(c_3413,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_5332,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3413])).

cnf(c_3417,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | m1_subset_1(X2_54,X3_54)
    | X2_54 != X0_54
    | X3_54 != X1_54 ),
    theory(equality)).

cnf(c_5123,plain,
    ( m1_subset_1(X0_54,X1_54)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | X1_54 != u1_struct_0(sK4)
    | X0_54 != sK6 ),
    inference(instantiation,[status(thm)],[c_3417])).

cnf(c_5270,plain,
    ( m1_subset_1(sK5,X0_54)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | X0_54 != u1_struct_0(sK4)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_5123])).

cnf(c_5331,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_5270])).

cnf(c_5333,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK5 != sK6
    | m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5331])).

cnf(c_5017,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3631])).

cnf(c_5018,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5017])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1088,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_26])).

cnf(c_1089,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1088])).

cnf(c_1091,plain,
    ( v2_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1089,c_33,c_32])).

cnf(c_1950,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_1091])).

cnf(c_1951,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k1_connsp_2(sK4,X0))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1950])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1077,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_1078,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1077])).

cnf(c_1955,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X0,k1_connsp_2(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1951,c_32,c_28,c_1078])).

cnf(c_3362,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | r2_hidden(X0_54,k1_connsp_2(sK4,X0_54)) ),
    inference(subtyping,[status(esa)],[c_1955])).

cnf(c_5014,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | r2_hidden(sK6,k1_connsp_2(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_3362])).

cnf(c_5015,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK6,k1_connsp_2(sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5014])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1989,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_1091])).

cnf(c_1990,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_1989])).

cnf(c_1994,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1990,c_32,c_28,c_1078])).

cnf(c_3360,plain,
    ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
    | m1_subset_1(k1_connsp_2(sK4,X0_54),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(subtyping,[status(esa)],[c_1994])).

cnf(c_5011,plain,
    ( m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3360])).

cnf(c_5012,plain,
    ( m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5011])).

cnf(c_22,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,sK3,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3400,negated_conjecture,
    ( r1_tmap_1(sK2,sK1,sK3,sK5)
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_4518,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3400])).

cnf(c_23,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3399,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_4609,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4518,c_3399])).

cnf(c_3436,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_3413])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1048,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_1049,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1048])).

cnf(c_1050,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1049])).

cnf(c_16,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

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
    ( v1_tsep_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_561,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_209,c_27])).

cnf(c_562,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_563,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK2) = iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
    | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_53,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5) != iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_52,plain,
    ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
    | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_51,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_50,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_49,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_43,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6420,c_6408,c_5724,c_5704,c_5657,c_5623,c_5589,c_5587,c_5583,c_5503,c_5332,c_5333,c_5018,c_5015,c_5012,c_4609,c_3399,c_3436,c_1050,c_563,c_53,c_52,c_51,c_50,c_49,c_43,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:30:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.27/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/0.99  
% 2.27/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.27/0.99  
% 2.27/0.99  ------  iProver source info
% 2.27/0.99  
% 2.27/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.27/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.27/0.99  git: non_committed_changes: false
% 2.27/0.99  git: last_make_outside_of_git: false
% 2.27/0.99  
% 2.27/0.99  ------ 
% 2.27/0.99  
% 2.27/0.99  ------ Input Options
% 2.27/0.99  
% 2.27/0.99  --out_options                           all
% 2.27/0.99  --tptp_safe_out                         true
% 2.27/0.99  --problem_path                          ""
% 2.27/0.99  --include_path                          ""
% 2.27/0.99  --clausifier                            res/vclausify_rel
% 2.27/0.99  --clausifier_options                    --mode clausify
% 2.27/0.99  --stdin                                 false
% 2.27/0.99  --stats_out                             all
% 2.27/0.99  
% 2.27/0.99  ------ General Options
% 2.27/0.99  
% 2.27/0.99  --fof                                   false
% 2.27/0.99  --time_out_real                         305.
% 2.27/0.99  --time_out_virtual                      -1.
% 2.27/0.99  --symbol_type_check                     false
% 2.27/0.99  --clausify_out                          false
% 2.27/0.99  --sig_cnt_out                           false
% 2.27/0.99  --trig_cnt_out                          false
% 2.27/0.99  --trig_cnt_out_tolerance                1.
% 2.27/0.99  --trig_cnt_out_sk_spl                   false
% 2.27/0.99  --abstr_cl_out                          false
% 2.27/0.99  
% 2.27/0.99  ------ Global Options
% 2.27/0.99  
% 2.27/0.99  --schedule                              default
% 2.27/0.99  --add_important_lit                     false
% 2.27/0.99  --prop_solver_per_cl                    1000
% 2.27/0.99  --min_unsat_core                        false
% 2.27/0.99  --soft_assumptions                      false
% 2.27/0.99  --soft_lemma_size                       3
% 2.27/0.99  --prop_impl_unit_size                   0
% 2.27/0.99  --prop_impl_unit                        []
% 2.27/0.99  --share_sel_clauses                     true
% 2.27/0.99  --reset_solvers                         false
% 2.27/0.99  --bc_imp_inh                            [conj_cone]
% 2.27/0.99  --conj_cone_tolerance                   3.
% 2.27/0.99  --extra_neg_conj                        none
% 2.27/0.99  --large_theory_mode                     true
% 2.27/0.99  --prolific_symb_bound                   200
% 2.27/0.99  --lt_threshold                          2000
% 2.27/0.99  --clause_weak_htbl                      true
% 2.27/0.99  --gc_record_bc_elim                     false
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing Options
% 2.27/0.99  
% 2.27/0.99  --preprocessing_flag                    true
% 2.27/0.99  --time_out_prep_mult                    0.1
% 2.27/0.99  --splitting_mode                        input
% 2.27/0.99  --splitting_grd                         true
% 2.27/0.99  --splitting_cvd                         false
% 2.27/0.99  --splitting_cvd_svl                     false
% 2.27/0.99  --splitting_nvd                         32
% 2.27/0.99  --sub_typing                            true
% 2.27/0.99  --prep_gs_sim                           true
% 2.27/0.99  --prep_unflatten                        true
% 2.27/0.99  --prep_res_sim                          true
% 2.27/0.99  --prep_upred                            true
% 2.27/0.99  --prep_sem_filter                       exhaustive
% 2.27/0.99  --prep_sem_filter_out                   false
% 2.27/0.99  --pred_elim                             true
% 2.27/0.99  --res_sim_input                         true
% 2.27/0.99  --eq_ax_congr_red                       true
% 2.27/0.99  --pure_diseq_elim                       true
% 2.27/0.99  --brand_transform                       false
% 2.27/0.99  --non_eq_to_eq                          false
% 2.27/0.99  --prep_def_merge                        true
% 2.27/0.99  --prep_def_merge_prop_impl              false
% 2.27/0.99  --prep_def_merge_mbd                    true
% 2.27/0.99  --prep_def_merge_tr_red                 false
% 2.27/0.99  --prep_def_merge_tr_cl                  false
% 2.27/0.99  --smt_preprocessing                     true
% 2.27/0.99  --smt_ac_axioms                         fast
% 2.27/0.99  --preprocessed_out                      false
% 2.27/0.99  --preprocessed_stats                    false
% 2.27/0.99  
% 2.27/0.99  ------ Abstraction refinement Options
% 2.27/0.99  
% 2.27/0.99  --abstr_ref                             []
% 2.27/0.99  --abstr_ref_prep                        false
% 2.27/0.99  --abstr_ref_until_sat                   false
% 2.27/0.99  --abstr_ref_sig_restrict                funpre
% 2.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/0.99  --abstr_ref_under                       []
% 2.27/0.99  
% 2.27/0.99  ------ SAT Options
% 2.27/0.99  
% 2.27/0.99  --sat_mode                              false
% 2.27/0.99  --sat_fm_restart_options                ""
% 2.27/0.99  --sat_gr_def                            false
% 2.27/0.99  --sat_epr_types                         true
% 2.27/0.99  --sat_non_cyclic_types                  false
% 2.27/0.99  --sat_finite_models                     false
% 2.27/0.99  --sat_fm_lemmas                         false
% 2.27/0.99  --sat_fm_prep                           false
% 2.27/0.99  --sat_fm_uc_incr                        true
% 2.27/0.99  --sat_out_model                         small
% 2.27/0.99  --sat_out_clauses                       false
% 2.27/0.99  
% 2.27/0.99  ------ QBF Options
% 2.27/0.99  
% 2.27/0.99  --qbf_mode                              false
% 2.27/0.99  --qbf_elim_univ                         false
% 2.27/0.99  --qbf_dom_inst                          none
% 2.27/0.99  --qbf_dom_pre_inst                      false
% 2.27/0.99  --qbf_sk_in                             false
% 2.27/0.99  --qbf_pred_elim                         true
% 2.27/0.99  --qbf_split                             512
% 2.27/0.99  
% 2.27/0.99  ------ BMC1 Options
% 2.27/0.99  
% 2.27/0.99  --bmc1_incremental                      false
% 2.27/0.99  --bmc1_axioms                           reachable_all
% 2.27/0.99  --bmc1_min_bound                        0
% 2.27/0.99  --bmc1_max_bound                        -1
% 2.27/0.99  --bmc1_max_bound_default                -1
% 2.27/0.99  --bmc1_symbol_reachability              true
% 2.27/0.99  --bmc1_property_lemmas                  false
% 2.27/0.99  --bmc1_k_induction                      false
% 2.27/0.99  --bmc1_non_equiv_states                 false
% 2.27/0.99  --bmc1_deadlock                         false
% 2.27/0.99  --bmc1_ucm                              false
% 2.27/0.99  --bmc1_add_unsat_core                   none
% 2.27/0.99  --bmc1_unsat_core_children              false
% 2.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/0.99  --bmc1_out_stat                         full
% 2.27/0.99  --bmc1_ground_init                      false
% 2.27/0.99  --bmc1_pre_inst_next_state              false
% 2.27/0.99  --bmc1_pre_inst_state                   false
% 2.27/0.99  --bmc1_pre_inst_reach_state             false
% 2.27/0.99  --bmc1_out_unsat_core                   false
% 2.27/0.99  --bmc1_aig_witness_out                  false
% 2.27/0.99  --bmc1_verbose                          false
% 2.27/0.99  --bmc1_dump_clauses_tptp                false
% 2.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.27/0.99  --bmc1_dump_file                        -
% 2.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.27/0.99  --bmc1_ucm_extend_mode                  1
% 2.27/0.99  --bmc1_ucm_init_mode                    2
% 2.27/0.99  --bmc1_ucm_cone_mode                    none
% 2.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.27/0.99  --bmc1_ucm_relax_model                  4
% 2.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/0.99  --bmc1_ucm_layered_model                none
% 2.27/0.99  --bmc1_ucm_max_lemma_size               10
% 2.27/0.99  
% 2.27/0.99  ------ AIG Options
% 2.27/0.99  
% 2.27/0.99  --aig_mode                              false
% 2.27/0.99  
% 2.27/0.99  ------ Instantiation Options
% 2.27/0.99  
% 2.27/0.99  --instantiation_flag                    true
% 2.27/0.99  --inst_sos_flag                         false
% 2.27/0.99  --inst_sos_phase                        true
% 2.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/0.99  --inst_lit_sel_side                     num_symb
% 2.27/0.99  --inst_solver_per_active                1400
% 2.27/0.99  --inst_solver_calls_frac                1.
% 2.27/0.99  --inst_passive_queue_type               priority_queues
% 2.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/0.99  --inst_passive_queues_freq              [25;2]
% 2.27/0.99  --inst_dismatching                      true
% 2.27/0.99  --inst_eager_unprocessed_to_passive     true
% 2.27/0.99  --inst_prop_sim_given                   true
% 2.27/0.99  --inst_prop_sim_new                     false
% 2.27/0.99  --inst_subs_new                         false
% 2.27/1.00  --inst_eq_res_simp                      false
% 2.27/1.00  --inst_subs_given                       false
% 2.27/1.00  --inst_orphan_elimination               true
% 2.27/1.00  --inst_learning_loop_flag               true
% 2.27/1.00  --inst_learning_start                   3000
% 2.27/1.00  --inst_learning_factor                  2
% 2.27/1.00  --inst_start_prop_sim_after_learn       3
% 2.27/1.00  --inst_sel_renew                        solver
% 2.27/1.00  --inst_lit_activity_flag                true
% 2.27/1.00  --inst_restr_to_given                   false
% 2.27/1.00  --inst_activity_threshold               500
% 2.27/1.00  --inst_out_proof                        true
% 2.27/1.00  
% 2.27/1.00  ------ Resolution Options
% 2.27/1.00  
% 2.27/1.00  --resolution_flag                       true
% 2.27/1.00  --res_lit_sel                           adaptive
% 2.27/1.00  --res_lit_sel_side                      none
% 2.27/1.00  --res_ordering                          kbo
% 2.27/1.00  --res_to_prop_solver                    active
% 2.27/1.00  --res_prop_simpl_new                    false
% 2.27/1.00  --res_prop_simpl_given                  true
% 2.27/1.00  --res_passive_queue_type                priority_queues
% 2.27/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/1.00  --res_passive_queues_freq               [15;5]
% 2.27/1.00  --res_forward_subs                      full
% 2.27/1.00  --res_backward_subs                     full
% 2.27/1.00  --res_forward_subs_resolution           true
% 2.27/1.00  --res_backward_subs_resolution          true
% 2.27/1.00  --res_orphan_elimination                true
% 2.27/1.00  --res_time_limit                        2.
% 2.27/1.00  --res_out_proof                         true
% 2.27/1.00  
% 2.27/1.00  ------ Superposition Options
% 2.27/1.00  
% 2.27/1.00  --superposition_flag                    true
% 2.27/1.00  --sup_passive_queue_type                priority_queues
% 2.27/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.27/1.00  --demod_completeness_check              fast
% 2.27/1.00  --demod_use_ground                      true
% 2.27/1.00  --sup_to_prop_solver                    passive
% 2.27/1.00  --sup_prop_simpl_new                    true
% 2.27/1.00  --sup_prop_simpl_given                  true
% 2.27/1.00  --sup_fun_splitting                     false
% 2.27/1.00  --sup_smt_interval                      50000
% 2.27/1.00  
% 2.27/1.00  ------ Superposition Simplification Setup
% 2.27/1.00  
% 2.27/1.00  --sup_indices_passive                   []
% 2.27/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.00  --sup_full_bw                           [BwDemod]
% 2.27/1.00  --sup_immed_triv                        [TrivRules]
% 2.27/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.00  --sup_immed_bw_main                     []
% 2.27/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.00  
% 2.27/1.00  ------ Combination Options
% 2.27/1.00  
% 2.27/1.00  --comb_res_mult                         3
% 2.27/1.00  --comb_sup_mult                         2
% 2.27/1.00  --comb_inst_mult                        10
% 2.27/1.00  
% 2.27/1.00  ------ Debug Options
% 2.27/1.00  
% 2.27/1.00  --dbg_backtrace                         false
% 2.27/1.00  --dbg_dump_prop_clauses                 false
% 2.27/1.00  --dbg_dump_prop_clauses_file            -
% 2.27/1.00  --dbg_out_stat                          false
% 2.27/1.00  ------ Parsing...
% 2.27/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.27/1.00  
% 2.27/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 2.27/1.00  
% 2.27/1.00  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.27/1.00  
% 2.27/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.27/1.00  ------ Proving...
% 2.27/1.00  ------ Problem Properties 
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  clauses                                 48
% 2.27/1.00  conjectures                             6
% 2.27/1.00  EPR                                     2
% 2.27/1.00  Horn                                    46
% 2.27/1.00  unary                                   6
% 2.27/1.00  binary                                  9
% 2.27/1.00  lits                                    144
% 2.27/1.00  lits eq                                 7
% 2.27/1.00  fd_pure                                 0
% 2.27/1.00  fd_pseudo                               0
% 2.27/1.00  fd_cond                                 0
% 2.27/1.00  fd_pseudo_cond                          0
% 2.27/1.00  AC symbols                              0
% 2.27/1.00  
% 2.27/1.00  ------ Schedule dynamic 5 is on 
% 2.27/1.00  
% 2.27/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  ------ 
% 2.27/1.00  Current options:
% 2.27/1.00  ------ 
% 2.27/1.00  
% 2.27/1.00  ------ Input Options
% 2.27/1.00  
% 2.27/1.00  --out_options                           all
% 2.27/1.00  --tptp_safe_out                         true
% 2.27/1.00  --problem_path                          ""
% 2.27/1.00  --include_path                          ""
% 2.27/1.00  --clausifier                            res/vclausify_rel
% 2.27/1.00  --clausifier_options                    --mode clausify
% 2.27/1.00  --stdin                                 false
% 2.27/1.00  --stats_out                             all
% 2.27/1.00  
% 2.27/1.00  ------ General Options
% 2.27/1.00  
% 2.27/1.00  --fof                                   false
% 2.27/1.00  --time_out_real                         305.
% 2.27/1.00  --time_out_virtual                      -1.
% 2.27/1.00  --symbol_type_check                     false
% 2.27/1.00  --clausify_out                          false
% 2.27/1.00  --sig_cnt_out                           false
% 2.27/1.00  --trig_cnt_out                          false
% 2.27/1.00  --trig_cnt_out_tolerance                1.
% 2.27/1.00  --trig_cnt_out_sk_spl                   false
% 2.27/1.00  --abstr_cl_out                          false
% 2.27/1.00  
% 2.27/1.00  ------ Global Options
% 2.27/1.00  
% 2.27/1.00  --schedule                              default
% 2.27/1.00  --add_important_lit                     false
% 2.27/1.00  --prop_solver_per_cl                    1000
% 2.27/1.00  --min_unsat_core                        false
% 2.27/1.00  --soft_assumptions                      false
% 2.27/1.00  --soft_lemma_size                       3
% 2.27/1.00  --prop_impl_unit_size                   0
% 2.27/1.00  --prop_impl_unit                        []
% 2.27/1.00  --share_sel_clauses                     true
% 2.27/1.00  --reset_solvers                         false
% 2.27/1.00  --bc_imp_inh                            [conj_cone]
% 2.27/1.00  --conj_cone_tolerance                   3.
% 2.27/1.00  --extra_neg_conj                        none
% 2.27/1.00  --large_theory_mode                     true
% 2.27/1.00  --prolific_symb_bound                   200
% 2.27/1.00  --lt_threshold                          2000
% 2.27/1.00  --clause_weak_htbl                      true
% 2.27/1.00  --gc_record_bc_elim                     false
% 2.27/1.00  
% 2.27/1.00  ------ Preprocessing Options
% 2.27/1.00  
% 2.27/1.00  --preprocessing_flag                    true
% 2.27/1.00  --time_out_prep_mult                    0.1
% 2.27/1.00  --splitting_mode                        input
% 2.27/1.00  --splitting_grd                         true
% 2.27/1.00  --splitting_cvd                         false
% 2.27/1.00  --splitting_cvd_svl                     false
% 2.27/1.00  --splitting_nvd                         32
% 2.27/1.00  --sub_typing                            true
% 2.27/1.00  --prep_gs_sim                           true
% 2.27/1.00  --prep_unflatten                        true
% 2.27/1.00  --prep_res_sim                          true
% 2.27/1.00  --prep_upred                            true
% 2.27/1.00  --prep_sem_filter                       exhaustive
% 2.27/1.00  --prep_sem_filter_out                   false
% 2.27/1.00  --pred_elim                             true
% 2.27/1.00  --res_sim_input                         true
% 2.27/1.00  --eq_ax_congr_red                       true
% 2.27/1.00  --pure_diseq_elim                       true
% 2.27/1.00  --brand_transform                       false
% 2.27/1.00  --non_eq_to_eq                          false
% 2.27/1.00  --prep_def_merge                        true
% 2.27/1.00  --prep_def_merge_prop_impl              false
% 2.27/1.00  --prep_def_merge_mbd                    true
% 2.27/1.00  --prep_def_merge_tr_red                 false
% 2.27/1.00  --prep_def_merge_tr_cl                  false
% 2.27/1.00  --smt_preprocessing                     true
% 2.27/1.00  --smt_ac_axioms                         fast
% 2.27/1.00  --preprocessed_out                      false
% 2.27/1.00  --preprocessed_stats                    false
% 2.27/1.00  
% 2.27/1.00  ------ Abstraction refinement Options
% 2.27/1.00  
% 2.27/1.00  --abstr_ref                             []
% 2.27/1.00  --abstr_ref_prep                        false
% 2.27/1.00  --abstr_ref_until_sat                   false
% 2.27/1.00  --abstr_ref_sig_restrict                funpre
% 2.27/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/1.00  --abstr_ref_under                       []
% 2.27/1.00  
% 2.27/1.00  ------ SAT Options
% 2.27/1.00  
% 2.27/1.00  --sat_mode                              false
% 2.27/1.00  --sat_fm_restart_options                ""
% 2.27/1.00  --sat_gr_def                            false
% 2.27/1.00  --sat_epr_types                         true
% 2.27/1.00  --sat_non_cyclic_types                  false
% 2.27/1.00  --sat_finite_models                     false
% 2.27/1.00  --sat_fm_lemmas                         false
% 2.27/1.00  --sat_fm_prep                           false
% 2.27/1.00  --sat_fm_uc_incr                        true
% 2.27/1.00  --sat_out_model                         small
% 2.27/1.00  --sat_out_clauses                       false
% 2.27/1.00  
% 2.27/1.00  ------ QBF Options
% 2.27/1.00  
% 2.27/1.00  --qbf_mode                              false
% 2.27/1.00  --qbf_elim_univ                         false
% 2.27/1.00  --qbf_dom_inst                          none
% 2.27/1.00  --qbf_dom_pre_inst                      false
% 2.27/1.00  --qbf_sk_in                             false
% 2.27/1.00  --qbf_pred_elim                         true
% 2.27/1.00  --qbf_split                             512
% 2.27/1.00  
% 2.27/1.00  ------ BMC1 Options
% 2.27/1.00  
% 2.27/1.00  --bmc1_incremental                      false
% 2.27/1.00  --bmc1_axioms                           reachable_all
% 2.27/1.00  --bmc1_min_bound                        0
% 2.27/1.00  --bmc1_max_bound                        -1
% 2.27/1.00  --bmc1_max_bound_default                -1
% 2.27/1.00  --bmc1_symbol_reachability              true
% 2.27/1.00  --bmc1_property_lemmas                  false
% 2.27/1.00  --bmc1_k_induction                      false
% 2.27/1.00  --bmc1_non_equiv_states                 false
% 2.27/1.00  --bmc1_deadlock                         false
% 2.27/1.00  --bmc1_ucm                              false
% 2.27/1.00  --bmc1_add_unsat_core                   none
% 2.27/1.00  --bmc1_unsat_core_children              false
% 2.27/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/1.00  --bmc1_out_stat                         full
% 2.27/1.00  --bmc1_ground_init                      false
% 2.27/1.00  --bmc1_pre_inst_next_state              false
% 2.27/1.00  --bmc1_pre_inst_state                   false
% 2.27/1.00  --bmc1_pre_inst_reach_state             false
% 2.27/1.00  --bmc1_out_unsat_core                   false
% 2.27/1.00  --bmc1_aig_witness_out                  false
% 2.27/1.00  --bmc1_verbose                          false
% 2.27/1.00  --bmc1_dump_clauses_tptp                false
% 2.27/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.27/1.00  --bmc1_dump_file                        -
% 2.27/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.27/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.27/1.00  --bmc1_ucm_extend_mode                  1
% 2.27/1.00  --bmc1_ucm_init_mode                    2
% 2.27/1.00  --bmc1_ucm_cone_mode                    none
% 2.27/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.27/1.00  --bmc1_ucm_relax_model                  4
% 2.27/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.27/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/1.00  --bmc1_ucm_layered_model                none
% 2.27/1.00  --bmc1_ucm_max_lemma_size               10
% 2.27/1.00  
% 2.27/1.00  ------ AIG Options
% 2.27/1.00  
% 2.27/1.00  --aig_mode                              false
% 2.27/1.00  
% 2.27/1.00  ------ Instantiation Options
% 2.27/1.00  
% 2.27/1.00  --instantiation_flag                    true
% 2.27/1.00  --inst_sos_flag                         false
% 2.27/1.00  --inst_sos_phase                        true
% 2.27/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/1.00  --inst_lit_sel_side                     none
% 2.27/1.00  --inst_solver_per_active                1400
% 2.27/1.00  --inst_solver_calls_frac                1.
% 2.27/1.00  --inst_passive_queue_type               priority_queues
% 2.27/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/1.00  --inst_passive_queues_freq              [25;2]
% 2.27/1.00  --inst_dismatching                      true
% 2.27/1.00  --inst_eager_unprocessed_to_passive     true
% 2.27/1.00  --inst_prop_sim_given                   true
% 2.27/1.00  --inst_prop_sim_new                     false
% 2.27/1.00  --inst_subs_new                         false
% 2.27/1.00  --inst_eq_res_simp                      false
% 2.27/1.00  --inst_subs_given                       false
% 2.27/1.00  --inst_orphan_elimination               true
% 2.27/1.00  --inst_learning_loop_flag               true
% 2.27/1.00  --inst_learning_start                   3000
% 2.27/1.00  --inst_learning_factor                  2
% 2.27/1.00  --inst_start_prop_sim_after_learn       3
% 2.27/1.00  --inst_sel_renew                        solver
% 2.27/1.00  --inst_lit_activity_flag                true
% 2.27/1.00  --inst_restr_to_given                   false
% 2.27/1.00  --inst_activity_threshold               500
% 2.27/1.00  --inst_out_proof                        true
% 2.27/1.00  
% 2.27/1.00  ------ Resolution Options
% 2.27/1.00  
% 2.27/1.00  --resolution_flag                       false
% 2.27/1.00  --res_lit_sel                           adaptive
% 2.27/1.00  --res_lit_sel_side                      none
% 2.27/1.00  --res_ordering                          kbo
% 2.27/1.00  --res_to_prop_solver                    active
% 2.27/1.00  --res_prop_simpl_new                    false
% 2.27/1.00  --res_prop_simpl_given                  true
% 2.27/1.00  --res_passive_queue_type                priority_queues
% 2.27/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/1.00  --res_passive_queues_freq               [15;5]
% 2.27/1.00  --res_forward_subs                      full
% 2.27/1.00  --res_backward_subs                     full
% 2.27/1.00  --res_forward_subs_resolution           true
% 2.27/1.00  --res_backward_subs_resolution          true
% 2.27/1.00  --res_orphan_elimination                true
% 2.27/1.00  --res_time_limit                        2.
% 2.27/1.00  --res_out_proof                         true
% 2.27/1.00  
% 2.27/1.00  ------ Superposition Options
% 2.27/1.00  
% 2.27/1.00  --superposition_flag                    true
% 2.27/1.00  --sup_passive_queue_type                priority_queues
% 2.27/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.27/1.00  --demod_completeness_check              fast
% 2.27/1.00  --demod_use_ground                      true
% 2.27/1.00  --sup_to_prop_solver                    passive
% 2.27/1.00  --sup_prop_simpl_new                    true
% 2.27/1.00  --sup_prop_simpl_given                  true
% 2.27/1.00  --sup_fun_splitting                     false
% 2.27/1.00  --sup_smt_interval                      50000
% 2.27/1.00  
% 2.27/1.00  ------ Superposition Simplification Setup
% 2.27/1.00  
% 2.27/1.00  --sup_indices_passive                   []
% 2.27/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.00  --sup_full_bw                           [BwDemod]
% 2.27/1.00  --sup_immed_triv                        [TrivRules]
% 2.27/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.00  --sup_immed_bw_main                     []
% 2.27/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/1.00  
% 2.27/1.00  ------ Combination Options
% 2.27/1.00  
% 2.27/1.00  --comb_res_mult                         3
% 2.27/1.00  --comb_sup_mult                         2
% 2.27/1.00  --comb_inst_mult                        10
% 2.27/1.00  
% 2.27/1.00  ------ Debug Options
% 2.27/1.00  
% 2.27/1.00  --dbg_backtrace                         false
% 2.27/1.00  --dbg_dump_prop_clauses                 false
% 2.27/1.00  --dbg_dump_prop_clauses_file            -
% 2.27/1.00  --dbg_out_stat                          false
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  ------ Proving...
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  % SZS status Theorem for theBenchmark.p
% 2.27/1.00  
% 2.27/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.27/1.00  
% 2.27/1.00  fof(f15,conjecture,(
% 2.27/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.27/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f16,negated_conjecture,(
% 2.27/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 2.27/1.00    inference(negated_conjecture,[],[f15])).
% 2.27/1.00  
% 2.27/1.00  fof(f42,plain,(
% 2.27/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.27/1.00    inference(ennf_transformation,[],[f16])).
% 2.27/1.00  
% 2.27/1.00  fof(f43,plain,(
% 2.27/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.27/1.00    inference(flattening,[],[f42])).
% 2.27/1.00  
% 2.27/1.00  fof(f49,plain,(
% 2.27/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4))) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.27/1.00    inference(nnf_transformation,[],[f43])).
% 2.27/1.00  
% 2.27/1.00  fof(f50,plain,(
% 2.27/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.27/1.00    inference(flattening,[],[f49])).
% 2.27/1.00  
% 2.27/1.00  fof(f56,plain,(
% 2.27/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) => ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),sK6) | r1_tmap_1(X1,X0,X2,X4)) & sK6 = X4 & m1_subset_1(sK6,u1_struct_0(X3)))) )),
% 2.27/1.00    introduced(choice_axiom,[])).
% 2.27/1.00  
% 2.27/1.00  fof(f55,plain,(
% 2.27/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,sK5)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,sK5)) & sK5 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 2.27/1.00    introduced(choice_axiom,[])).
% 2.27/1.00  
% 2.27/1.00  fof(f54,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(sK4,X0,k2_tmap_1(X1,X0,X2,sK4),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(sK4,X1) & v1_tsep_1(sK4,X1) & ~v2_struct_0(sK4))) )),
% 2.27/1.00    introduced(choice_axiom,[])).
% 2.27/1.00  
% 2.27/1.00  fof(f53,plain,(
% 2.27/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5) | ~r1_tmap_1(X1,X0,sK3,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,sK3,X3),X5) | r1_tmap_1(X1,X0,sK3,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 2.27/1.00    introduced(choice_axiom,[])).
% 2.27/1.00  
% 2.27/1.00  fof(f52,plain,(
% 2.27/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5) | ~r1_tmap_1(sK2,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(sK2,X0,X2,X3),X5) | r1_tmap_1(sK2,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(sK2))) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))) )),
% 2.27/1.00    introduced(choice_axiom,[])).
% 2.27/1.00  
% 2.27/1.00  fof(f51,plain,(
% 2.27/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | r1_tmap_1(X1,X0,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5) | ~r1_tmap_1(X1,sK1,X2,X4)) & (r1_tmap_1(X3,sK1,k2_tmap_1(X1,sK1,X2,X3),X5) | r1_tmap_1(X1,sK1,X2,X4)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.27/1.00    introduced(choice_axiom,[])).
% 2.27/1.00  
% 2.27/1.00  fof(f57,plain,(
% 2.27/1.00    ((((((~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | ~r1_tmap_1(sK2,sK1,sK3,sK5)) & (r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | r1_tmap_1(sK2,sK1,sK3,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_pre_topc(sK4,sK2) & v1_tsep_1(sK4,sK2) & ~v2_struct_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.27/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f50,f56,f55,f54,f53,f52,f51])).
% 2.27/1.00  
% 2.27/1.00  fof(f90,plain,(
% 2.27/1.00    m1_pre_topc(sK4,sK2)),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f14,axiom,(
% 2.27/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 2.27/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f40,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/1.00    inference(ennf_transformation,[],[f14])).
% 2.27/1.00  
% 2.27/1.00  fof(f41,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/1.00    inference(flattening,[],[f40])).
% 2.27/1.00  
% 2.27/1.00  fof(f48,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/1.00    inference(nnf_transformation,[],[f41])).
% 2.27/1.00  
% 2.27/1.00  fof(f78,plain,(
% 2.27/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f48])).
% 2.27/1.00  
% 2.27/1.00  fof(f100,plain,(
% 2.27/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X1,X0,X2,X6) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.00    inference(equality_resolution,[],[f78])).
% 2.27/1.00  
% 2.27/1.00  fof(f86,plain,(
% 2.27/1.00    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f85,plain,(
% 2.27/1.00    v1_funct_1(sK3)),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f5,axiom,(
% 2.27/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.27/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f23,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/1.00    inference(ennf_transformation,[],[f5])).
% 2.27/1.00  
% 2.27/1.00  fof(f24,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/1.00    inference(flattening,[],[f23])).
% 2.27/1.00  
% 2.27/1.00  fof(f62,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f24])).
% 2.27/1.00  
% 2.27/1.00  fof(f82,plain,(
% 2.27/1.00    ~v2_struct_0(sK2)),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f83,plain,(
% 2.27/1.00    v2_pre_topc(sK2)),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f84,plain,(
% 2.27/1.00    l1_pre_topc(sK2)),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f88,plain,(
% 2.27/1.00    ~v2_struct_0(sK4)),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f80,plain,(
% 2.27/1.00    v2_pre_topc(sK1)),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f79,plain,(
% 2.27/1.00    ~v2_struct_0(sK1)),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f81,plain,(
% 2.27/1.00    l1_pre_topc(sK1)),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f87,plain,(
% 2.27/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f2,axiom,(
% 2.27/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.27/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f19,plain,(
% 2.27/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.27/1.00    inference(ennf_transformation,[],[f2])).
% 2.27/1.00  
% 2.27/1.00  fof(f59,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f19])).
% 2.27/1.00  
% 2.27/1.00  fof(f1,axiom,(
% 2.27/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.27/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f17,plain,(
% 2.27/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.27/1.00    inference(ennf_transformation,[],[f1])).
% 2.27/1.00  
% 2.27/1.00  fof(f18,plain,(
% 2.27/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.27/1.00    inference(flattening,[],[f17])).
% 2.27/1.00  
% 2.27/1.00  fof(f58,plain,(
% 2.27/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f18])).
% 2.27/1.00  
% 2.27/1.00  fof(f77,plain,(
% 2.27/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f48])).
% 2.27/1.00  
% 2.27/1.00  fof(f101,plain,(
% 2.27/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X6) | ~m1_connsp_2(X4,X1,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.00    inference(equality_resolution,[],[f77])).
% 2.27/1.00  
% 2.27/1.00  fof(f13,axiom,(
% 2.27/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 2.27/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f38,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/1.00    inference(ennf_transformation,[],[f13])).
% 2.27/1.00  
% 2.27/1.00  fof(f39,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/1.00    inference(flattening,[],[f38])).
% 2.27/1.00  
% 2.27/1.00  fof(f76,plain,(
% 2.27/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f39])).
% 2.27/1.00  
% 2.27/1.00  fof(f99,plain,(
% 2.27/1.00    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.00    inference(equality_resolution,[],[f76])).
% 2.27/1.00  
% 2.27/1.00  fof(f10,axiom,(
% 2.27/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.27/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f33,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/1.00    inference(ennf_transformation,[],[f10])).
% 2.27/1.00  
% 2.27/1.00  fof(f34,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/1.00    inference(flattening,[],[f33])).
% 2.27/1.00  
% 2.27/1.00  fof(f44,plain,(
% 2.27/1.00    ! [X2,X1,X0] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => (r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_connsp_2(sK0(X0,X1,X2),X0,X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK0(X0,X1,X2))))),
% 2.27/1.00    introduced(choice_axiom,[])).
% 2.27/1.00  
% 2.27/1.00  fof(f45,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(sK0(X0,X1,X2),X2) & v3_pre_topc(sK0(X0,X1,X2),X0) & m1_connsp_2(sK0(X0,X1,X2),X0,X1) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK0(X0,X1,X2))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f44])).
% 2.27/1.00  
% 2.27/1.00  fof(f71,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (r1_tarski(sK0(X0,X1,X2),X2) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f45])).
% 2.27/1.00  
% 2.27/1.00  fof(f7,axiom,(
% 2.27/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.27/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f27,plain,(
% 2.27/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/1.00    inference(ennf_transformation,[],[f7])).
% 2.27/1.00  
% 2.27/1.00  fof(f28,plain,(
% 2.27/1.00    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/1.00    inference(flattening,[],[f27])).
% 2.27/1.00  
% 2.27/1.00  fof(f64,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f28])).
% 2.27/1.00  
% 2.27/1.00  fof(f69,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (m1_connsp_2(sK0(X0,X1,X2),X0,X1) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f45])).
% 2.27/1.00  
% 2.27/1.00  fof(f68,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f45])).
% 2.27/1.00  
% 2.27/1.00  fof(f9,axiom,(
% 2.27/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 2.27/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f31,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/1.00    inference(ennf_transformation,[],[f9])).
% 2.27/1.00  
% 2.27/1.00  fof(f32,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/1.00    inference(flattening,[],[f31])).
% 2.27/1.00  
% 2.27/1.00  fof(f66,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f32])).
% 2.27/1.00  
% 2.27/1.00  fof(f8,axiom,(
% 2.27/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 2.27/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f29,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/1.00    inference(ennf_transformation,[],[f8])).
% 2.27/1.00  
% 2.27/1.00  fof(f30,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/1.00    inference(flattening,[],[f29])).
% 2.27/1.00  
% 2.27/1.00  fof(f65,plain,(
% 2.27/1.00    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f30])).
% 2.27/1.00  
% 2.27/1.00  fof(f3,axiom,(
% 2.27/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.27/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f20,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.27/1.00    inference(ennf_transformation,[],[f3])).
% 2.27/1.00  
% 2.27/1.00  fof(f21,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.27/1.00    inference(flattening,[],[f20])).
% 2.27/1.00  
% 2.27/1.00  fof(f60,plain,(
% 2.27/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f21])).
% 2.27/1.00  
% 2.27/1.00  fof(f4,axiom,(
% 2.27/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.27/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f22,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.27/1.00    inference(ennf_transformation,[],[f4])).
% 2.27/1.00  
% 2.27/1.00  fof(f61,plain,(
% 2.27/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f22])).
% 2.27/1.00  
% 2.27/1.00  fof(f6,axiom,(
% 2.27/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.27/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f25,plain,(
% 2.27/1.00    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.27/1.00    inference(ennf_transformation,[],[f6])).
% 2.27/1.00  
% 2.27/1.00  fof(f26,plain,(
% 2.27/1.00    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.27/1.00    inference(flattening,[],[f25])).
% 2.27/1.00  
% 2.27/1.00  fof(f63,plain,(
% 2.27/1.00    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f26])).
% 2.27/1.00  
% 2.27/1.00  fof(f94,plain,(
% 2.27/1.00    r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | r1_tmap_1(sK2,sK1,sK3,sK5)),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f93,plain,(
% 2.27/1.00    sK5 = sK6),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f12,axiom,(
% 2.27/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.27/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f37,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.27/1.00    inference(ennf_transformation,[],[f12])).
% 2.27/1.00  
% 2.27/1.00  fof(f75,plain,(
% 2.27/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f37])).
% 2.27/1.00  
% 2.27/1.00  fof(f11,axiom,(
% 2.27/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.27/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.27/1.00  
% 2.27/1.00  fof(f35,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.27/1.00    inference(ennf_transformation,[],[f11])).
% 2.27/1.00  
% 2.27/1.00  fof(f36,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.27/1.00    inference(flattening,[],[f35])).
% 2.27/1.00  
% 2.27/1.00  fof(f46,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.27/1.00    inference(nnf_transformation,[],[f36])).
% 2.27/1.00  
% 2.27/1.00  fof(f47,plain,(
% 2.27/1.00    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.27/1.00    inference(flattening,[],[f46])).
% 2.27/1.00  
% 2.27/1.00  fof(f72,plain,(
% 2.27/1.00    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.27/1.00    inference(cnf_transformation,[],[f47])).
% 2.27/1.00  
% 2.27/1.00  fof(f98,plain,(
% 2.27/1.00    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.27/1.00    inference(equality_resolution,[],[f72])).
% 2.27/1.00  
% 2.27/1.00  fof(f89,plain,(
% 2.27/1.00    v1_tsep_1(sK4,sK2)),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f95,plain,(
% 2.27/1.00    ~r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) | ~r1_tmap_1(sK2,sK1,sK3,sK5)),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f92,plain,(
% 2.27/1.00    m1_subset_1(sK6,u1_struct_0(sK4))),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  fof(f91,plain,(
% 2.27/1.00    m1_subset_1(sK5,u1_struct_0(sK2))),
% 2.27/1.00    inference(cnf_transformation,[],[f57])).
% 2.27/1.00  
% 2.27/1.00  cnf(c_26,negated_conjecture,
% 2.27/1.00      ( m1_pre_topc(sK4,sK2) ),
% 2.27/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_19,plain,
% 2.27/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.27/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.27/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.27/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 2.27/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.27/1.00      | ~ m1_pre_topc(X4,X0)
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.27/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.27/1.00      | ~ v1_funct_1(X2)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | v2_struct_0(X4)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ l1_pre_topc(X0)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f100]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_30,negated_conjecture,
% 2.27/1.00      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 2.27/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_883,plain,
% 2.27/1.00      ( r1_tmap_1(X0,X1,X2,X3)
% 2.27/1.00      | ~ r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.27/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 2.27/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.27/1.00      | ~ m1_pre_topc(X4,X0)
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.27/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.27/1.00      | ~ v1_funct_1(X2)
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X4)
% 2.27/1.00      | ~ l1_pre_topc(X0)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X0)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.27/1.00      | sK3 != X2 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_884,plain,
% 2.27/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.27/1.00      | r1_tmap_1(X2,X1,sK3,X3)
% 2.27/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 2.27/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_pre_topc(X0,X2)
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.27/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/1.00      | ~ v1_funct_1(sK3)
% 2.27/1.00      | v2_struct_0(X2)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | ~ l1_pre_topc(X2)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X2)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_883]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_31,negated_conjecture,
% 2.27/1.00      ( v1_funct_1(sK3) ),
% 2.27/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_888,plain,
% 2.27/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_pre_topc(X0,X2)
% 2.27/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 2.27/1.00      | r1_tmap_1(X2,X1,sK3,X3)
% 2.27/1.00      | ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.27/1.00      | v2_struct_0(X2)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | ~ l1_pre_topc(X2)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X2)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_884,c_31]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_889,plain,
% 2.27/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.27/1.00      | r1_tmap_1(X2,X1,sK3,X3)
% 2.27/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 2.27/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_pre_topc(X0,X2)
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.27/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X2)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ l1_pre_topc(X2)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X2)
% 2.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(renaming,[status(thm)],[c_888]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_4,plain,
% 2.27/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.27/1.00      | m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | ~ l1_pre_topc(X1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_930,plain,
% 2.27/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.27/1.00      | r1_tmap_1(X2,X1,sK3,X3)
% 2.27/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 2.27/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_pre_topc(X0,X2)
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X2)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ l1_pre_topc(X2)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X2)
% 2.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_889,c_4]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1099,plain,
% 2.27/1.00      ( ~ r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.27/1.00      | r1_tmap_1(X2,X1,sK3,X3)
% 2.27/1.00      | ~ m1_connsp_2(X4,X2,X3)
% 2.27/1.00      | ~ r1_tarski(X4,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | v2_struct_0(X2)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X2)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X2)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.27/1.00      | sK2 != X2
% 2.27/1.00      | sK4 != X0 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_930]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1100,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,X0,sK3,X1)
% 2.27/1.00      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.27/1.00      | ~ m1_connsp_2(X2,sK2,X1)
% 2.27/1.00      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | v2_struct_0(sK2)
% 2.27/1.00      | v2_struct_0(sK4)
% 2.27/1.00      | ~ l1_pre_topc(X0)
% 2.27/1.00      | ~ l1_pre_topc(sK2)
% 2.27/1.00      | ~ v2_pre_topc(X0)
% 2.27/1.00      | ~ v2_pre_topc(sK2)
% 2.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.27/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_1099]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_34,negated_conjecture,
% 2.27/1.00      ( ~ v2_struct_0(sK2) ),
% 2.27/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_33,negated_conjecture,
% 2.27/1.00      ( v2_pre_topc(sK2) ),
% 2.27/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_32,negated_conjecture,
% 2.27/1.00      ( l1_pre_topc(sK2) ),
% 2.27/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_28,negated_conjecture,
% 2.27/1.00      ( ~ v2_struct_0(sK4) ),
% 2.27/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1104,plain,
% 2.27/1.00      ( ~ v2_pre_topc(X0)
% 2.27/1.00      | r1_tmap_1(sK2,X0,sK3,X1)
% 2.27/1.00      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.27/1.00      | ~ m1_connsp_2(X2,sK2,X1)
% 2.27/1.00      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | ~ l1_pre_topc(X0)
% 2.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.27/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_1100,c_34,c_33,c_32,c_28]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1105,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,X0,sK3,X1)
% 2.27/1.00      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.27/1.00      | ~ m1_connsp_2(X2,sK2,X1)
% 2.27/1.00      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | ~ l1_pre_topc(X0)
% 2.27/1.00      | ~ v2_pre_topc(X0)
% 2.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.27/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.27/1.00      inference(renaming,[status(thm)],[c_1104]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_36,negated_conjecture,
% 2.27/1.00      ( v2_pre_topc(sK1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1344,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,X0,sK3,X1)
% 2.27/1.00      | ~ r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.27/1.00      | ~ m1_connsp_2(X2,sK2,X1)
% 2.27/1.00      | ~ r1_tarski(X2,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | ~ l1_pre_topc(X0)
% 2.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.27/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.27/1.00      | sK1 != X0 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_1105,c_36]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1345,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 2.27/1.00      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.27/1.00      | ~ m1_connsp_2(X1,sK2,X0)
% 2.27/1.00      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.27/1.00      | v2_struct_0(sK1)
% 2.27/1.00      | ~ l1_pre_topc(sK1)
% 2.27/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_1344]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_37,negated_conjecture,
% 2.27/1.00      ( ~ v2_struct_0(sK1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_35,negated_conjecture,
% 2.27/1.00      ( l1_pre_topc(sK1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_29,negated_conjecture,
% 2.27/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 2.27/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1349,plain,
% 2.27/1.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.27/1.00      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_connsp_2(X1,sK2,X0)
% 2.27/1.00      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.27/1.00      | r1_tmap_1(sK2,sK1,sK3,X0)
% 2.27/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_1345,c_37,c_35,c_29]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1350,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,sK1,sK3,X0)
% 2.27/1.00      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.27/1.00      | ~ m1_connsp_2(X1,sK2,X0)
% 2.27/1.00      | ~ r1_tarski(X1,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(renaming,[status(thm)],[c_1349]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3389,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,sK1,sK3,X0_54)
% 2.27/1.00      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
% 2.27/1.00      | ~ m1_connsp_2(X1_54,sK2,X0_54)
% 2.27/1.00      | ~ r1_tarski(X1_54,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_1350]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3635,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,sK1,sK3,X0_54)
% 2.27/1.00      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
% 2.27/1.00      | ~ m1_connsp_2(X1_54,sK2,X0_54)
% 2.27/1.00      | ~ r1_tarski(X1_54,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.27/1.00      inference(equality_resolution_simp,[status(thm)],[c_3389]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5987,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,sK1,sK3,X0_54)
% 2.27/1.00      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
% 2.27/1.00      | ~ m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,X0_54)
% 2.27/1.00      | ~ r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(sK0(sK2,sK5,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3635]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_6419,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,sK1,sK3,sK5)
% 2.27/1.00      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
% 2.27/1.00      | ~ m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,sK5)
% 2.27/1.00      | ~ r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(sK0(sK2,sK5,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_5987]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_6420,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5) != iProver_top
% 2.27/1.00      | m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,sK5) != iProver_top
% 2.27/1.00      | r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
% 2.27/1.00      | m1_subset_1(sK0(sK2,sK5,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.27/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_6419]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3423,plain,
% 2.27/1.00      ( ~ r1_tmap_1(X0_55,X1_55,X0_54,X1_54)
% 2.27/1.00      | r1_tmap_1(X0_55,X1_55,X2_54,X3_54)
% 2.27/1.00      | X2_54 != X0_54
% 2.27/1.00      | X3_54 != X1_54 ),
% 2.27/1.00      theory(equality) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5143,plain,
% 2.27/1.00      ( r1_tmap_1(sK4,sK1,X0_54,X1_54)
% 2.27/1.00      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 2.27/1.00      | X0_54 != k2_tmap_1(sK2,sK1,sK3,sK4)
% 2.27/1.00      | X1_54 != sK6 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3423]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5337,plain,
% 2.27/1.00      ( r1_tmap_1(sK4,sK1,X0_54,sK5)
% 2.27/1.00      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 2.27/1.00      | X0_54 != k2_tmap_1(sK2,sK1,sK3,sK4)
% 2.27/1.00      | sK5 != sK6 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_5143]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_6406,plain,
% 2.27/1.00      ( r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
% 2.27/1.00      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 2.27/1.00      | k2_tmap_1(sK2,sK1,sK3,sK4) != k2_tmap_1(sK2,sK1,sK3,sK4)
% 2.27/1.00      | sK5 != sK6 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_5337]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_6408,plain,
% 2.27/1.00      ( k2_tmap_1(sK2,sK1,sK3,sK4) != k2_tmap_1(sK2,sK1,sK3,sK4)
% 2.27/1.00      | sK5 != sK6
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5) = iProver_top
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_6406]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3422,plain,
% 2.27/1.00      ( X0_54 != X1_54
% 2.27/1.00      | k2_tmap_1(X0_55,X1_55,X0_54,X2_55) = k2_tmap_1(X0_55,X1_55,X1_54,X2_55) ),
% 2.27/1.00      theory(equality) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5721,plain,
% 2.27/1.00      ( X0_54 != sK3
% 2.27/1.00      | k2_tmap_1(sK2,sK1,X0_54,sK4) = k2_tmap_1(sK2,sK1,sK3,sK4) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3422]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5724,plain,
% 2.27/1.00      ( k2_tmap_1(sK2,sK1,sK3,sK4) = k2_tmap_1(sK2,sK1,sK3,sK4)
% 2.27/1.00      | sK3 != sK3 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_5721]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.27/1.00      | ~ r2_hidden(X2,X0)
% 2.27/1.00      | ~ v1_xboole_0(X1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3402,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 2.27/1.00      | ~ r2_hidden(X2_54,X0_54)
% 2.27/1.00      | ~ v1_xboole_0(X1_54) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5225,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.27/1.00      | ~ r2_hidden(X1_54,X0_54)
% 2.27/1.00      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3402]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5454,plain,
% 2.27/1.00      ( ~ m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.27/1.00      | ~ r2_hidden(X0_54,k1_connsp_2(sK4,sK6))
% 2.27/1.00      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_5225]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5703,plain,
% 2.27/1.00      ( ~ m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.27/1.00      | ~ r2_hidden(sK6,k1_connsp_2(sK4,sK6))
% 2.27/1.00      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_5454]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5704,plain,
% 2.27/1.00      ( m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.27/1.00      | r2_hidden(sK6,k1_connsp_2(sK4,sK6)) != iProver_top
% 2.27/1.00      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_5703]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_0,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3403,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0_54,X1_54)
% 2.27/1.00      | r2_hidden(X0_54,X1_54)
% 2.27/1.00      | v1_xboole_0(X1_54) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5656,plain,
% 2.27/1.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
% 2.27/1.00      | r2_hidden(sK5,u1_struct_0(sK4))
% 2.27/1.00      | v1_xboole_0(u1_struct_0(sK4)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3403]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5657,plain,
% 2.27/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top
% 2.27/1.00      | r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top
% 2.27/1.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_5656]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_20,plain,
% 2.27/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.27/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.27/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.27/1.00      | ~ m1_connsp_2(X5,X0,X3)
% 2.27/1.00      | ~ r1_tarski(X5,u1_struct_0(X4))
% 2.27/1.00      | ~ m1_pre_topc(X4,X0)
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.27/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
% 2.27/1.00      | ~ v1_funct_1(X2)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | v2_struct_0(X4)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ l1_pre_topc(X0)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f101]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_18,plain,
% 2.27/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.27/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.27/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.27/1.00      | ~ m1_pre_topc(X4,X0)
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.27/1.00      | ~ v1_funct_1(X2)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | v2_struct_0(X4)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ l1_pre_topc(X0)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f99]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_200,plain,
% 2.27/1.00      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.27/1.00      | ~ m1_pre_topc(X4,X0)
% 2.27/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.27/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.27/1.00      | ~ r1_tmap_1(X0,X1,X2,X3)
% 2.27/1.00      | ~ v1_funct_1(X2)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | v2_struct_0(X4)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ l1_pre_topc(X0)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X0) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_20,c_18]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_201,plain,
% 2.27/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.27/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.27/1.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 2.27/1.00      | ~ m1_pre_topc(X4,X0)
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.27/1.00      | ~ v1_funct_1(X2)
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X4)
% 2.27/1.00      | ~ l1_pre_topc(X0)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X0)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(renaming,[status(thm)],[c_200]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_826,plain,
% 2.27/1.00      ( ~ r1_tmap_1(X0,X1,X2,X3)
% 2.27/1.00      | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,X2,X4),X3)
% 2.27/1.00      | ~ m1_pre_topc(X4,X0)
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X4))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 2.27/1.00      | ~ v1_funct_1(X2)
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X4)
% 2.27/1.00      | ~ l1_pre_topc(X0)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X0)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK2)
% 2.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.27/1.00      | sK3 != X2 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_201,c_30]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_827,plain,
% 2.27/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.27/1.00      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.27/1.00      | ~ m1_pre_topc(X0,X2)
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/1.00      | ~ v1_funct_1(sK3)
% 2.27/1.00      | v2_struct_0(X2)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | ~ l1_pre_topc(X2)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X2)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_826]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_831,plain,
% 2.27/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_pre_topc(X0,X2)
% 2.27/1.00      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.27/1.00      | r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.27/1.00      | v2_struct_0(X2)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | ~ l1_pre_topc(X2)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X2)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_827,c_31]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_832,plain,
% 2.27/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.27/1.00      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.27/1.00      | ~ m1_pre_topc(X0,X2)
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X2)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ l1_pre_topc(X2)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X2)
% 2.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(renaming,[status(thm)],[c_831]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_867,plain,
% 2.27/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.27/1.00      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.27/1.00      | ~ m1_pre_topc(X0,X2)
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | v2_struct_0(X2)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ l1_pre_topc(X2)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X2)
% 2.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_832,c_4]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1147,plain,
% 2.27/1.00      ( r1_tmap_1(X0,X1,k2_tmap_1(X2,X1,sK3,X0),X3)
% 2.27/1.00      | ~ r1_tmap_1(X2,X1,sK3,X3)
% 2.27/1.00      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | v2_struct_0(X2)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X2)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X2)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | u1_struct_0(X2) != u1_struct_0(sK2)
% 2.27/1.00      | u1_struct_0(X1) != u1_struct_0(sK1)
% 2.27/1.00      | sK2 != X2
% 2.27/1.00      | sK4 != X0 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_867]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1148,plain,
% 2.27/1.00      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.27/1.00      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | v2_struct_0(sK2)
% 2.27/1.00      | v2_struct_0(sK4)
% 2.27/1.00      | ~ l1_pre_topc(X0)
% 2.27/1.00      | ~ l1_pre_topc(sK2)
% 2.27/1.00      | ~ v2_pre_topc(X0)
% 2.27/1.00      | ~ v2_pre_topc(sK2)
% 2.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.27/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_1147]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1152,plain,
% 2.27/1.00      ( ~ v2_pre_topc(X0)
% 2.27/1.00      | ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.27/1.00      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | ~ l1_pre_topc(X0)
% 2.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.27/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_1148,c_34,c_33,c_32,c_28]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1153,plain,
% 2.27/1.00      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.27/1.00      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | ~ l1_pre_topc(X0)
% 2.27/1.00      | ~ v2_pre_topc(X0)
% 2.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.27/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.27/1.00      inference(renaming,[status(thm)],[c_1152]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1320,plain,
% 2.27/1.00      ( ~ r1_tmap_1(sK2,X0,sK3,X1)
% 2.27/1.00      | r1_tmap_1(sK4,X0,k2_tmap_1(sK2,X0,sK3,sK4),X1)
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
% 2.27/1.00      | v2_struct_0(X0)
% 2.27/1.00      | ~ l1_pre_topc(X0)
% 2.27/1.00      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.27/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.27/1.00      | sK1 != X0 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_1153,c_36]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1321,plain,
% 2.27/1.00      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 2.27/1.00      | v2_struct_0(sK1)
% 2.27/1.00      | ~ l1_pre_topc(sK1)
% 2.27/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_1320]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1325,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.27/1.00      | ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 2.27/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_1321,c_37,c_35,c_29]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1326,plain,
% 2.27/1.00      ( ~ r1_tmap_1(sK2,sK1,sK3,X0)
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0)
% 2.27/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.27/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(renaming,[status(thm)],[c_1325]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3390,plain,
% 2.27/1.00      ( ~ r1_tmap_1(sK2,sK1,sK3,X0_54)
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
% 2.27/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 2.27/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_1326]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3631,plain,
% 2.27/1.00      ( ~ r1_tmap_1(sK2,sK1,sK3,X0_54)
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),X0_54)
% 2.27/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK4)) ),
% 2.27/1.00      inference(equality_resolution_simp,[status(thm)],[c_3390]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5615,plain,
% 2.27/1.00      ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5)
% 2.27/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3631]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5623,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,sK1,sK3,sK5) != iProver_top
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK5) = iProver_top
% 2.27/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_5615]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_9,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/1.00      | r1_tarski(sK0(X1,X2,X0),X0)
% 2.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_6,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_250,plain,
% 2.27/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | r1_tarski(sK0(X1,X2,X0),X0)
% 2.27/1.00      | ~ m1_connsp_2(X0,X1,X2)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(global_propositional_subsumption,[status(thm)],[c_9,c_6]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_251,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/1.00      | r1_tarski(sK0(X1,X2,X0),X0)
% 2.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(renaming,[status(thm)],[c_250]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1440,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/1.00      | r1_tarski(sK0(X1,X2,X0),X0)
% 2.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | sK2 != X1 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_251,c_33]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1441,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.27/1.00      | r1_tarski(sK0(sK2,X1,X0),X0)
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.27/1.00      | v2_struct_0(sK2)
% 2.27/1.00      | ~ l1_pre_topc(sK2) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_1440]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1445,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.27/1.00      | r1_tarski(sK0(sK2,X1,X0),X0)
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_1441,c_34,c_32]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3386,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0_54,sK2,X1_54)
% 2.27/1.00      | r1_tarski(sK0(sK2,X1_54,X0_54),X0_54)
% 2.27/1.00      | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_1445]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_4993,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0_54,sK2,sK5)
% 2.27/1.00      | r1_tarski(sK0(sK2,sK5,X0_54),X0_54)
% 2.27/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3386]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5575,plain,
% 2.27/1.00      ( ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK5)
% 2.27/1.00      | r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_4993]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5589,plain,
% 2.27/1.00      ( m1_connsp_2(u1_struct_0(sK4),sK2,sK5) != iProver_top
% 2.27/1.00      | r1_tarski(sK0(sK2,sK5,u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top
% 2.27/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_5575]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_11,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/1.00      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_236,plain,
% 2.27/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.27/1.00      | ~ m1_connsp_2(X0,X1,X2)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_11,c_6]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_237,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/1.00      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(renaming,[status(thm)],[c_236]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1482,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/1.00      | m1_connsp_2(sK0(X1,X2,X0),X1,X2)
% 2.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | sK2 != X1 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_237,c_33]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1483,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.27/1.00      | m1_connsp_2(sK0(sK2,X1,X0),sK2,X1)
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.27/1.00      | v2_struct_0(sK2)
% 2.27/1.00      | ~ l1_pre_topc(sK2) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_1482]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1487,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.27/1.00      | m1_connsp_2(sK0(sK2,X1,X0),sK2,X1)
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_1483,c_34,c_32]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3384,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0_54,sK2,X1_54)
% 2.27/1.00      | m1_connsp_2(sK0(sK2,X1_54,X0_54),sK2,X1_54)
% 2.27/1.00      | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_1487]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_4988,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0_54,sK2,sK5)
% 2.27/1.00      | m1_connsp_2(sK0(sK2,sK5,X0_54),sK2,sK5)
% 2.27/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3384]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5576,plain,
% 2.27/1.00      ( m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,sK5)
% 2.27/1.00      | ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK5)
% 2.27/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_4988]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5587,plain,
% 2.27/1.00      ( m1_connsp_2(sK0(sK2,sK5,u1_struct_0(sK4)),sK2,sK5) = iProver_top
% 2.27/1.00      | m1_connsp_2(u1_struct_0(sK4),sK2,sK5) != iProver_top
% 2.27/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_5576]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_12,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_229,plain,
% 2.27/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | ~ m1_connsp_2(X0,X1,X2)
% 2.27/1.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_12,c_6]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_230,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(renaming,[status(thm)],[c_229]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1503,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,X1,X2)
% 2.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | m1_subset_1(sK0(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | sK2 != X1 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_230,c_33]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1504,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.27/1.00      | m1_subset_1(sK0(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | v2_struct_0(sK2)
% 2.27/1.00      | ~ l1_pre_topc(sK2) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_1503]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1508,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0,sK2,X1)
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.27/1.00      | m1_subset_1(sK0(sK2,X1,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_1504,c_34,c_32]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3383,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0_54,sK2,X1_54)
% 2.27/1.00      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 2.27/1.00      | m1_subset_1(sK0(sK2,X1_54,X0_54),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_1508]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_4978,plain,
% 2.27/1.00      ( ~ m1_connsp_2(X0_54,sK2,sK5)
% 2.27/1.00      | m1_subset_1(sK0(sK2,sK5,X0_54),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3383]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5578,plain,
% 2.27/1.00      ( ~ m1_connsp_2(u1_struct_0(sK4),sK2,sK5)
% 2.27/1.00      | m1_subset_1(sK0(sK2,sK5,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_4978]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5583,plain,
% 2.27/1.00      ( m1_connsp_2(u1_struct_0(sK4),sK2,sK5) != iProver_top
% 2.27/1.00      | m1_subset_1(sK0(sK2,sK5,u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.27/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_5578]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_8,plain,
% 2.27/1.00      ( m1_connsp_2(X0,X1,X2)
% 2.27/1.00      | ~ v3_pre_topc(X0,X1)
% 2.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.00      | ~ r2_hidden(X2,X0)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1545,plain,
% 2.27/1.00      ( m1_connsp_2(X0,X1,X2)
% 2.27/1.00      | ~ v3_pre_topc(X0,X1)
% 2.27/1.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.00      | ~ r2_hidden(X2,X0)
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | sK2 != X1 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_33]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1546,plain,
% 2.27/1.00      ( m1_connsp_2(X0,sK2,X1)
% 2.27/1.00      | ~ v3_pre_topc(X0,sK2)
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | ~ r2_hidden(X1,X0)
% 2.27/1.00      | v2_struct_0(sK2)
% 2.27/1.00      | ~ l1_pre_topc(sK2) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_1545]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1550,plain,
% 2.27/1.00      ( m1_connsp_2(X0,sK2,X1)
% 2.27/1.00      | ~ v3_pre_topc(X0,sK2)
% 2.27/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | ~ r2_hidden(X1,X0) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_1546,c_34,c_32]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3381,plain,
% 2.27/1.00      ( m1_connsp_2(X0_54,sK2,X1_54)
% 2.27/1.00      | ~ v3_pre_topc(X0_54,sK2)
% 2.27/1.00      | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
% 2.27/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | ~ r2_hidden(X1_54,X0_54) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_1550]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5006,plain,
% 2.27/1.00      ( m1_connsp_2(u1_struct_0(sK4),sK2,X0_54)
% 2.27/1.00      | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
% 2.27/1.00      | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
% 2.27/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | ~ r2_hidden(X0_54,u1_struct_0(sK4)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3381]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5502,plain,
% 2.27/1.00      ( m1_connsp_2(u1_struct_0(sK4),sK2,sK5)
% 2.27/1.00      | ~ v3_pre_topc(u1_struct_0(sK4),sK2)
% 2.27/1.00      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 2.27/1.00      | ~ r2_hidden(sK5,u1_struct_0(sK4)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_5006]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5503,plain,
% 2.27/1.00      ( m1_connsp_2(u1_struct_0(sK4),sK2,sK5) = iProver_top
% 2.27/1.00      | v3_pre_topc(u1_struct_0(sK4),sK2) != iProver_top
% 2.27/1.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.27/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 2.27/1.00      | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_5502]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3413,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5332,plain,
% 2.27/1.00      ( u1_struct_0(sK4) = u1_struct_0(sK4) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3413]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3417,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0_54,X1_54)
% 2.27/1.00      | m1_subset_1(X2_54,X3_54)
% 2.27/1.00      | X2_54 != X0_54
% 2.27/1.00      | X3_54 != X1_54 ),
% 2.27/1.00      theory(equality) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5123,plain,
% 2.27/1.00      ( m1_subset_1(X0_54,X1_54)
% 2.27/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.27/1.00      | X1_54 != u1_struct_0(sK4)
% 2.27/1.00      | X0_54 != sK6 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3417]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5270,plain,
% 2.27/1.00      ( m1_subset_1(sK5,X0_54)
% 2.27/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.27/1.00      | X0_54 != u1_struct_0(sK4)
% 2.27/1.00      | sK5 != sK6 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_5123]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5331,plain,
% 2.27/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4))
% 2.27/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.27/1.00      | u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.27/1.00      | sK5 != sK6 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_5270]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5333,plain,
% 2.27/1.00      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 2.27/1.00      | sK5 != sK6
% 2.27/1.00      | m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top
% 2.27/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_5331]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5017,plain,
% 2.27/1.00      ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6)
% 2.27/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3631]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5018,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,sK1,sK3,sK6) != iProver_top
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top
% 2.27/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_5017]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_7,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.27/1.00      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_2,plain,
% 2.27/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | v2_pre_topc(X0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1088,plain,
% 2.27/1.00      ( ~ l1_pre_topc(X0)
% 2.27/1.00      | ~ v2_pre_topc(X0)
% 2.27/1.00      | v2_pre_topc(X1)
% 2.27/1.00      | sK2 != X0
% 2.27/1.00      | sK4 != X1 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_26]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1089,plain,
% 2.27/1.00      ( ~ l1_pre_topc(sK2) | ~ v2_pre_topc(sK2) | v2_pre_topc(sK4) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_1088]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1091,plain,
% 2.27/1.00      ( v2_pre_topc(sK4) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_1089,c_33,c_32]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1950,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.27/1.00      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | sK4 != X1 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_1091]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1951,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.27/1.00      | r2_hidden(X0,k1_connsp_2(sK4,X0))
% 2.27/1.00      | v2_struct_0(sK4)
% 2.27/1.00      | ~ l1_pre_topc(sK4) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_1950]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3,plain,
% 2.27/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.27/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1077,plain,
% 2.27/1.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X0 | sK4 != X1 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_26]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1078,plain,
% 2.27/1.00      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_1077]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1955,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.27/1.00      | r2_hidden(X0,k1_connsp_2(sK4,X0)) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_1951,c_32,c_28,c_1078]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3362,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 2.27/1.00      | r2_hidden(X0_54,k1_connsp_2(sK4,X0_54)) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_1955]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5014,plain,
% 2.27/1.00      ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
% 2.27/1.00      | r2_hidden(sK6,k1_connsp_2(sK4,sK6)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3362]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5015,plain,
% 2.27/1.00      ( m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top
% 2.27/1.00      | r2_hidden(sK6,k1_connsp_2(sK4,sK6)) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_5014]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.27/1.00      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1989,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.27/1.00      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.00      | v2_struct_0(X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | sK4 != X1 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_1091]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1990,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.27/1.00      | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.27/1.00      | v2_struct_0(sK4)
% 2.27/1.00      | ~ l1_pre_topc(sK4) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_1989]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1994,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.27/1.00      | m1_subset_1(k1_connsp_2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_1990,c_32,c_28,c_1078]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3360,plain,
% 2.27/1.00      ( ~ m1_subset_1(X0_54,u1_struct_0(sK4))
% 2.27/1.00      | m1_subset_1(k1_connsp_2(sK4,X0_54),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_1994]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5011,plain,
% 2.27/1.00      ( m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.27/1.00      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3360]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_5012,plain,
% 2.27/1.00      ( m1_subset_1(k1_connsp_2(sK4,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.27/1.00      | m1_subset_1(sK6,u1_struct_0(sK4)) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_5011]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_22,negated_conjecture,
% 2.27/1.00      ( r1_tmap_1(sK2,sK1,sK3,sK5)
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 2.27/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3400,negated_conjecture,
% 2.27/1.00      ( r1_tmap_1(sK2,sK1,sK3,sK5)
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_4518,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_3400]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_23,negated_conjecture,
% 2.27/1.00      ( sK5 = sK6 ),
% 2.27/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3399,negated_conjecture,
% 2.27/1.00      ( sK5 = sK6 ),
% 2.27/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_4609,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,sK1,sK3,sK6) = iProver_top
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
% 2.27/1.00      inference(light_normalisation,[status(thm)],[c_4518,c_3399]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_3436,plain,
% 2.27/1.00      ( sK3 = sK3 ),
% 2.27/1.00      inference(instantiation,[status(thm)],[c_3413]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_17,plain,
% 2.27/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.27/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.00      | ~ l1_pre_topc(X1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1048,plain,
% 2.27/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | sK2 != X1
% 2.27/1.00      | sK4 != X0 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1049,plain,
% 2.27/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.27/1.00      | ~ l1_pre_topc(sK2) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_1048]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_1050,plain,
% 2.27/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.27/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_1049]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_16,plain,
% 2.27/1.00      ( ~ v1_tsep_1(X0,X1)
% 2.27/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.27/1.00      | ~ m1_pre_topc(X0,X1)
% 2.27/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(cnf_transformation,[],[f98]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_208,plain,
% 2.27/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.27/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.27/1.00      | ~ v1_tsep_1(X0,X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(global_propositional_subsumption,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_16,c_17]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_209,plain,
% 2.27/1.00      ( ~ v1_tsep_1(X0,X1)
% 2.27/1.00      | v3_pre_topc(u1_struct_0(X0),X1)
% 2.27/1.00      | ~ m1_pre_topc(X0,X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1) ),
% 2.27/1.00      inference(renaming,[status(thm)],[c_208]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_27,negated_conjecture,
% 2.27/1.00      ( v1_tsep_1(sK4,sK2) ),
% 2.27/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_561,plain,
% 2.27/1.00      ( v3_pre_topc(u1_struct_0(X0),X1)
% 2.27/1.00      | ~ m1_pre_topc(X0,X1)
% 2.27/1.00      | ~ l1_pre_topc(X1)
% 2.27/1.00      | ~ v2_pre_topc(X1)
% 2.27/1.00      | sK2 != X1
% 2.27/1.00      | sK4 != X0 ),
% 2.27/1.00      inference(resolution_lifted,[status(thm)],[c_209,c_27]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_562,plain,
% 2.27/1.00      ( v3_pre_topc(u1_struct_0(sK4),sK2)
% 2.27/1.00      | ~ m1_pre_topc(sK4,sK2)
% 2.27/1.00      | ~ l1_pre_topc(sK2)
% 2.27/1.00      | ~ v2_pre_topc(sK2) ),
% 2.27/1.00      inference(unflattening,[status(thm)],[c_561]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_563,plain,
% 2.27/1.00      ( v3_pre_topc(u1_struct_0(sK4),sK2) = iProver_top
% 2.27/1.00      | m1_pre_topc(sK4,sK2) != iProver_top
% 2.27/1.00      | l1_pre_topc(sK2) != iProver_top
% 2.27/1.00      | v2_pre_topc(sK2) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_21,negated_conjecture,
% 2.27/1.00      ( ~ r1_tmap_1(sK2,sK1,sK3,sK5)
% 2.27/1.00      | ~ r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) ),
% 2.27/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_53,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,sK1,sK3,sK5) != iProver_top
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) != iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_52,plain,
% 2.27/1.00      ( r1_tmap_1(sK2,sK1,sK3,sK5) = iProver_top
% 2.27/1.00      | r1_tmap_1(sK4,sK1,k2_tmap_1(sK2,sK1,sK3,sK4),sK6) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_24,negated_conjecture,
% 2.27/1.00      ( m1_subset_1(sK6,u1_struct_0(sK4)) ),
% 2.27/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_51,plain,
% 2.27/1.00      ( m1_subset_1(sK6,u1_struct_0(sK4)) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_25,negated_conjecture,
% 2.27/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.27/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_50,plain,
% 2.27/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_49,plain,
% 2.27/1.00      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_43,plain,
% 2.27/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(c_42,plain,
% 2.27/1.00      ( v2_pre_topc(sK2) = iProver_top ),
% 2.27/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.27/1.00  
% 2.27/1.00  cnf(contradiction,plain,
% 2.27/1.00      ( $false ),
% 2.27/1.00      inference(minisat,
% 2.27/1.00                [status(thm)],
% 2.27/1.00                [c_6420,c_6408,c_5724,c_5704,c_5657,c_5623,c_5589,c_5587,
% 2.27/1.00                 c_5583,c_5503,c_5332,c_5333,c_5018,c_5015,c_5012,c_4609,
% 2.27/1.00                 c_3399,c_3436,c_1050,c_563,c_53,c_52,c_51,c_50,c_49,
% 2.27/1.00                 c_43,c_42]) ).
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.27/1.00  
% 2.27/1.00  ------                               Statistics
% 2.27/1.00  
% 2.27/1.00  ------ General
% 2.27/1.00  
% 2.27/1.00  abstr_ref_over_cycles:                  0
% 2.27/1.00  abstr_ref_under_cycles:                 0
% 2.27/1.00  gc_basic_clause_elim:                   0
% 2.27/1.00  forced_gc_time:                         0
% 2.27/1.00  parsing_time:                           0.011
% 2.27/1.00  unif_index_cands_time:                  0.
% 2.27/1.00  unif_index_add_time:                    0.
% 2.27/1.00  orderings_time:                         0.
% 2.27/1.00  out_proof_time:                         0.015
% 2.27/1.00  total_time:                             0.197
% 2.27/1.00  num_of_symbols:                         63
% 2.27/1.00  num_of_terms:                           4577
% 2.27/1.00  
% 2.27/1.00  ------ Preprocessing
% 2.27/1.00  
% 2.27/1.00  num_of_splits:                          4
% 2.27/1.00  num_of_split_atoms:                     4
% 2.27/1.00  num_of_reused_defs:                     0
% 2.27/1.00  num_eq_ax_congr_red:                    24
% 2.27/1.00  num_of_sem_filtered_clauses:            1
% 2.27/1.00  num_of_subtypes:                        2
% 2.27/1.00  monotx_restored_types:                  0
% 2.27/1.00  sat_num_of_epr_types:                   0
% 2.27/1.00  sat_num_of_non_cyclic_types:            0
% 2.27/1.00  sat_guarded_non_collapsed_types:        0
% 2.27/1.00  num_pure_diseq_elim:                    0
% 2.27/1.00  simp_replaced_by:                       0
% 2.27/1.00  res_preprocessed:                       158
% 2.27/1.00  prep_upred:                             0
% 2.27/1.00  prep_unflattend:                        134
% 2.27/1.00  smt_new_axioms:                         0
% 2.27/1.00  pred_elim_cands:                        14
% 2.27/1.00  pred_elim:                              7
% 2.27/1.00  pred_elim_cl:                           -7
% 2.27/1.00  pred_elim_cycles:                       17
% 2.27/1.00  merged_defs:                            6
% 2.27/1.00  merged_defs_ncl:                        0
% 2.27/1.00  bin_hyper_res:                          6
% 2.27/1.00  prep_cycles:                            3
% 2.27/1.00  pred_elim_time:                         0.068
% 2.27/1.00  splitting_time:                         0.
% 2.27/1.00  sem_filter_time:                        0.
% 2.27/1.00  monotx_time:                            0.
% 2.27/1.00  subtype_inf_time:                       0.
% 2.27/1.00  
% 2.27/1.00  ------ Problem properties
% 2.27/1.00  
% 2.27/1.00  clauses:                                48
% 2.27/1.00  conjectures:                            6
% 2.27/1.00  epr:                                    2
% 2.27/1.00  horn:                                   46
% 2.27/1.00  ground:                                 12
% 2.27/1.00  unary:                                  6
% 2.27/1.00  binary:                                 9
% 2.27/1.00  lits:                                   144
% 2.27/1.00  lits_eq:                                7
% 2.27/1.00  fd_pure:                                0
% 2.27/1.00  fd_pseudo:                              0
% 2.27/1.00  fd_cond:                                0
% 2.27/1.00  fd_pseudo_cond:                         0
% 2.27/1.00  ac_symbols:                             0
% 2.27/1.00  
% 2.27/1.00  ------ Propositional Solver
% 2.27/1.00  
% 2.27/1.00  prop_solver_calls:                      24
% 2.27/1.00  prop_fast_solver_calls:                 2107
% 2.27/1.00  smt_solver_calls:                       0
% 2.27/1.00  smt_fast_solver_calls:                  0
% 2.27/1.00  prop_num_of_clauses:                    1640
% 2.27/1.00  prop_preprocess_simplified:             5932
% 2.27/1.00  prop_fo_subsumed:                       115
% 2.27/1.00  prop_solver_time:                       0.
% 2.27/1.00  smt_solver_time:                        0.
% 2.27/1.00  smt_fast_solver_time:                   0.
% 2.27/1.00  prop_fast_solver_time:                  0.
% 2.27/1.00  prop_unsat_core_time:                   0.
% 2.27/1.00  
% 2.27/1.00  ------ QBF
% 2.27/1.00  
% 2.27/1.00  qbf_q_res:                              0
% 2.27/1.00  qbf_num_tautologies:                    0
% 2.27/1.00  qbf_prep_cycles:                        0
% 2.27/1.00  
% 2.27/1.00  ------ BMC1
% 2.27/1.00  
% 2.27/1.00  bmc1_current_bound:                     -1
% 2.27/1.00  bmc1_last_solved_bound:                 -1
% 2.27/1.00  bmc1_unsat_core_size:                   -1
% 2.27/1.00  bmc1_unsat_core_parents_size:           -1
% 2.27/1.00  bmc1_merge_next_fun:                    0
% 2.27/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.27/1.00  
% 2.27/1.00  ------ Instantiation
% 2.27/1.00  
% 2.27/1.00  inst_num_of_clauses:                    318
% 2.27/1.00  inst_num_in_passive:                    63
% 2.27/1.00  inst_num_in_active:                     254
% 2.27/1.00  inst_num_in_unprocessed:                0
% 2.27/1.00  inst_num_of_loops:                      271
% 2.27/1.00  inst_num_of_learning_restarts:          0
% 2.27/1.00  inst_num_moves_active_passive:          12
% 2.27/1.00  inst_lit_activity:                      0
% 2.27/1.00  inst_lit_activity_moves:                0
% 2.27/1.00  inst_num_tautologies:                   0
% 2.27/1.00  inst_num_prop_implied:                  0
% 2.27/1.00  inst_num_existing_simplified:           0
% 2.27/1.00  inst_num_eq_res_simplified:             0
% 2.27/1.00  inst_num_child_elim:                    0
% 2.27/1.00  inst_num_of_dismatching_blockings:      7
% 2.27/1.00  inst_num_of_non_proper_insts:           263
% 2.27/1.00  inst_num_of_duplicates:                 0
% 2.27/1.00  inst_inst_num_from_inst_to_res:         0
% 2.27/1.00  inst_dismatching_checking_time:         0.
% 2.27/1.00  
% 2.27/1.00  ------ Resolution
% 2.27/1.00  
% 2.27/1.00  res_num_of_clauses:                     0
% 2.27/1.00  res_num_in_passive:                     0
% 2.27/1.00  res_num_in_active:                      0
% 2.27/1.00  res_num_of_loops:                       161
% 2.27/1.00  res_forward_subset_subsumed:            40
% 2.27/1.00  res_backward_subset_subsumed:           0
% 2.27/1.00  res_forward_subsumed:                   0
% 2.27/1.00  res_backward_subsumed:                  0
% 2.27/1.00  res_forward_subsumption_resolution:     6
% 2.27/1.00  res_backward_subsumption_resolution:    0
% 2.27/1.00  res_clause_to_clause_subsumption:       241
% 2.27/1.00  res_orphan_elimination:                 0
% 2.27/1.00  res_tautology_del:                      80
% 2.27/1.00  res_num_eq_res_simplified:              2
% 2.27/1.00  res_num_sel_changes:                    0
% 2.27/1.00  res_moves_from_active_to_pass:          0
% 2.27/1.00  
% 2.27/1.00  ------ Superposition
% 2.27/1.00  
% 2.27/1.00  sup_time_total:                         0.
% 2.27/1.00  sup_time_generating:                    0.
% 2.27/1.00  sup_time_sim_full:                      0.
% 2.27/1.00  sup_time_sim_immed:                     0.
% 2.27/1.00  
% 2.27/1.00  sup_num_of_clauses:                     72
% 2.27/1.00  sup_num_in_active:                      54
% 2.27/1.00  sup_num_in_passive:                     18
% 2.27/1.00  sup_num_of_loops:                       54
% 2.27/1.00  sup_fw_superposition:                   16
% 2.27/1.00  sup_bw_superposition:                   13
% 2.27/1.00  sup_immediate_simplified:               1
% 2.27/1.00  sup_given_eliminated:                   0
% 2.27/1.00  comparisons_done:                       0
% 2.27/1.00  comparisons_avoided:                    0
% 2.27/1.00  
% 2.27/1.00  ------ Simplifications
% 2.27/1.00  
% 2.27/1.00  
% 2.27/1.00  sim_fw_subset_subsumed:                 1
% 2.27/1.00  sim_bw_subset_subsumed:                 0
% 2.27/1.00  sim_fw_subsumed:                        1
% 2.27/1.00  sim_bw_subsumed:                        0
% 2.27/1.00  sim_fw_subsumption_res:                 0
% 2.27/1.00  sim_bw_subsumption_res:                 0
% 2.27/1.00  sim_tautology_del:                      1
% 2.27/1.00  sim_eq_tautology_del:                   0
% 2.27/1.00  sim_eq_res_simp:                        2
% 2.27/1.00  sim_fw_demodulated:                     0
% 2.27/1.00  sim_bw_demodulated:                     0
% 2.27/1.00  sim_light_normalised:                   3
% 2.27/1.00  sim_joinable_taut:                      0
% 2.27/1.00  sim_joinable_simp:                      0
% 2.27/1.00  sim_ac_normalised:                      0
% 2.27/1.00  sim_smt_subsumption:                    0
% 2.27/1.00  
%------------------------------------------------------------------------------
