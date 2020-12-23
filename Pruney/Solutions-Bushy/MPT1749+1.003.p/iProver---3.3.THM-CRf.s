%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1749+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:20 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  202 (1445 expanded)
%              Number of clauses        :  128 ( 330 expanded)
%              Number of leaves         :   21 ( 569 expanded)
%              Depth                    :   25
%              Number of atoms          : 1071 (20542 expanded)
%              Number of equality atoms :  278 (1703 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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
                             => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
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
                               => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5) ) )
                         => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
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
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
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
    inference(flattening,[],[f33])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
          & ! [X5] :
              ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
              | ~ r2_hidden(X5,u1_struct_0(X2))
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK6)
        & ! [X5] :
            ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(sK6,X5)
            | ~ r2_hidden(X5,u1_struct_0(X2))
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X0))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
              & ! [X5] :
                  ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                  | ~ r2_hidden(X5,u1_struct_0(X2))
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK5,X2),X4)
            & ! [X5] :
                ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),sK5,X5) = k1_funct_1(X4,X5)
                | ~ r2_hidden(X5,u1_struct_0(X2))
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                  & ! [X5] :
                      ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
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
                ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK4),X4)
                & ! [X5] :
                    ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                    | ~ r2_hidden(X5,u1_struct_0(sK4))
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X3) )
        & m1_pre_topc(sK4,X1)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
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
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK3,X0,X3,X2),X4)
                    & ! [X5] :
                        ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
                        | ~ r2_hidden(X5,u1_struct_0(X2))
                        | ~ m1_subset_1(X5,u1_struct_0(sK3)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(sK3),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK3)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                        & ! [X5] :
                            ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
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
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK2),k2_tmap_1(X1,sK2,X3,X2),X4)
                      & ! [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(sK2),X3,X5) = k1_funct_1(X4,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK2))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK2))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK2))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK2))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK3,sK2,sK5,sK4),sK6)
    & ! [X5] :
        ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X5) = k1_funct_1(sK6,X5)
        | ~ r2_hidden(X5,u1_struct_0(sK4))
        | ~ m1_subset_1(X5,u1_struct_0(sK3)) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f34,f44,f43,f42,f41,f40])).

fof(f77,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => ( r2_hidden(X5,X3)
                             => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                       => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,X3)
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X1,X2,sK1(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK1(X0,X1,X2,X3,X4))
        & r2_hidden(sK1(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK1(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ( k3_funct_2(X0,X1,X2,sK1(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK1(X0,X1,X2,X3,X4))
                        & r2_hidden(sK1(X0,X1,X2,X3,X4),X3)
                        & m1_subset_1(sK1(X0,X1,X2,X3,X4),X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f38])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = X4
      | m1_subset_1(sK1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = X4
      | r2_hidden(sK1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X5] :
      ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X5) = k1_funct_1(sK6,X5)
      | ~ r2_hidden(X5,u1_struct_0(sK4))
      | ~ m1_subset_1(X5,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f35])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f1])).

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
    inference(flattening,[],[f15])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
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

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f57])).

fof(f79,plain,(
    ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK3,sK2,sK5,sK4),sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = X4
      | k3_funct_2(X0,X1,X2,sK1(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK1(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1036,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1576,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1036])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1033,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1579,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1033])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | m1_subset_1(sK1(X1,X2,X0,X4,X3),X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_partfun1(X1,X2,X0,X4) = X3 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1040,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X1_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | m1_subset_1(sK1(X1_53,X2_53,X0_53,X4_53,X3_53),X1_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X4_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X4_53) = X3_53 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1572,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = X4_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X4_53,X3_53,X1_53) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X3_53,X1_53))) != iProver_top
    | m1_subset_1(sK1(X0_53,X1_53,X2_53,X3_53,X4_53),X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X3_53) = iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X4_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1040])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | r2_hidden(sK1(X1,X2,X0,X4,X3),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_partfun1(X1,X2,X0,X4) = X3 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1041,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | r2_hidden(sK1(X1_53,X2_53,X0_53,X4_53,X3_53),X4_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X1_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X4_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X4_53) = X3_53 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1571,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = X4_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X4_53,X3_53,X1_53) != iProver_top
    | r2_hidden(sK1(X0_53,X1_53,X2_53,X3_53,X4_53),X3_53) = iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X3_53,X1_53))) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X3_53) = iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X4_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1041])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0) = k1_funct_1(sK6,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1037,negated_conjecture,
    ( ~ r2_hidden(X0_53,u1_struct_0(sK4))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK3))
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_53) = k1_funct_1(sK6,X0_53) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1575,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,X0_53) = k1_funct_1(sK6,X0_53)
    | r2_hidden(X0_53,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1037])).

cnf(c_3170,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK1(X0_53,X1_53,X2_53,u1_struct_0(sK4),X3_53)) = k1_funct_1(sK6,sK1(X0_53,X1_53,X2_53,u1_struct_0(sK4),X3_53))
    | k2_partfun1(X0_53,X1_53,X2_53,u1_struct_0(sK4)) = X3_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X3_53,u1_struct_0(sK4),X1_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X1_53))) != iProver_top
    | m1_subset_1(sK1(X0_53,X1_53,X2_53,u1_struct_0(sK4),X3_53),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1571,c_1575])).

cnf(c_6,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_430,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_26])).

cnf(c_431,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_433,plain,
    ( l1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_28])).

cnf(c_525,plain,
    ( l1_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_433])).

cnf(c_526,plain,
    ( l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_527,plain,
    ( l1_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_9,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_538,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_539,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ l1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_540,plain,
    ( v1_xboole_0(u1_struct_0(sK4)) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1039,plain,
    ( r2_hidden(X0_53,X1_53)
    | ~ m1_subset_1(X0_53,X1_53)
    | v1_xboole_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1871,plain,
    ( r2_hidden(sK0(X0_53),X0_53)
    | ~ m1_subset_1(sK0(X0_53),X0_53)
    | v1_xboole_0(X0_53) ),
    inference(instantiation,[status(thm)],[c_1039])).

cnf(c_2822,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1871])).

cnf(c_2823,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2822])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1038,plain,
    ( ~ r2_hidden(X0_53,X1_53)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X2_53))
    | ~ v1_xboole_0(X2_53) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_4112,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(X0_53))
    | ~ v1_xboole_0(X0_53) ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_4118,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4112])).

cnf(c_8,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1043,plain,
    ( m1_subset_1(sK0(X0_53),X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_4228,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1043])).

cnf(c_4229,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4228])).

cnf(c_4298,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK1(X0_53,X1_53,X2_53,u1_struct_0(sK4),X3_53)) = k1_funct_1(sK6,sK1(X0_53,X1_53,X2_53,u1_struct_0(sK4),X3_53))
    | k2_partfun1(X0_53,X1_53,X2_53,u1_struct_0(sK4)) = X3_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X3_53,u1_struct_0(sK4),X1_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X1_53))) != iProver_top
    | m1_subset_1(sK1(X0_53,X1_53,X2_53,u1_struct_0(sK4),X3_53),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3170,c_527,c_540,c_2823,c_4118,c_4229])).

cnf(c_4315,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK1(u1_struct_0(sK3),X0_53,X1_53,u1_struct_0(sK4),X2_53)) = k1_funct_1(sK6,sK1(u1_struct_0(sK3),X0_53,X1_53,u1_struct_0(sK4),X2_53))
    | k2_partfun1(u1_struct_0(sK3),X0_53,X1_53,u1_struct_0(sK4)) = X2_53
    | v1_funct_2(X1_53,u1_struct_0(sK3),X0_53) != iProver_top
    | v1_funct_2(X2_53,u1_struct_0(sK4),X0_53) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_53))) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0_53))) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1572,c_4298])).

cnf(c_39,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_15,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_419,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_420,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_421,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_511,plain,
    ( l1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_28])).

cnf(c_512,plain,
    ( l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_513,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_549,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_30])).

cnf(c_550,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ l1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_551,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | l1_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_550])).

cnf(c_4700,plain,
    ( m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0_53))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_53))) != iProver_top
    | v1_funct_2(X2_53,u1_struct_0(sK4),X0_53) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK3),X0_53) != iProver_top
    | k2_partfun1(u1_struct_0(sK3),X0_53,X1_53,u1_struct_0(sK4)) = X2_53
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK1(u1_struct_0(sK3),X0_53,X1_53,u1_struct_0(sK4),X2_53)) = k1_funct_1(sK6,sK1(u1_struct_0(sK3),X0_53,X1_53,u1_struct_0(sK4),X2_53))
    | v1_xboole_0(X0_53) = iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4315,c_39,c_421,c_513,c_527,c_540,c_551])).

cnf(c_4701,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK1(u1_struct_0(sK3),X0_53,X1_53,u1_struct_0(sK4),X2_53)) = k1_funct_1(sK6,sK1(u1_struct_0(sK3),X0_53,X1_53,u1_struct_0(sK4),X2_53))
    | k2_partfun1(u1_struct_0(sK3),X0_53,X1_53,u1_struct_0(sK4)) = X2_53
    | v1_funct_2(X1_53,u1_struct_0(sK3),X0_53) != iProver_top
    | v1_funct_2(X2_53,u1_struct_0(sK4),X0_53) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_53))) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),X0_53))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4700])).

cnf(c_4715,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4),X0_53)) = k1_funct_1(sK6,sK1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4),X0_53))
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) = X0_53
    | v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1579,c_4701])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_386,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | sK3 != X1
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_26])).

cnf(c_387,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK3)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,X1,X0,sK4) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_391,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,X1,X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_30,c_29,c_28])).

cnf(c_392,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,X1,X0,sK4) ),
    inference(renaming,[status(thm)],[c_391])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_477,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(X1),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,X1,X0,sK4)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_392,c_32])).

cnf(c_478,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,X0,sK4) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_482,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),X0,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_33,c_31])).

cnf(c_1027,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),X0_53,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,X0_53,sK4) ),
    inference(subtyping,[status(esa)],[c_482])).

cnf(c_1585,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),X0_53,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,X0_53,sK4)
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1027])).

cnf(c_3636,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,sK5,sK4)
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1579,c_1585])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1127,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_3721,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) = k2_tmap_1(sK3,sK2,sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3636,c_25,c_24,c_23,c_1127])).

cnf(c_4847,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4),X0_53)) = k1_funct_1(sK6,sK1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4),X0_53))
    | k2_tmap_1(sK3,sK2,sK5,sK4) = X0_53
    | v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4715,c_3721])).

cnf(c_34,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_42,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_43,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_76,plain,
    ( v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_78,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_83,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_85,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_4875,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | k2_tmap_1(sK3,sK2,sK5,sK4) = X0_53
    | k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4),X0_53)) = k1_funct_1(sK6,sK1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4),X0_53))
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4847,c_34,c_36,c_42,c_43,c_78,c_85])).

cnf(c_4876,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4),X0_53)) = k1_funct_1(sK6,sK1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4),X0_53))
    | k2_tmap_1(sK3,sK2,sK5,sK4) = X0_53
    | v1_funct_2(X0_53,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4875])).

cnf(c_4886,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4),sK6)) = k1_funct_1(sK6,sK1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4),sK6))
    | k2_tmap_1(sK3,sK2,sK5,sK4) = sK6
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_4876])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_45,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_46,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_84,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_18,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK2),k2_tmap_1(sK3,sK2,sK5,sK4),sK6) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_365,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK3,sK2,sK5,sK4) != X0
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK4) != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_366,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
    | sK6 != k2_tmap_1(sK3,sK2,sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_1030,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
    | sK6 != k2_tmap_1(sK3,sK2,sK5,sK4) ),
    inference(subtyping,[status(esa)],[c_366])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1044,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ l1_struct_0(X2_54)
    | ~ l1_struct_0(X1_54)
    | ~ l1_struct_0(X0_54)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k2_tmap_1(X0_54,X1_54,X0_53,X2_54)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1947,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ l1_struct_0(X0_54)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK3,sK2,sK5,X0_54))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1044])).

cnf(c_2144,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK4)
    | v1_funct_1(k2_tmap_1(sK3,sK2,sK5,sK4))
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1947])).

cnf(c_1050,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_2283,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_1052,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_2710,plain,
    ( k2_tmap_1(sK3,sK2,sK5,sK4) != X0_53
    | sK6 != X0_53
    | sK6 = k2_tmap_1(sK3,sK2,sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_1052])).

cnf(c_4155,plain,
    ( k2_tmap_1(sK3,sK2,sK5,sK4) != sK6
    | sK6 = k2_tmap_1(sK3,sK2,sK5,sK4)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2710])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1046,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_53,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ l1_struct_0(X2_54)
    | ~ l1_struct_0(X1_54)
    | ~ l1_struct_0(X0_54)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1967,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | m1_subset_1(k2_tmap_1(sK3,sK2,sK5,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ l1_struct_0(X0_54)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_4156,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | m1_subset_1(k2_tmap_1(sK3,sK2,sK5,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1967])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1045,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | v1_funct_2(k2_tmap_1(X0_54,X1_54,X0_53,X2_54),u1_struct_0(X2_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ l1_struct_0(X2_54)
    | ~ l1_struct_0(X1_54)
    | ~ l1_struct_0(X0_54)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1957,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK2,sK5,X0_54),u1_struct_0(X0_54),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ l1_struct_0(X0_54)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_4176,plain,
    ( v1_funct_2(k2_tmap_1(sK3,sK2,sK5,sK4),u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK4)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1957])).

cnf(c_5013,plain,
    ( k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),sK5,sK1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4),sK6)) = k1_funct_1(sK6,sK1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4),sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4886,c_31,c_25,c_24,c_23,c_45,c_46,c_84,c_512,c_526,c_1030,c_2144,c_2283,c_4155,c_4156,c_4176])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k3_funct_2(X1,X2,X0,sK1(X1,X2,X0,X4,X3)) != k1_funct_1(X3,sK1(X1,X2,X0,X4,X3))
    | k2_partfun1(X1,X2,X0,X4) = X3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1042,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X1_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X4_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | k3_funct_2(X1_53,X2_53,X0_53,sK1(X1_53,X2_53,X0_53,X4_53,X3_53)) != k1_funct_1(X3_53,sK1(X1_53,X2_53,X0_53,X4_53,X3_53))
    | k2_partfun1(X1_53,X2_53,X0_53,X4_53) = X3_53 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1570,plain,
    ( k3_funct_2(X0_53,X1_53,X2_53,sK1(X0_53,X1_53,X2_53,X3_53,X4_53)) != k1_funct_1(X4_53,sK1(X0_53,X1_53,X2_53,X3_53,X4_53))
    | k2_partfun1(X0_53,X1_53,X2_53,X3_53) = X4_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X4_53,X3_53,X1_53) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X3_53,X1_53))) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X3_53) = iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X4_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1042])).

cnf(c_5016,plain,
    ( k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK2),sK5,u1_struct_0(sK4)) = sK6
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5013,c_1570])).

cnf(c_5017,plain,
    ( k2_tmap_1(sK3,sK2,sK5,sK4) = sK6
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5016,c_3721])).

cnf(c_47,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_44,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5017,c_4176,c_4156,c_4155,c_2283,c_2144,c_1030,c_551,c_540,c_527,c_526,c_513,c_512,c_421,c_85,c_84,c_78,c_47,c_46,c_45,c_44,c_23,c_43,c_24,c_42,c_25,c_39,c_36,c_31,c_34])).


%------------------------------------------------------------------------------
