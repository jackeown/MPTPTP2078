%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1749+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:20 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :  190 (2831 expanded)
%              Number of clauses        :  127 ( 702 expanded)
%              Number of leaves         :   16 (1065 expanded)
%              Depth                    :   30
%              Number of atoms          : 1069 (38183 expanded)
%              Number of equality atoms :  409 (3769 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   36 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f35,plain,(
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
     => ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK5)
        & ! [X5] :
            ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(sK5,X5)
            | ~ r2_hidden(X5,u1_struct_0(X2))
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
        & v1_funct_2(sK5,u1_struct_0(X2),u1_struct_0(X0))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
            ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK4,X2),X4)
            & ! [X5] :
                ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),sK4,X5) = k1_funct_1(X4,X5)
                | ~ r2_hidden(X5,u1_struct_0(X2))
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
            & v1_funct_1(X4) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
                ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK3),X4)
                & ! [X5] :
                    ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
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

fof(f32,plain,(
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
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK2,X0,X3,X2),X4)
                    & ! [X5] :
                        ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5)
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

fof(f31,plain,
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
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X1,sK1,X3,X2),X4)
                      & ! [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(sK1),X3,X5) = k1_funct_1(X4,X5)
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

fof(f36,plain,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5)
    & ! [X5] :
        ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X5) = k1_funct_1(sK5,X5)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f28,f35,f34,f33,f32,f31])).

fof(f61,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f29,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,X3)
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X1,X2,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
        & r2_hidden(sK0(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ( k3_funct_2(X0,X1,X2,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
                        & r2_hidden(sK0(X0,X1,X2,X3,X4),X3)
                        & m1_subset_1(sK0(X0,X1,X2,X3,X4),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f29])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = X4
      | m1_subset_1(sK0(X0,X1,X2,X3,X4),X0)
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
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = X4
      | r2_hidden(sK0(X0,X1,X2,X3,X4),X3)
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
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X5] :
      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X5) = k1_funct_1(sK5,X5)
      | ~ r2_hidden(X5,u1_struct_0(sK3))
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f55,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = X4
      | k3_funct_2(X0,X1,X2,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
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
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_735,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1143,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_732,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1146,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | m1_subset_1(sK0(X1,X2,X0,X4,X3),X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_partfun1(X1,X2,X0,X4) = X3 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_737,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X1_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | m1_subset_1(sK0(X1_53,X2_53,X0_53,X4_53,X3_53),X1_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X4_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X4_53) = X3_53 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1141,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = X4_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X4_53,X3_53,X1_53) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X3_53,X1_53))) != iProver_top
    | m1_subset_1(sK0(X0_53,X1_53,X2_53,X3_53,X4_53),X0_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X3_53) = iProver_top
    | v1_funct_1(X4_53) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | r2_hidden(sK0(X1,X2,X0,X4,X3),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_partfun1(X1,X2,X0,X4) = X3 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_738,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | r2_hidden(sK0(X1_53,X2_53,X0_53,X4_53,X3_53),X4_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X1_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X4_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X4_53) = X3_53 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1140,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = X4_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X4_53,X3_53,X1_53) != iProver_top
    | r2_hidden(sK0(X0_53,X1_53,X2_53,X3_53,X4_53),X3_53) = iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X3_53,X1_53))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X3_53) = iProver_top
    | v1_funct_1(X4_53) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0) = k1_funct_1(sK5,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_736,negated_conjecture,
    ( ~ r2_hidden(X0_53,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_53,u1_struct_0(sK2))
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53) = k1_funct_1(sK5,X0_53) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1142,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53) = k1_funct_1(sK5,X0_53)
    | r2_hidden(X0_53,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_1644,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(X0_53,X1_53,X2_53,u1_struct_0(sK3),X3_53)) = k1_funct_1(sK5,sK0(X0_53,X1_53,X2_53,u1_struct_0(sK3),X3_53))
    | k2_partfun1(X0_53,X1_53,X2_53,u1_struct_0(sK3)) = X3_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X3_53,u1_struct_0(sK3),X1_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X1_53))) != iProver_top
    | m1_subset_1(sK0(X0_53,X1_53,X2_53,u1_struct_0(sK3),X3_53),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1140,c_1142])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_33,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_286,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_428,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_19])).

cnf(c_429,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_431,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_21])).

cnf(c_531,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_286,c_431])).

cnf(c_532,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | v2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_533,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_2573,plain,
    ( v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK0(X0_53,X1_53,X2_53,u1_struct_0(sK3),X3_53),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X1_53))) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_2(X3_53,u1_struct_0(sK3),X1_53) != iProver_top
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | k2_partfun1(X0_53,X1_53,X2_53,u1_struct_0(sK3)) = X3_53
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(X0_53,X1_53,X2_53,u1_struct_0(sK3),X3_53)) = k1_funct_1(sK5,sK0(X0_53,X1_53,X2_53,u1_struct_0(sK3),X3_53))
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1644,c_33,c_533])).

cnf(c_2574,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(X0_53,X1_53,X2_53,u1_struct_0(sK3),X3_53)) = k1_funct_1(sK5,sK0(X0_53,X1_53,X2_53,u1_struct_0(sK3),X3_53))
    | k2_partfun1(X0_53,X1_53,X2_53,u1_struct_0(sK3)) = X3_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X3_53,u1_struct_0(sK3),X1_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X1_53))) != iProver_top
    | m1_subset_1(sK0(X0_53,X1_53,X2_53,u1_struct_0(sK3),X3_53),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2573])).

cnf(c_2591,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),X0_53,X1_53,u1_struct_0(sK3),X2_53)) = k1_funct_1(sK5,sK0(u1_struct_0(sK2),X0_53,X1_53,u1_struct_0(sK3),X2_53))
    | k2_partfun1(u1_struct_0(sK2),X0_53,X1_53,u1_struct_0(sK3)) = X2_53
    | v1_funct_2(X1_53,u1_struct_0(sK2),X0_53) != iProver_top
    | v1_funct_2(X2_53,u1_struct_0(sK3),X0_53) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0_53))) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_53))) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_2574])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_30,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_32,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_10,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_417,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_418,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_419,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_509,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_286,c_21])).

cnf(c_510,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_511,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_3323,plain,
    ( m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_53))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0_53))) != iProver_top
    | v1_funct_2(X2_53,u1_struct_0(sK3),X0_53) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),X0_53) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),X0_53,X1_53,u1_struct_0(sK3)) = X2_53
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),X0_53,X1_53,u1_struct_0(sK3),X2_53)) = k1_funct_1(sK5,sK0(u1_struct_0(sK2),X0_53,X1_53,u1_struct_0(sK3),X2_53))
    | v1_xboole_0(X0_53) = iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2591,c_30,c_32,c_33,c_419,c_511,c_533])).

cnf(c_3324,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),X0_53,X1_53,u1_struct_0(sK3),X2_53)) = k1_funct_1(sK5,sK0(u1_struct_0(sK2),X0_53,X1_53,u1_struct_0(sK3),X2_53))
    | k2_partfun1(u1_struct_0(sK2),X0_53,X1_53,u1_struct_0(sK3)) = X2_53
    | v1_funct_2(X1_53,u1_struct_0(sK2),X0_53) != iProver_top
    | v1_funct_2(X2_53,u1_struct_0(sK3),X0_53) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0_53))) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),X0_53))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_3323])).

cnf(c_3338,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),X0_53)) = k1_funct_1(sK5,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),X0_53))
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = X0_53
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_3324])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_741,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1137,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_1507,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53) = k7_relat_1(sK4,X0_53)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_1137])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1385,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(instantiation,[status(thm)],[c_741])).

cnf(c_2110,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1507,c_18,c_16,c_1385])).

cnf(c_3386,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),X0_53)) = k1_funct_1(sK5,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),X0_53))
    | k7_relat_1(sK4,u1_struct_0(sK3)) = X0_53
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3338,c_2110])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_27,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_29,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_35,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_36,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_66,plain,
    ( v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_68,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_70,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_72,plain,
    ( l1_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_3467,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | k7_relat_1(sK4,u1_struct_0(sK3)) = X0_53
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),X0_53)) = k1_funct_1(sK5,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),X0_53))
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3386,c_27,c_29,c_35,c_36,c_68,c_72])).

cnf(c_3468,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),X0_53)) = k1_funct_1(sK5,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),X0_53))
    | k7_relat_1(sK4,u1_struct_0(sK3)) = X0_53
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_3467])).

cnf(c_3478,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),sK5))
    | k7_relat_1(sK4,u1_struct_0(sK3)) = sK5
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_3468])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_14,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3518,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),sK5))
    | k7_relat_1(sK4,u1_struct_0(sK3)) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3478])).

cnf(c_3523,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),sK5))
    | k7_relat_1(sK4,u1_struct_0(sK3)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3478,c_15,c_14,c_3518])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_740,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ m1_subset_1(X3_53,X1_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_xboole_0(X1_53)
    | ~ v1_funct_1(X0_53)
    | k3_funct_2(X1_53,X2_53,X0_53,X3_53) = k1_funct_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1138,plain,
    ( k3_funct_2(X0_53,X1_53,X2_53,X3_53) = k1_funct_1(X2_53,X3_53)
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | m1_subset_1(X3_53,X0_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_1530,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53) = k1_funct_1(sK4,X0_53)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_1138])).

cnf(c_2308,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53) = k1_funct_1(sK4,X0_53)
    | m1_subset_1(X0_53,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1530,c_30,c_35,c_36,c_511])).

cnf(c_2316,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),X0_53,X1_53,X2_53,X3_53)) = k1_funct_1(sK4,sK0(u1_struct_0(sK2),X0_53,X1_53,X2_53,X3_53))
    | k2_partfun1(u1_struct_0(sK2),X0_53,X1_53,X2_53) = X3_53
    | v1_funct_2(X3_53,X2_53,X0_53) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),X0_53) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X0_53))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0_53))) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_2308])).

cnf(c_2453,plain,
    ( v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X0_53))) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),X0_53) != iProver_top
    | v1_funct_2(X3_53,X2_53,X0_53) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),X0_53,X1_53,X2_53) = X3_53
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),X0_53,X1_53,X2_53,X3_53)) = k1_funct_1(sK4,sK0(u1_struct_0(sK2),X0_53,X1_53,X2_53,X3_53))
    | v1_funct_1(X3_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2316,c_30,c_511])).

cnf(c_2454,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),X0_53,X1_53,X2_53,X3_53)) = k1_funct_1(sK4,sK0(u1_struct_0(sK2),X0_53,X1_53,X2_53,X3_53))
    | k2_partfun1(u1_struct_0(sK2),X0_53,X1_53,X2_53) = X3_53
    | v1_funct_2(X3_53,X2_53,X0_53) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),X0_53) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X0_53))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X0_53))) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2453])).

cnf(c_2470,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53,X1_53)) = k1_funct_1(sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53,X1_53))
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_2454])).

cnf(c_2524,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53,X1_53)) = k1_funct_1(sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53,X1_53))
    | k7_relat_1(sK4,X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2470,c_2110])).

cnf(c_2887,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | v1_funct_2(X1_53,X0_53,u1_struct_0(sK1)) != iProver_top
    | k7_relat_1(sK4,X0_53) = X1_53
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53,X1_53)) = k1_funct_1(sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53,X1_53))
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2524,c_27,c_29,c_35,c_36,c_68,c_72])).

cnf(c_2888,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53,X1_53)) = k1_funct_1(sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,X0_53,X1_53))
    | k7_relat_1(sK4,X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2887])).

cnf(c_2900,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),sK5))
    | k7_relat_1(sK4,u1_struct_0(sK3)) = sK5
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_2888])).

cnf(c_2961,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_funct_1(sK5)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),sK5))
    | k7_relat_1(sK4,u1_struct_0(sK3)) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2900])).

cnf(c_2967,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),sK5)) = k1_funct_1(sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),sK5))
    | k7_relat_1(sK4,u1_struct_0(sK3)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2900,c_21,c_20,c_15,c_14,c_418,c_532,c_2961])).

cnf(c_3529,plain,
    ( k1_funct_1(sK4,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),sK5)) = k1_funct_1(sK5,sK0(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3),sK5))
    | k7_relat_1(sK4,u1_struct_0(sK3)) = sK5 ),
    inference(superposition,[status(thm)],[c_3523,c_2967])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_38,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_39,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_40,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
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
    | k3_funct_2(X1,X2,X0,sK0(X1,X2,X0,X4,X3)) != k1_funct_1(X3,sK0(X1,X2,X0,X4,X3))
    | k2_partfun1(X1,X2,X0,X4) = X3 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_739,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X1_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X4_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | k3_funct_2(X1_53,X2_53,X0_53,sK0(X1_53,X2_53,X0_53,X4_53,X3_53)) != k1_funct_1(X3_53,sK0(X1_53,X2_53,X0_53,X4_53,X3_53))
    | k2_partfun1(X1_53,X2_53,X0_53,X4_53) = X3_53 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1139,plain,
    ( k3_funct_2(X0_53,X1_53,X2_53,sK0(X0_53,X1_53,X2_53,X3_53,X4_53)) != k1_funct_1(X4_53,sK0(X0_53,X1_53,X2_53,X3_53,X4_53))
    | k2_partfun1(X0_53,X1_53,X2_53,X3_53) = X4_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X4_53,X3_53,X1_53) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X3_53,X1_53))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X3_53) = iProver_top
    | v1_funct_1(X4_53) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_3528,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = sK5
    | k7_relat_1(sK4,u1_struct_0(sK3)) = sK5
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3523,c_1139])).

cnf(c_3546,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK3)) = sK5
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3528,c_2110])).

cnf(c_3599,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK3)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3529,c_27,c_29,c_30,c_32,c_33,c_35,c_36,c_37,c_38,c_39,c_40,c_68,c_72,c_419,c_511,c_533,c_3546])).

cnf(c_6,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_11,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK4,sK3),sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_304,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_tmap_1(sK2,sK1,sK4,sK3) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK3) != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_305,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | sK5 != k2_tmap_1(sK2,sK1,sK4,sK3) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_729,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | sK5 != k2_tmap_1(sK2,sK1,sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_305])).

cnf(c_743,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3))
    | sP0_iProver_split
    | sK5 != k2_tmap_1(sK2,sK1,sK4,sK3) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_729])).

cnf(c_1149,plain,
    ( sK5 != k2_tmap_1(sK2,sK1,sK4,sK3)
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_742,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_729])).

cnf(c_1150,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_1230,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK3) != sK5
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK4,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1149,c_1150])).

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
    inference(cnf_transformation,[],[f37])).

cnf(c_384,plain,
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
    | sK2 != X1
    | sK3 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_385,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_389,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_23,c_22,c_21])).

cnf(c_390,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3) ),
    inference(renaming,[status(thm)],[c_389])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_475,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(X1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,X1,X0,sK3)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_390,c_25])).

cnf(c_476,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0,sK3) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_480,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_26,c_24])).

cnf(c_726,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0_53,sK3) ),
    inference(subtyping,[status(esa)],[c_480])).

cnf(c_1153,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_53,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,X0_53,sK3)
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_2228,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK2,sK1,sK4,sK3)
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_1153])).

cnf(c_2261,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK3) = k7_relat_1(sK4,u1_struct_0(sK3))
    | v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2228,c_2110])).

cnf(c_2596,plain,
    ( k2_tmap_1(sK2,sK1,sK4,sK3) = k7_relat_1(sK4,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2261,c_35,c_36])).

cnf(c_2658,plain,
    ( k7_relat_1(sK4,u1_struct_0(sK3)) != sK5
    | v1_funct_2(k7_relat_1(sK4,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1230,c_2596])).

cnf(c_3603,plain,
    ( sK5 != sK5
    | v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3599,c_2658])).

cnf(c_3607,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3603])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3607,c_40,c_39,c_38])).


%------------------------------------------------------------------------------
