%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:44 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  259 (5234 expanded)
%              Number of clauses        :  170 (1575 expanded)
%              Number of leaves         :   23 (1538 expanded)
%              Depth                    :   30
%              Number of atoms          : 1634 (48386 expanded)
%              Number of equality atoms :  610 (6439 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal clause size      :   24 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,u1_struct_0(X1))
                     => k1_funct_1(X2,X3) = X3 ) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,u1_struct_0(X1))
                       => k1_funct_1(X2,X3) = X3 ) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
          & ! [X3] :
              ( k1_funct_1(X2,X3) = X3
              | ~ r2_hidden(X3,u1_struct_0(X1))
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
     => ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3)
        & ! [X3] :
            ( k1_funct_1(sK3,X3) = X3
            | ~ r2_hidden(X3,u1_struct_0(X1))
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2)
            & ! [X3] :
                ( k1_funct_1(X2,X3) = X3
                | ~ r2_hidden(X3,u1_struct_0(sK2))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)
                & ! [X3] :
                    ( k1_funct_1(X2,X3) = X3
                    | ~ r2_hidden(X3,u1_struct_0(X1))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2)
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = X3
                  | ~ r2_hidden(X3,u1_struct_0(X1))
                  | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
    & ! [X3] :
        ( k1_funct_1(sK3,X3) = X3
        | ~ r2_hidden(X3,u1_struct_0(sK2))
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f54,f61,f60,f59])).

fof(f93,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f96,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f90,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f91,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f94,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f95,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f62])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f80,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f3])).

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

fof(f55,plain,(
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

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
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

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ? [X5] :
                          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f57,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
        & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      | ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
                        & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
                        & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f57])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f97,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f98,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f66])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,u1_struct_0(X1))
               => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
              | ~ r2_hidden(X2,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2014,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | m1_subset_1(k4_tmap_1(X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2624,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_subset_1(k4_tmap_1(X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2014])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1998,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_2640,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1998])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2001,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2637,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2001])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2018,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X0_53)
    | ~ m1_pre_topc(X0_53,X3_53)
    | ~ m1_pre_topc(X2_53,X3_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X3_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X3_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X3_53)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2620,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_54)
    | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_pre_topc(X0_53,X3_53) != iProver_top
    | m1_pre_topc(X2_53,X3_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X3_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X3_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X3_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2018])).

cnf(c_4312,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK2,X0_53,sK3)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2637,c_2620])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_36,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_37,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_38,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4637,plain,
    ( l1_pre_topc(X1_53) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK2,X0_53,sK3)
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4312,c_36,c_37,c_38,c_41,c_42])).

cnf(c_4638,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK2,X0_53,sK3)
    | m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_pre_topc(X0_53,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_53) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4637])).

cnf(c_4643,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2640,c_4638])).

cnf(c_17,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2010,plain,
    ( m1_pre_topc(X0_53,X0_53)
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2628,plain,
    ( m1_pre_topc(X0_53,X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2010])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2019,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X2_53,X0_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X0_53)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_54,X2_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2619,plain,
    ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_54,X2_53)
    | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2019])).

cnf(c_4105,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_53)) = k2_tmap_1(sK2,sK1,sK3,X0_53)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_53,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2637,c_2619])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_39,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_40,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2021,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2797,plain,
    ( ~ m1_pre_topc(sK2,X0_53)
    | ~ l1_pre_topc(X0_53)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2021])).

cnf(c_2798,plain,
    ( m1_pre_topc(sK2,X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2797])).

cnf(c_2800,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2798])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2023,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53)
    | v2_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2984,plain,
    ( ~ m1_pre_topc(sK2,X0_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X0_53)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2023])).

cnf(c_2985,plain,
    ( m1_pre_topc(sK2,X0_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2984])).

cnf(c_2987,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2985])).

cnf(c_4185,plain,
    ( m1_pre_topc(X0_53,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_53)) = k2_tmap_1(sK2,sK1,sK3,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4105,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_2800,c_2987])).

cnf(c_4186,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_53)) = k2_tmap_1(sK2,sK1,sK3,X0_53)
    | m1_pre_topc(X0_53,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4185])).

cnf(c_4191,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2628,c_4186])).

cnf(c_4194,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4191,c_38,c_40,c_2800])).

cnf(c_4645,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2)
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4643,c_4194])).

cnf(c_3244,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2010])).

cnf(c_3245,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3244])).

cnf(c_4651,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4645,c_36,c_37,c_38,c_40,c_2800,c_3245])).

cnf(c_23,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
    | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2006,plain,
    ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,k3_tmap_1(X2_53,X1_53,X0_53,X0_53,X0_54))
    | ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2632,plain,
    ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,k3_tmap_1(X2_53,X1_53,X0_53,X0_53,X0_54)) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2006])).

cnf(c_4653,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4651,c_2632])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4848,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4653,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2017,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | m1_subset_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | ~ l1_struct_0(X1_53)
    | ~ l1_struct_0(X2_53)
    | ~ l1_struct_0(X0_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2621,plain,
    ( v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) = iProver_top
    | l1_struct_0(X1_53) != iProver_top
    | l1_struct_0(X2_53) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2017])).

cnf(c_3,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2024,plain,
    ( ~ r2_funct_2(X0_54,X1_54,X2_54,X3_54)
    | ~ v1_funct_2(X2_54,X0_54,X1_54)
    | ~ v1_funct_2(X3_54,X0_54,X1_54)
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X2_54)
    | ~ v1_funct_1(X3_54)
    | X3_54 = X2_54 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2614,plain,
    ( X0_54 = X1_54
    | r2_funct_2(X2_54,X3_54,X1_54,X0_54) != iProver_top
    | v1_funct_2(X1_54,X2_54,X3_54) != iProver_top
    | v1_funct_2(X0_54,X2_54,X3_54) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2024])).

cnf(c_3898,plain,
    ( sK3 = X0_54
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2637,c_2614])).

cnf(c_4118,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | sK3 = X0_54
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3898,c_41,c_42])).

cnf(c_4119,plain,
    ( sK3 = X0_54
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_4118])).

cnf(c_4124,plain,
    ( k2_tmap_1(X0_53,sK1,X0_54,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(X0_53,sK1,X0_54,sK2)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_53,sK1,X0_54,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_53,sK1,X0_54,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2621,c_4119])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_102,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_104,plain,
    ( l1_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_2022,plain,
    ( l1_struct_0(X0_53)
    | ~ l1_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2784,plain,
    ( l1_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2022])).

cnf(c_2785,plain,
    ( l1_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2784])).

cnf(c_4212,plain,
    ( k2_tmap_1(X0_53,sK1,X0_54,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(X0_53,sK1,X0_54,sK2)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(X0_53,sK1,X0_54,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_tmap_1(X0_53,sK1,X0_54,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4124,c_38,c_40,c_104,c_2785,c_2800])).

cnf(c_4852,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4848,c_4212])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2015,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ l1_struct_0(X1_53)
    | ~ l1_struct_0(X2_53)
    | ~ l1_struct_0(X0_53)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3062,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1_53)
    | ~ l1_struct_0(X0_53)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_tmap_1(X0_53,sK1,X0_54,X1_53)) ),
    inference(instantiation,[status(thm)],[c_2015])).

cnf(c_3518,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_53)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_53))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3062])).

cnf(c_3724,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3518])).

cnf(c_3727,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3724])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2016,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | v1_funct_2(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),u1_struct_0(X2_53),u1_struct_0(X1_53))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ l1_struct_0(X1_53)
    | ~ l1_struct_0(X2_53)
    | ~ l1_struct_0(X0_53)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_4145,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2016])).

cnf(c_4146,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4145])).

cnf(c_4887,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4852,c_38,c_40,c_41,c_42,c_43,c_104,c_2785,c_2800,c_3727,c_4146])).

cnf(c_21,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2008,plain,
    ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54)
    | ~ v1_funct_2(X1_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X0_53,X2_53)
    | r2_hidden(sK0(X1_53,X2_53,X0_53,X0_54,X1_54),u1_struct_0(X0_53))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2630,plain,
    ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54) = iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | r2_hidden(sK0(X1_53,X2_53,X0_53,X0_54,X1_54),u1_struct_0(X0_53)) = iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2008])).

cnf(c_4894,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4887,c_2630])).

cnf(c_6260,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4894,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_2800,c_2987,c_3245])).

cnf(c_6261,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_6260])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2011,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53)))
    | ~ l1_pre_topc(X1_53) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2627,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53))) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2011])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2027,plain,
    ( ~ r2_hidden(X0_54,X1_54)
    | m1_subset_1(X0_54,X2_54)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X2_54)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2611,plain,
    ( r2_hidden(X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_54,X2_54) = iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X2_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2027])).

cnf(c_3384,plain,
    ( m1_pre_topc(X0_53,X1_53) != iProver_top
    | r2_hidden(X0_54,u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X1_53)) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2627,c_2611])).

cnf(c_6265,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(X0_53)) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_6261,c_3384])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k1_funct_1(sK3,X0) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2002,negated_conjecture,
    ( ~ r2_hidden(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK1))
    | k1_funct_1(sK3,X0_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2636,plain,
    ( k1_funct_1(sK3,X0_54) = X0_54
    | r2_hidden(X0_54,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2002])).

cnf(c_6264,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_6261,c_2636])).

cnf(c_6555,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_6265,c_6264])).

cnf(c_6851,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6555,c_38,c_40])).

cnf(c_6852,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_6851])).

cnf(c_6856,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2624,c_6852])).

cnf(c_26,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2029,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_2054,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2029])).

cnf(c_2,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2025,plain,
    ( r2_funct_2(X0_54,X1_54,X2_54,X2_54)
    | ~ v1_funct_2(X2_54,X0_54,X1_54)
    | ~ m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X2_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3167,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2025])).

cnf(c_2040,plain,
    ( ~ r2_funct_2(X0_54,X1_54,X2_54,X3_54)
    | r2_funct_2(X4_54,X5_54,X6_54,X7_54)
    | X4_54 != X0_54
    | X5_54 != X1_54
    | X6_54 != X2_54
    | X7_54 != X3_54 ),
    theory(equality)).

cnf(c_2767,plain,
    ( ~ r2_funct_2(X0_54,X1_54,X2_54,X3_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
    | k4_tmap_1(sK1,sK2) != X2_54
    | u1_struct_0(sK1) != X1_54
    | u1_struct_0(sK2) != X0_54
    | sK3 != X3_54 ),
    inference(instantiation,[status(thm)],[c_2040])).

cnf(c_3204,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | k4_tmap_1(sK1,sK2) != sK3
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2767])).

cnf(c_3297,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2029])).

cnf(c_3306,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2029])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2012,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | v2_struct_0(X1_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53)
    | v1_funct_1(k4_tmap_1(X1_53,X0_53)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3511,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2012])).

cnf(c_3512,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3511])).

cnf(c_14,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2013,plain,
    ( v1_funct_2(k4_tmap_1(X0_53,X1_53),u1_struct_0(X1_53),u1_struct_0(X0_53))
    | ~ m1_pre_topc(X1_53,X0_53)
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X0_53)
    | ~ v2_pre_topc(X0_53) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3710,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2013])).

cnf(c_3711,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3710])).

cnf(c_4123,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2624,c_4119])).

cnf(c_7098,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6856,c_36,c_37,c_38,c_40,c_30,c_29,c_28,c_26,c_2054,c_3167,c_3204,c_3297,c_3306,c_3512,c_3711,c_4123])).

cnf(c_22,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2007,plain,
    ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54)
    | ~ v1_funct_2(X1_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | m1_subset_1(sK0(X1_53,X2_53,X0_53,X0_54,X1_54),u1_struct_0(X2_53))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2631,plain,
    ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54) = iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X0_53,X2_53) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_subset_1(sK0(X1_53,X2_53,X0_53,X0_54,X1_54),u1_struct_0(X2_53)) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X2_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X2_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2007])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2026,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ m1_subset_1(X3_54,X1_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | v1_xboole_0(X1_54)
    | ~ v1_funct_1(X0_54)
    | k3_funct_2(X1_54,X2_54,X0_54,X3_54) = k1_funct_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2612,plain,
    ( k3_funct_2(X0_54,X1_54,X2_54,X3_54) = k1_funct_1(X2_54,X3_54)
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | m1_subset_1(X3_54,X0_54) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2026])).

cnf(c_3456,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = k1_funct_1(sK3,X0_54)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2637,c_2612])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2020,plain,
    ( v2_struct_0(X0_53)
    | ~ l1_struct_0(X0_53)
    | ~ v1_xboole_0(u1_struct_0(X0_53)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2748,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2020])).

cnf(c_2749,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2748])).

cnf(c_3736,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = k1_funct_1(sK3,X0_54)
    | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3456,c_38,c_39,c_40,c_41,c_42,c_2749,c_2785,c_2800])).

cnf(c_4571,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_53,sK2,X1_53,X0_54,X1_54)) = k1_funct_1(sK3,sK0(X0_53,sK2,X1_53,X0_54,X1_54))
    | r2_funct_2(u1_struct_0(X1_53),u1_struct_0(X0_53),k2_tmap_1(sK2,X0_53,X0_54,X1_53),X1_54) = iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X1_53),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(X1_53,sK2) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_2631,c_3736])).

cnf(c_4728,plain,
    ( v2_pre_topc(X0_53) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X0_53)))) != iProver_top
    | m1_pre_topc(X1_53,sK2) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X1_53),u1_struct_0(X0_53)) != iProver_top
    | r2_funct_2(u1_struct_0(X1_53),u1_struct_0(X0_53),k2_tmap_1(sK2,X0_53,X0_54,X1_53),X1_54) = iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_53,sK2,X1_53,X0_54,X1_54)) = k1_funct_1(sK3,sK0(X0_53,sK2,X1_53,X0_54,X1_54))
    | l1_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4571,c_37,c_38,c_39,c_40,c_2800,c_2987])).

cnf(c_4729,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_53,sK2,X1_53,X0_54,X1_54)) = k1_funct_1(sK3,sK0(X0_53,sK2,X1_53,X0_54,X1_54))
    | r2_funct_2(u1_struct_0(X1_53),u1_struct_0(X0_53),k2_tmap_1(sK2,X0_53,X0_54,X1_53),X1_54) = iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X1_53),u1_struct_0(X0_53)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
    | m1_pre_topc(X1_53,sK2) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X0_53)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_4728])).

cnf(c_4902,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4887,c_4729])).

cnf(c_5321,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4902,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_2800,c_3245])).

cnf(c_5322,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_5321])).

cnf(c_5326,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2624,c_5322])).

cnf(c_5398,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5326,c_36,c_37,c_38,c_40,c_30,c_29,c_28,c_26,c_2054,c_3167,c_3204,c_3297,c_3306,c_3512,c_3711,c_4123])).

cnf(c_20,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK0(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK0(X1,X2,X0,X3,X4)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2009,plain,
    ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54)
    | ~ v1_funct_2(X1_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53))
    | ~ m1_pre_topc(X0_53,X2_53)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | v2_struct_0(X2_53)
    | ~ l1_pre_topc(X1_53)
    | ~ l1_pre_topc(X2_53)
    | ~ v2_pre_topc(X1_53)
    | ~ v2_pre_topc(X2_53)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | k3_funct_2(u1_struct_0(X2_53),u1_struct_0(X1_53),X0_54,sK0(X1_53,X2_53,X0_53,X0_54,X1_54)) != k1_funct_1(X1_54,sK0(X1_53,X2_53,X0_53,X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2629,plain,
    ( k3_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,sK0(X1_53,X0_53,X2_53,X0_54,X1_54)) != k1_funct_1(X1_54,sK0(X1_53,X0_53,X2_53,X0_54,X1_54))
    | r2_funct_2(u1_struct_0(X2_53),u1_struct_0(X1_53),k2_tmap_1(X0_53,X1_53,X0_54,X2_53),X1_54) = iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_pre_topc(X2_53,X0_53) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | v2_struct_0(X2_53) = iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X1_53) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X1_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2009])).

cnf(c_5400,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5398,c_2629])).

cnf(c_5401,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5400,c_4887])).

cnf(c_4129,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2014])).

cnf(c_4130,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4129])).

cnf(c_6460,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5401,c_36,c_37,c_38,c_39,c_40,c_30,c_41,c_29,c_42,c_28,c_43,c_26,c_2054,c_2800,c_2987,c_3167,c_3204,c_3245,c_3297,c_3306,c_3512,c_3711,c_4123,c_4130])).

cnf(c_7100,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_7098,c_6460])).

cnf(c_25,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2004,plain,
    ( ~ m1_pre_topc(X0_53,X1_53)
    | ~ r2_hidden(X0_54,u1_struct_0(X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(X1_53))
    | v2_struct_0(X1_53)
    | v2_struct_0(X0_53)
    | ~ l1_pre_topc(X1_53)
    | ~ v2_pre_topc(X1_53)
    | k1_funct_1(k4_tmap_1(X1_53,X0_53),X0_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2634,plain,
    ( k1_funct_1(k4_tmap_1(X0_53,X1_53),X0_54) = X0_54
    | m1_pre_topc(X1_53,X0_53) != iProver_top
    | r2_hidden(X0_54,u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
    | v2_struct_0(X1_53) = iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2004])).

cnf(c_6266,plain,
    ( k1_funct_1(k4_tmap_1(X0_53,sK2),sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(X0_53)) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_6261,c_2634])).

cnf(c_6783,plain,
    ( v2_struct_0(X0_53) = iProver_top
    | k1_funct_1(k4_tmap_1(X0_53,sK2),sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6266,c_39,c_6265])).

cnf(c_6784,plain,
    ( k1_funct_1(k4_tmap_1(X0_53,sK2),sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_53) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_6783])).

cnf(c_6788,plain,
    ( k1_funct_1(k4_tmap_1(X0_53,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_53) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(X0_53) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_53) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_53) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2624,c_6784])).

cnf(c_6791,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6788])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7100,c_6791,c_4123,c_3711,c_3512,c_3306,c_3297,c_3204,c_3167,c_2054,c_26,c_28,c_29,c_30,c_40,c_38,c_37,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.73/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.02  
% 3.73/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/1.02  
% 3.73/1.02  ------  iProver source info
% 3.73/1.02  
% 3.73/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.73/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/1.02  git: non_committed_changes: false
% 3.73/1.02  git: last_make_outside_of_git: false
% 3.73/1.02  
% 3.73/1.02  ------ 
% 3.73/1.02  
% 3.73/1.02  ------ Input Options
% 3.73/1.02  
% 3.73/1.02  --out_options                           all
% 3.73/1.02  --tptp_safe_out                         true
% 3.73/1.02  --problem_path                          ""
% 3.73/1.02  --include_path                          ""
% 3.73/1.02  --clausifier                            res/vclausify_rel
% 3.73/1.02  --clausifier_options                    ""
% 3.73/1.02  --stdin                                 false
% 3.73/1.02  --stats_out                             all
% 3.73/1.02  
% 3.73/1.02  ------ General Options
% 3.73/1.02  
% 3.73/1.02  --fof                                   false
% 3.73/1.02  --time_out_real                         305.
% 3.73/1.02  --time_out_virtual                      -1.
% 3.73/1.02  --symbol_type_check                     false
% 3.73/1.02  --clausify_out                          false
% 3.73/1.02  --sig_cnt_out                           false
% 3.73/1.03  --trig_cnt_out                          false
% 3.73/1.03  --trig_cnt_out_tolerance                1.
% 3.73/1.03  --trig_cnt_out_sk_spl                   false
% 3.73/1.03  --abstr_cl_out                          false
% 3.73/1.03  
% 3.73/1.03  ------ Global Options
% 3.73/1.03  
% 3.73/1.03  --schedule                              default
% 3.73/1.03  --add_important_lit                     false
% 3.73/1.03  --prop_solver_per_cl                    1000
% 3.73/1.03  --min_unsat_core                        false
% 3.73/1.03  --soft_assumptions                      false
% 3.73/1.03  --soft_lemma_size                       3
% 3.73/1.03  --prop_impl_unit_size                   0
% 3.73/1.03  --prop_impl_unit                        []
% 3.73/1.03  --share_sel_clauses                     true
% 3.73/1.03  --reset_solvers                         false
% 3.73/1.03  --bc_imp_inh                            [conj_cone]
% 3.73/1.03  --conj_cone_tolerance                   3.
% 3.73/1.03  --extra_neg_conj                        none
% 3.73/1.03  --large_theory_mode                     true
% 3.73/1.03  --prolific_symb_bound                   200
% 3.73/1.03  --lt_threshold                          2000
% 3.73/1.03  --clause_weak_htbl                      true
% 3.73/1.03  --gc_record_bc_elim                     false
% 3.73/1.03  
% 3.73/1.03  ------ Preprocessing Options
% 3.73/1.03  
% 3.73/1.03  --preprocessing_flag                    true
% 3.73/1.03  --time_out_prep_mult                    0.1
% 3.73/1.03  --splitting_mode                        input
% 3.73/1.03  --splitting_grd                         true
% 3.73/1.03  --splitting_cvd                         false
% 3.73/1.03  --splitting_cvd_svl                     false
% 3.73/1.03  --splitting_nvd                         32
% 3.73/1.03  --sub_typing                            true
% 3.73/1.03  --prep_gs_sim                           true
% 3.73/1.03  --prep_unflatten                        true
% 3.73/1.03  --prep_res_sim                          true
% 3.73/1.03  --prep_upred                            true
% 3.73/1.03  --prep_sem_filter                       exhaustive
% 3.73/1.03  --prep_sem_filter_out                   false
% 3.73/1.03  --pred_elim                             true
% 3.73/1.03  --res_sim_input                         true
% 3.73/1.03  --eq_ax_congr_red                       true
% 3.73/1.03  --pure_diseq_elim                       true
% 3.73/1.03  --brand_transform                       false
% 3.73/1.03  --non_eq_to_eq                          false
% 3.73/1.03  --prep_def_merge                        true
% 3.73/1.03  --prep_def_merge_prop_impl              false
% 3.73/1.03  --prep_def_merge_mbd                    true
% 3.73/1.03  --prep_def_merge_tr_red                 false
% 3.73/1.03  --prep_def_merge_tr_cl                  false
% 3.73/1.03  --smt_preprocessing                     true
% 3.73/1.03  --smt_ac_axioms                         fast
% 3.73/1.03  --preprocessed_out                      false
% 3.73/1.03  --preprocessed_stats                    false
% 3.73/1.03  
% 3.73/1.03  ------ Abstraction refinement Options
% 3.73/1.03  
% 3.73/1.03  --abstr_ref                             []
% 3.73/1.03  --abstr_ref_prep                        false
% 3.73/1.03  --abstr_ref_until_sat                   false
% 3.73/1.03  --abstr_ref_sig_restrict                funpre
% 3.73/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/1.03  --abstr_ref_under                       []
% 3.73/1.03  
% 3.73/1.03  ------ SAT Options
% 3.73/1.03  
% 3.73/1.03  --sat_mode                              false
% 3.73/1.03  --sat_fm_restart_options                ""
% 3.73/1.03  --sat_gr_def                            false
% 3.73/1.03  --sat_epr_types                         true
% 3.73/1.03  --sat_non_cyclic_types                  false
% 3.73/1.03  --sat_finite_models                     false
% 3.73/1.03  --sat_fm_lemmas                         false
% 3.73/1.03  --sat_fm_prep                           false
% 3.73/1.03  --sat_fm_uc_incr                        true
% 3.73/1.03  --sat_out_model                         small
% 3.73/1.03  --sat_out_clauses                       false
% 3.73/1.03  
% 3.73/1.03  ------ QBF Options
% 3.73/1.03  
% 3.73/1.03  --qbf_mode                              false
% 3.73/1.03  --qbf_elim_univ                         false
% 3.73/1.03  --qbf_dom_inst                          none
% 3.73/1.03  --qbf_dom_pre_inst                      false
% 3.73/1.03  --qbf_sk_in                             false
% 3.73/1.03  --qbf_pred_elim                         true
% 3.73/1.03  --qbf_split                             512
% 3.73/1.03  
% 3.73/1.03  ------ BMC1 Options
% 3.73/1.03  
% 3.73/1.03  --bmc1_incremental                      false
% 3.73/1.03  --bmc1_axioms                           reachable_all
% 3.73/1.03  --bmc1_min_bound                        0
% 3.73/1.03  --bmc1_max_bound                        -1
% 3.73/1.03  --bmc1_max_bound_default                -1
% 3.73/1.03  --bmc1_symbol_reachability              true
% 3.73/1.03  --bmc1_property_lemmas                  false
% 3.73/1.03  --bmc1_k_induction                      false
% 3.73/1.03  --bmc1_non_equiv_states                 false
% 3.73/1.03  --bmc1_deadlock                         false
% 3.73/1.03  --bmc1_ucm                              false
% 3.73/1.03  --bmc1_add_unsat_core                   none
% 3.73/1.03  --bmc1_unsat_core_children              false
% 3.73/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/1.03  --bmc1_out_stat                         full
% 3.73/1.03  --bmc1_ground_init                      false
% 3.73/1.03  --bmc1_pre_inst_next_state              false
% 3.73/1.03  --bmc1_pre_inst_state                   false
% 3.73/1.03  --bmc1_pre_inst_reach_state             false
% 3.73/1.03  --bmc1_out_unsat_core                   false
% 3.73/1.03  --bmc1_aig_witness_out                  false
% 3.73/1.03  --bmc1_verbose                          false
% 3.73/1.03  --bmc1_dump_clauses_tptp                false
% 3.73/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.73/1.03  --bmc1_dump_file                        -
% 3.73/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.73/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.73/1.03  --bmc1_ucm_extend_mode                  1
% 3.73/1.03  --bmc1_ucm_init_mode                    2
% 3.73/1.03  --bmc1_ucm_cone_mode                    none
% 3.73/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.73/1.03  --bmc1_ucm_relax_model                  4
% 3.73/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.73/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/1.03  --bmc1_ucm_layered_model                none
% 3.73/1.03  --bmc1_ucm_max_lemma_size               10
% 3.73/1.03  
% 3.73/1.03  ------ AIG Options
% 3.73/1.03  
% 3.73/1.03  --aig_mode                              false
% 3.73/1.03  
% 3.73/1.03  ------ Instantiation Options
% 3.73/1.03  
% 3.73/1.03  --instantiation_flag                    true
% 3.73/1.03  --inst_sos_flag                         true
% 3.73/1.03  --inst_sos_phase                        true
% 3.73/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/1.03  --inst_lit_sel_side                     num_symb
% 3.73/1.03  --inst_solver_per_active                1400
% 3.73/1.03  --inst_solver_calls_frac                1.
% 3.73/1.03  --inst_passive_queue_type               priority_queues
% 3.73/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/1.03  --inst_passive_queues_freq              [25;2]
% 3.73/1.03  --inst_dismatching                      true
% 3.73/1.03  --inst_eager_unprocessed_to_passive     true
% 3.73/1.03  --inst_prop_sim_given                   true
% 3.73/1.03  --inst_prop_sim_new                     false
% 3.73/1.03  --inst_subs_new                         false
% 3.73/1.03  --inst_eq_res_simp                      false
% 3.73/1.03  --inst_subs_given                       false
% 3.73/1.03  --inst_orphan_elimination               true
% 3.73/1.03  --inst_learning_loop_flag               true
% 3.73/1.03  --inst_learning_start                   3000
% 3.73/1.03  --inst_learning_factor                  2
% 3.73/1.03  --inst_start_prop_sim_after_learn       3
% 3.73/1.03  --inst_sel_renew                        solver
% 3.73/1.03  --inst_lit_activity_flag                true
% 3.73/1.03  --inst_restr_to_given                   false
% 3.73/1.03  --inst_activity_threshold               500
% 3.73/1.03  --inst_out_proof                        true
% 3.73/1.03  
% 3.73/1.03  ------ Resolution Options
% 3.73/1.03  
% 3.73/1.03  --resolution_flag                       true
% 3.73/1.03  --res_lit_sel                           adaptive
% 3.73/1.03  --res_lit_sel_side                      none
% 3.73/1.03  --res_ordering                          kbo
% 3.73/1.03  --res_to_prop_solver                    active
% 3.73/1.03  --res_prop_simpl_new                    false
% 3.73/1.03  --res_prop_simpl_given                  true
% 3.73/1.03  --res_passive_queue_type                priority_queues
% 3.73/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/1.03  --res_passive_queues_freq               [15;5]
% 3.73/1.03  --res_forward_subs                      full
% 3.73/1.03  --res_backward_subs                     full
% 3.73/1.03  --res_forward_subs_resolution           true
% 3.73/1.03  --res_backward_subs_resolution          true
% 3.73/1.03  --res_orphan_elimination                true
% 3.73/1.03  --res_time_limit                        2.
% 3.73/1.03  --res_out_proof                         true
% 3.73/1.03  
% 3.73/1.03  ------ Superposition Options
% 3.73/1.03  
% 3.73/1.03  --superposition_flag                    true
% 3.73/1.03  --sup_passive_queue_type                priority_queues
% 3.73/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.73/1.03  --demod_completeness_check              fast
% 3.73/1.03  --demod_use_ground                      true
% 3.73/1.03  --sup_to_prop_solver                    passive
% 3.73/1.03  --sup_prop_simpl_new                    true
% 3.73/1.03  --sup_prop_simpl_given                  true
% 3.73/1.03  --sup_fun_splitting                     true
% 3.73/1.03  --sup_smt_interval                      50000
% 3.73/1.03  
% 3.73/1.03  ------ Superposition Simplification Setup
% 3.73/1.03  
% 3.73/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.73/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.73/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.73/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.73/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.73/1.03  --sup_immed_triv                        [TrivRules]
% 3.73/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.03  --sup_immed_bw_main                     []
% 3.73/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.73/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.03  --sup_input_bw                          []
% 3.73/1.03  
% 3.73/1.03  ------ Combination Options
% 3.73/1.03  
% 3.73/1.03  --comb_res_mult                         3
% 3.73/1.03  --comb_sup_mult                         2
% 3.73/1.03  --comb_inst_mult                        10
% 3.73/1.03  
% 3.73/1.03  ------ Debug Options
% 3.73/1.03  
% 3.73/1.03  --dbg_backtrace                         false
% 3.73/1.03  --dbg_dump_prop_clauses                 false
% 3.73/1.03  --dbg_dump_prop_clauses_file            -
% 3.73/1.03  --dbg_out_stat                          false
% 3.73/1.03  ------ Parsing...
% 3.73/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/1.03  
% 3.73/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.73/1.03  
% 3.73/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/1.03  
% 3.73/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.03  ------ Proving...
% 3.73/1.03  ------ Problem Properties 
% 3.73/1.03  
% 3.73/1.03  
% 3.73/1.03  clauses                                 34
% 3.73/1.03  conjectures                             10
% 3.73/1.03  EPR                                     11
% 3.73/1.03  Horn                                    23
% 3.73/1.03  unary                                   9
% 3.73/1.03  binary                                  2
% 3.73/1.03  lits                                    183
% 3.73/1.03  lits eq                                 7
% 3.73/1.03  fd_pure                                 0
% 3.73/1.03  fd_pseudo                               0
% 3.73/1.03  fd_cond                                 0
% 3.73/1.03  fd_pseudo_cond                          1
% 3.73/1.03  AC symbols                              0
% 3.73/1.03  
% 3.73/1.03  ------ Schedule dynamic 5 is on 
% 3.73/1.03  
% 3.73/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.73/1.03  
% 3.73/1.03  
% 3.73/1.03  ------ 
% 3.73/1.03  Current options:
% 3.73/1.03  ------ 
% 3.73/1.03  
% 3.73/1.03  ------ Input Options
% 3.73/1.03  
% 3.73/1.03  --out_options                           all
% 3.73/1.03  --tptp_safe_out                         true
% 3.73/1.03  --problem_path                          ""
% 3.73/1.03  --include_path                          ""
% 3.73/1.03  --clausifier                            res/vclausify_rel
% 3.73/1.03  --clausifier_options                    ""
% 3.73/1.03  --stdin                                 false
% 3.73/1.03  --stats_out                             all
% 3.73/1.03  
% 3.73/1.03  ------ General Options
% 3.73/1.03  
% 3.73/1.03  --fof                                   false
% 3.73/1.03  --time_out_real                         305.
% 3.73/1.03  --time_out_virtual                      -1.
% 3.73/1.03  --symbol_type_check                     false
% 3.73/1.03  --clausify_out                          false
% 3.73/1.03  --sig_cnt_out                           false
% 3.73/1.03  --trig_cnt_out                          false
% 3.73/1.03  --trig_cnt_out_tolerance                1.
% 3.73/1.03  --trig_cnt_out_sk_spl                   false
% 3.73/1.03  --abstr_cl_out                          false
% 3.73/1.03  
% 3.73/1.03  ------ Global Options
% 3.73/1.03  
% 3.73/1.03  --schedule                              default
% 3.73/1.03  --add_important_lit                     false
% 3.73/1.03  --prop_solver_per_cl                    1000
% 3.73/1.03  --min_unsat_core                        false
% 3.73/1.03  --soft_assumptions                      false
% 3.73/1.03  --soft_lemma_size                       3
% 3.73/1.03  --prop_impl_unit_size                   0
% 3.73/1.03  --prop_impl_unit                        []
% 3.73/1.03  --share_sel_clauses                     true
% 3.73/1.03  --reset_solvers                         false
% 3.73/1.03  --bc_imp_inh                            [conj_cone]
% 3.73/1.03  --conj_cone_tolerance                   3.
% 3.73/1.03  --extra_neg_conj                        none
% 3.73/1.03  --large_theory_mode                     true
% 3.73/1.03  --prolific_symb_bound                   200
% 3.73/1.03  --lt_threshold                          2000
% 3.73/1.03  --clause_weak_htbl                      true
% 3.73/1.03  --gc_record_bc_elim                     false
% 3.73/1.03  
% 3.73/1.03  ------ Preprocessing Options
% 3.73/1.03  
% 3.73/1.03  --preprocessing_flag                    true
% 3.73/1.03  --time_out_prep_mult                    0.1
% 3.73/1.03  --splitting_mode                        input
% 3.73/1.03  --splitting_grd                         true
% 3.73/1.03  --splitting_cvd                         false
% 3.73/1.03  --splitting_cvd_svl                     false
% 3.73/1.03  --splitting_nvd                         32
% 3.73/1.03  --sub_typing                            true
% 3.73/1.03  --prep_gs_sim                           true
% 3.73/1.03  --prep_unflatten                        true
% 3.73/1.03  --prep_res_sim                          true
% 3.73/1.03  --prep_upred                            true
% 3.73/1.03  --prep_sem_filter                       exhaustive
% 3.73/1.03  --prep_sem_filter_out                   false
% 3.73/1.03  --pred_elim                             true
% 3.73/1.03  --res_sim_input                         true
% 3.73/1.03  --eq_ax_congr_red                       true
% 3.73/1.03  --pure_diseq_elim                       true
% 3.73/1.03  --brand_transform                       false
% 3.73/1.03  --non_eq_to_eq                          false
% 3.73/1.03  --prep_def_merge                        true
% 3.73/1.03  --prep_def_merge_prop_impl              false
% 3.73/1.03  --prep_def_merge_mbd                    true
% 3.73/1.03  --prep_def_merge_tr_red                 false
% 3.73/1.03  --prep_def_merge_tr_cl                  false
% 3.73/1.03  --smt_preprocessing                     true
% 3.73/1.03  --smt_ac_axioms                         fast
% 3.73/1.03  --preprocessed_out                      false
% 3.73/1.03  --preprocessed_stats                    false
% 3.73/1.03  
% 3.73/1.03  ------ Abstraction refinement Options
% 3.73/1.03  
% 3.73/1.03  --abstr_ref                             []
% 3.73/1.03  --abstr_ref_prep                        false
% 3.73/1.03  --abstr_ref_until_sat                   false
% 3.73/1.03  --abstr_ref_sig_restrict                funpre
% 3.73/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/1.03  --abstr_ref_under                       []
% 3.73/1.03  
% 3.73/1.03  ------ SAT Options
% 3.73/1.03  
% 3.73/1.03  --sat_mode                              false
% 3.73/1.03  --sat_fm_restart_options                ""
% 3.73/1.03  --sat_gr_def                            false
% 3.73/1.03  --sat_epr_types                         true
% 3.73/1.03  --sat_non_cyclic_types                  false
% 3.73/1.03  --sat_finite_models                     false
% 3.73/1.03  --sat_fm_lemmas                         false
% 3.73/1.03  --sat_fm_prep                           false
% 3.73/1.03  --sat_fm_uc_incr                        true
% 3.73/1.03  --sat_out_model                         small
% 3.73/1.03  --sat_out_clauses                       false
% 3.73/1.03  
% 3.73/1.03  ------ QBF Options
% 3.73/1.03  
% 3.73/1.03  --qbf_mode                              false
% 3.73/1.03  --qbf_elim_univ                         false
% 3.73/1.03  --qbf_dom_inst                          none
% 3.73/1.03  --qbf_dom_pre_inst                      false
% 3.73/1.03  --qbf_sk_in                             false
% 3.73/1.03  --qbf_pred_elim                         true
% 3.73/1.03  --qbf_split                             512
% 3.73/1.03  
% 3.73/1.03  ------ BMC1 Options
% 3.73/1.03  
% 3.73/1.03  --bmc1_incremental                      false
% 3.73/1.03  --bmc1_axioms                           reachable_all
% 3.73/1.03  --bmc1_min_bound                        0
% 3.73/1.03  --bmc1_max_bound                        -1
% 3.73/1.03  --bmc1_max_bound_default                -1
% 3.73/1.03  --bmc1_symbol_reachability              true
% 3.73/1.03  --bmc1_property_lemmas                  false
% 3.73/1.03  --bmc1_k_induction                      false
% 3.73/1.03  --bmc1_non_equiv_states                 false
% 3.73/1.03  --bmc1_deadlock                         false
% 3.73/1.03  --bmc1_ucm                              false
% 3.73/1.03  --bmc1_add_unsat_core                   none
% 3.73/1.03  --bmc1_unsat_core_children              false
% 3.73/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/1.03  --bmc1_out_stat                         full
% 3.73/1.03  --bmc1_ground_init                      false
% 3.73/1.03  --bmc1_pre_inst_next_state              false
% 3.73/1.03  --bmc1_pre_inst_state                   false
% 3.73/1.03  --bmc1_pre_inst_reach_state             false
% 3.73/1.03  --bmc1_out_unsat_core                   false
% 3.73/1.03  --bmc1_aig_witness_out                  false
% 3.73/1.03  --bmc1_verbose                          false
% 3.73/1.03  --bmc1_dump_clauses_tptp                false
% 3.73/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.73/1.03  --bmc1_dump_file                        -
% 3.73/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.73/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.73/1.03  --bmc1_ucm_extend_mode                  1
% 3.73/1.03  --bmc1_ucm_init_mode                    2
% 3.73/1.03  --bmc1_ucm_cone_mode                    none
% 3.73/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.73/1.03  --bmc1_ucm_relax_model                  4
% 3.73/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.73/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/1.03  --bmc1_ucm_layered_model                none
% 3.73/1.03  --bmc1_ucm_max_lemma_size               10
% 3.73/1.03  
% 3.73/1.03  ------ AIG Options
% 3.73/1.03  
% 3.73/1.03  --aig_mode                              false
% 3.73/1.03  
% 3.73/1.03  ------ Instantiation Options
% 3.73/1.03  
% 3.73/1.03  --instantiation_flag                    true
% 3.73/1.03  --inst_sos_flag                         true
% 3.73/1.03  --inst_sos_phase                        true
% 3.73/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/1.03  --inst_lit_sel_side                     none
% 3.73/1.03  --inst_solver_per_active                1400
% 3.73/1.03  --inst_solver_calls_frac                1.
% 3.73/1.03  --inst_passive_queue_type               priority_queues
% 3.73/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/1.03  --inst_passive_queues_freq              [25;2]
% 3.73/1.03  --inst_dismatching                      true
% 3.73/1.03  --inst_eager_unprocessed_to_passive     true
% 3.73/1.03  --inst_prop_sim_given                   true
% 3.73/1.03  --inst_prop_sim_new                     false
% 3.73/1.03  --inst_subs_new                         false
% 3.73/1.03  --inst_eq_res_simp                      false
% 3.73/1.03  --inst_subs_given                       false
% 3.73/1.03  --inst_orphan_elimination               true
% 3.73/1.03  --inst_learning_loop_flag               true
% 3.73/1.03  --inst_learning_start                   3000
% 3.73/1.03  --inst_learning_factor                  2
% 3.73/1.03  --inst_start_prop_sim_after_learn       3
% 3.73/1.03  --inst_sel_renew                        solver
% 3.73/1.03  --inst_lit_activity_flag                true
% 3.73/1.03  --inst_restr_to_given                   false
% 3.73/1.03  --inst_activity_threshold               500
% 3.73/1.03  --inst_out_proof                        true
% 3.73/1.03  
% 3.73/1.03  ------ Resolution Options
% 3.73/1.03  
% 3.73/1.03  --resolution_flag                       false
% 3.73/1.03  --res_lit_sel                           adaptive
% 3.73/1.03  --res_lit_sel_side                      none
% 3.73/1.03  --res_ordering                          kbo
% 3.73/1.03  --res_to_prop_solver                    active
% 3.73/1.03  --res_prop_simpl_new                    false
% 3.73/1.03  --res_prop_simpl_given                  true
% 3.73/1.03  --res_passive_queue_type                priority_queues
% 3.73/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/1.03  --res_passive_queues_freq               [15;5]
% 3.73/1.03  --res_forward_subs                      full
% 3.73/1.03  --res_backward_subs                     full
% 3.73/1.03  --res_forward_subs_resolution           true
% 3.73/1.03  --res_backward_subs_resolution          true
% 3.73/1.03  --res_orphan_elimination                true
% 3.73/1.03  --res_time_limit                        2.
% 3.73/1.03  --res_out_proof                         true
% 3.73/1.03  
% 3.73/1.03  ------ Superposition Options
% 3.73/1.03  
% 3.73/1.03  --superposition_flag                    true
% 3.73/1.03  --sup_passive_queue_type                priority_queues
% 3.73/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.73/1.03  --demod_completeness_check              fast
% 3.73/1.03  --demod_use_ground                      true
% 3.73/1.03  --sup_to_prop_solver                    passive
% 3.73/1.03  --sup_prop_simpl_new                    true
% 3.73/1.03  --sup_prop_simpl_given                  true
% 3.73/1.03  --sup_fun_splitting                     true
% 3.73/1.03  --sup_smt_interval                      50000
% 3.73/1.03  
% 3.73/1.03  ------ Superposition Simplification Setup
% 3.73/1.03  
% 3.73/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.73/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.73/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.73/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.73/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.73/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.73/1.03  --sup_immed_triv                        [TrivRules]
% 3.73/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.03  --sup_immed_bw_main                     []
% 3.73/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.73/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/1.03  --sup_input_bw                          []
% 3.73/1.03  
% 3.73/1.03  ------ Combination Options
% 3.73/1.03  
% 3.73/1.03  --comb_res_mult                         3
% 3.73/1.03  --comb_sup_mult                         2
% 3.73/1.03  --comb_inst_mult                        10
% 3.73/1.03  
% 3.73/1.03  ------ Debug Options
% 3.73/1.03  
% 3.73/1.03  --dbg_backtrace                         false
% 3.73/1.03  --dbg_dump_prop_clauses                 false
% 3.73/1.03  --dbg_dump_prop_clauses_file            -
% 3.73/1.03  --dbg_out_stat                          false
% 3.73/1.03  
% 3.73/1.03  
% 3.73/1.03  
% 3.73/1.03  
% 3.73/1.03  ------ Proving...
% 3.73/1.03  
% 3.73/1.03  
% 3.73/1.03  % SZS status Theorem for theBenchmark.p
% 3.73/1.03  
% 3.73/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/1.03  
% 3.73/1.03  fof(f11,axiom,(
% 3.73/1.03    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f39,plain,(
% 3.73/1.03    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.73/1.03    inference(ennf_transformation,[],[f11])).
% 3.73/1.03  
% 3.73/1.03  fof(f40,plain,(
% 3.73/1.03    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.73/1.03    inference(flattening,[],[f39])).
% 3.73/1.03  
% 3.73/1.03  fof(f78,plain,(
% 3.73/1.03    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f40])).
% 3.73/1.03  
% 3.73/1.03  fof(f19,conjecture,(
% 3.73/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f20,negated_conjecture,(
% 3.73/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 3.73/1.03    inference(negated_conjecture,[],[f19])).
% 3.73/1.03  
% 3.73/1.03  fof(f53,plain,(
% 3.73/1.03    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.73/1.03    inference(ennf_transformation,[],[f20])).
% 3.73/1.03  
% 3.73/1.03  fof(f54,plain,(
% 3.73/1.03    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.73/1.03    inference(flattening,[],[f53])).
% 3.73/1.03  
% 3.73/1.03  fof(f61,plain,(
% 3.73/1.03    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 3.73/1.03    introduced(choice_axiom,[])).
% 3.73/1.03  
% 3.73/1.03  fof(f60,plain,(
% 3.73/1.03    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.73/1.03    introduced(choice_axiom,[])).
% 3.73/1.03  
% 3.73/1.03  fof(f59,plain,(
% 3.73/1.03    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.73/1.03    introduced(choice_axiom,[])).
% 3.73/1.03  
% 3.73/1.03  fof(f62,plain,(
% 3.73/1.03    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.73/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f54,f61,f60,f59])).
% 3.73/1.03  
% 3.73/1.03  fof(f93,plain,(
% 3.73/1.03    m1_pre_topc(sK2,sK1)),
% 3.73/1.03    inference(cnf_transformation,[],[f62])).
% 3.73/1.03  
% 3.73/1.03  fof(f96,plain,(
% 3.73/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 3.73/1.03    inference(cnf_transformation,[],[f62])).
% 3.73/1.03  
% 3.73/1.03  fof(f9,axiom,(
% 3.73/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f35,plain,(
% 3.73/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.73/1.03    inference(ennf_transformation,[],[f9])).
% 3.73/1.03  
% 3.73/1.03  fof(f36,plain,(
% 3.73/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.73/1.03    inference(flattening,[],[f35])).
% 3.73/1.03  
% 3.73/1.03  fof(f72,plain,(
% 3.73/1.03    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f36])).
% 3.73/1.03  
% 3.73/1.03  fof(f89,plain,(
% 3.73/1.03    ~v2_struct_0(sK1)),
% 3.73/1.03    inference(cnf_transformation,[],[f62])).
% 3.73/1.03  
% 3.73/1.03  fof(f90,plain,(
% 3.73/1.03    v2_pre_topc(sK1)),
% 3.73/1.03    inference(cnf_transformation,[],[f62])).
% 3.73/1.03  
% 3.73/1.03  fof(f91,plain,(
% 3.73/1.03    l1_pre_topc(sK1)),
% 3.73/1.03    inference(cnf_transformation,[],[f62])).
% 3.73/1.03  
% 3.73/1.03  fof(f94,plain,(
% 3.73/1.03    v1_funct_1(sK3)),
% 3.73/1.03    inference(cnf_transformation,[],[f62])).
% 3.73/1.03  
% 3.73/1.03  fof(f95,plain,(
% 3.73/1.03    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 3.73/1.03    inference(cnf_transformation,[],[f62])).
% 3.73/1.03  
% 3.73/1.03  fof(f13,axiom,(
% 3.73/1.03    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f42,plain,(
% 3.73/1.03    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.73/1.03    inference(ennf_transformation,[],[f13])).
% 3.73/1.03  
% 3.73/1.03  fof(f80,plain,(
% 3.73/1.03    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f42])).
% 3.73/1.03  
% 3.73/1.03  fof(f8,axiom,(
% 3.73/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f33,plain,(
% 3.73/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.73/1.03    inference(ennf_transformation,[],[f8])).
% 3.73/1.03  
% 3.73/1.03  fof(f34,plain,(
% 3.73/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.73/1.03    inference(flattening,[],[f33])).
% 3.73/1.03  
% 3.73/1.03  fof(f71,plain,(
% 3.73/1.03    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f34])).
% 3.73/1.03  
% 3.73/1.03  fof(f92,plain,(
% 3.73/1.03    ~v2_struct_0(sK2)),
% 3.73/1.03    inference(cnf_transformation,[],[f62])).
% 3.73/1.03  
% 3.73/1.03  fof(f6,axiom,(
% 3.73/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f30,plain,(
% 3.73/1.03    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.73/1.03    inference(ennf_transformation,[],[f6])).
% 3.73/1.03  
% 3.73/1.03  fof(f69,plain,(
% 3.73/1.03    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f30])).
% 3.73/1.03  
% 3.73/1.03  fof(f4,axiom,(
% 3.73/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f27,plain,(
% 3.73/1.03    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.73/1.03    inference(ennf_transformation,[],[f4])).
% 3.73/1.03  
% 3.73/1.03  fof(f28,plain,(
% 3.73/1.03    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.73/1.03    inference(flattening,[],[f27])).
% 3.73/1.03  
% 3.73/1.03  fof(f67,plain,(
% 3.73/1.03    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f28])).
% 3.73/1.03  
% 3.73/1.03  fof(f16,axiom,(
% 3.73/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f47,plain,(
% 3.73/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.73/1.03    inference(ennf_transformation,[],[f16])).
% 3.73/1.03  
% 3.73/1.03  fof(f48,plain,(
% 3.73/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.73/1.03    inference(flattening,[],[f47])).
% 3.73/1.03  
% 3.73/1.03  fof(f86,plain,(
% 3.73/1.03    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f48])).
% 3.73/1.03  
% 3.73/1.03  fof(f10,axiom,(
% 3.73/1.03    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f37,plain,(
% 3.73/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.73/1.03    inference(ennf_transformation,[],[f10])).
% 3.73/1.03  
% 3.73/1.03  fof(f38,plain,(
% 3.73/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.73/1.03    inference(flattening,[],[f37])).
% 3.73/1.03  
% 3.73/1.03  fof(f75,plain,(
% 3.73/1.03    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f38])).
% 3.73/1.03  
% 3.73/1.03  fof(f3,axiom,(
% 3.73/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f25,plain,(
% 3.73/1.03    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.73/1.03    inference(ennf_transformation,[],[f3])).
% 3.73/1.03  
% 3.73/1.03  fof(f26,plain,(
% 3.73/1.03    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.73/1.03    inference(flattening,[],[f25])).
% 3.73/1.03  
% 3.73/1.03  fof(f55,plain,(
% 3.73/1.03    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.73/1.03    inference(nnf_transformation,[],[f26])).
% 3.73/1.03  
% 3.73/1.03  fof(f65,plain,(
% 3.73/1.03    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f55])).
% 3.73/1.03  
% 3.73/1.03  fof(f5,axiom,(
% 3.73/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f29,plain,(
% 3.73/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.73/1.03    inference(ennf_transformation,[],[f5])).
% 3.73/1.03  
% 3.73/1.03  fof(f68,plain,(
% 3.73/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f29])).
% 3.73/1.03  
% 3.73/1.03  fof(f73,plain,(
% 3.73/1.03    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f38])).
% 3.73/1.03  
% 3.73/1.03  fof(f74,plain,(
% 3.73/1.03    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f38])).
% 3.73/1.03  
% 3.73/1.03  fof(f15,axiom,(
% 3.73/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f45,plain,(
% 3.73/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.73/1.03    inference(ennf_transformation,[],[f15])).
% 3.73/1.03  
% 3.73/1.03  fof(f46,plain,(
% 3.73/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.73/1.03    inference(flattening,[],[f45])).
% 3.73/1.03  
% 3.73/1.03  fof(f57,plain,(
% 3.73/1.03    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) => (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))))),
% 3.73/1.03    introduced(choice_axiom,[])).
% 3.73/1.03  
% 3.73/1.03  fof(f58,plain,(
% 3.73/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.73/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f57])).
% 3.73/1.03  
% 3.73/1.03  fof(f84,plain,(
% 3.73/1.03    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f58])).
% 3.73/1.03  
% 3.73/1.03  fof(f12,axiom,(
% 3.73/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f41,plain,(
% 3.73/1.03    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.73/1.03    inference(ennf_transformation,[],[f12])).
% 3.73/1.03  
% 3.73/1.03  fof(f79,plain,(
% 3.73/1.03    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f41])).
% 3.73/1.03  
% 3.73/1.03  fof(f1,axiom,(
% 3.73/1.03    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f21,plain,(
% 3.73/1.03    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.73/1.03    inference(ennf_transformation,[],[f1])).
% 3.73/1.03  
% 3.73/1.03  fof(f22,plain,(
% 3.73/1.03    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.73/1.03    inference(flattening,[],[f21])).
% 3.73/1.03  
% 3.73/1.03  fof(f63,plain,(
% 3.73/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f22])).
% 3.73/1.03  
% 3.73/1.03  fof(f97,plain,(
% 3.73/1.03    ( ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) )),
% 3.73/1.03    inference(cnf_transformation,[],[f62])).
% 3.73/1.03  
% 3.73/1.03  fof(f98,plain,(
% 3.73/1.03    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)),
% 3.73/1.03    inference(cnf_transformation,[],[f62])).
% 3.73/1.03  
% 3.73/1.03  fof(f66,plain,(
% 3.73/1.03    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f55])).
% 3.73/1.03  
% 3.73/1.03  fof(f99,plain,(
% 3.73/1.03    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.73/1.03    inference(equality_resolution,[],[f66])).
% 3.73/1.03  
% 3.73/1.03  fof(f76,plain,(
% 3.73/1.03    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f40])).
% 3.73/1.03  
% 3.73/1.03  fof(f77,plain,(
% 3.73/1.03    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f40])).
% 3.73/1.03  
% 3.73/1.03  fof(f83,plain,(
% 3.73/1.03    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f58])).
% 3.73/1.03  
% 3.73/1.03  fof(f2,axiom,(
% 3.73/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f23,plain,(
% 3.73/1.03    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.73/1.03    inference(ennf_transformation,[],[f2])).
% 3.73/1.03  
% 3.73/1.03  fof(f24,plain,(
% 3.73/1.03    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.73/1.03    inference(flattening,[],[f23])).
% 3.73/1.03  
% 3.73/1.03  fof(f64,plain,(
% 3.73/1.03    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f24])).
% 3.73/1.03  
% 3.73/1.03  fof(f7,axiom,(
% 3.73/1.03    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f31,plain,(
% 3.73/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.73/1.03    inference(ennf_transformation,[],[f7])).
% 3.73/1.03  
% 3.73/1.03  fof(f32,plain,(
% 3.73/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.73/1.03    inference(flattening,[],[f31])).
% 3.73/1.03  
% 3.73/1.03  fof(f70,plain,(
% 3.73/1.03    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f32])).
% 3.73/1.03  
% 3.73/1.03  fof(f85,plain,(
% 3.73/1.03    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f58])).
% 3.73/1.03  
% 3.73/1.03  fof(f18,axiom,(
% 3.73/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 3.73/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.03  
% 3.73/1.03  fof(f51,plain,(
% 3.73/1.03    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.73/1.03    inference(ennf_transformation,[],[f18])).
% 3.73/1.03  
% 3.73/1.03  fof(f52,plain,(
% 3.73/1.03    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.73/1.03    inference(flattening,[],[f51])).
% 3.73/1.03  
% 3.73/1.03  fof(f88,plain,(
% 3.73/1.03    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.73/1.03    inference(cnf_transformation,[],[f52])).
% 3.73/1.03  
% 3.73/1.03  cnf(c_13,plain,
% 3.73/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.73/1.03      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.73/1.03      | v2_struct_0(X1)
% 3.73/1.03      | ~ l1_pre_topc(X1)
% 3.73/1.03      | ~ v2_pre_topc(X1) ),
% 3.73/1.03      inference(cnf_transformation,[],[f78]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2014,plain,
% 3.73/1.03      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.73/1.03      | m1_subset_1(k4_tmap_1(X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.73/1.03      | v2_struct_0(X1_53)
% 3.73/1.03      | ~ l1_pre_topc(X1_53)
% 3.73/1.03      | ~ v2_pre_topc(X1_53) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_13]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2624,plain,
% 3.73/1.03      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 3.73/1.03      | m1_subset_1(k4_tmap_1(X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) = iProver_top
% 3.73/1.03      | v2_struct_0(X1_53) = iProver_top
% 3.73/1.03      | l1_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X1_53) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2014]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_31,negated_conjecture,
% 3.73/1.03      ( m1_pre_topc(sK2,sK1) ),
% 3.73/1.03      inference(cnf_transformation,[],[f93]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_1998,negated_conjecture,
% 3.73/1.03      ( m1_pre_topc(sK2,sK1) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_31]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2640,plain,
% 3.73/1.03      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_1998]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_28,negated_conjecture,
% 3.73/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 3.73/1.03      inference(cnf_transformation,[],[f96]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2001,negated_conjecture,
% 3.73/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_28]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2637,plain,
% 3.73/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2001]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_9,plain,
% 3.73/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.73/1.03      | ~ m1_pre_topc(X3,X4)
% 3.73/1.03      | ~ m1_pre_topc(X3,X1)
% 3.73/1.03      | ~ m1_pre_topc(X1,X4)
% 3.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.73/1.03      | v2_struct_0(X4)
% 3.73/1.03      | v2_struct_0(X2)
% 3.73/1.03      | ~ l1_pre_topc(X4)
% 3.73/1.03      | ~ l1_pre_topc(X2)
% 3.73/1.03      | ~ v2_pre_topc(X4)
% 3.73/1.03      | ~ v2_pre_topc(X2)
% 3.73/1.03      | ~ v1_funct_1(X0)
% 3.73/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.73/1.03      inference(cnf_transformation,[],[f72]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2018,plain,
% 3.73/1.03      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.73/1.03      | ~ m1_pre_topc(X2_53,X0_53)
% 3.73/1.03      | ~ m1_pre_topc(X0_53,X3_53)
% 3.73/1.03      | ~ m1_pre_topc(X2_53,X3_53)
% 3.73/1.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.73/1.03      | v2_struct_0(X1_53)
% 3.73/1.03      | v2_struct_0(X3_53)
% 3.73/1.03      | ~ l1_pre_topc(X1_53)
% 3.73/1.03      | ~ l1_pre_topc(X3_53)
% 3.73/1.03      | ~ v2_pre_topc(X1_53)
% 3.73/1.03      | ~ v2_pre_topc(X3_53)
% 3.73/1.03      | ~ v1_funct_1(X0_54)
% 3.73/1.03      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_54) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_9]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2620,plain,
% 3.73/1.03      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k3_tmap_1(X3_53,X1_53,X0_53,X2_53,X0_54)
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 3.73/1.03      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 3.73/1.03      | m1_pre_topc(X0_53,X3_53) != iProver_top
% 3.73/1.03      | m1_pre_topc(X2_53,X3_53) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 3.73/1.03      | v2_struct_0(X1_53) = iProver_top
% 3.73/1.03      | v2_struct_0(X3_53) = iProver_top
% 3.73/1.03      | l1_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | l1_pre_topc(X3_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X3_53) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2018]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4312,plain,
% 3.73/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK2,X0_53,sK3)
% 3.73/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 3.73/1.03      | m1_pre_topc(X0_53,sK2) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,X1_53) != iProver_top
% 3.73/1.03      | v2_struct_0(X1_53) = iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | l1_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_2637,c_2620]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_35,negated_conjecture,
% 3.73/1.03      ( ~ v2_struct_0(sK1) ),
% 3.73/1.03      inference(cnf_transformation,[],[f89]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_36,plain,
% 3.73/1.03      ( v2_struct_0(sK1) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_34,negated_conjecture,
% 3.73/1.03      ( v2_pre_topc(sK1) ),
% 3.73/1.03      inference(cnf_transformation,[],[f90]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_37,plain,
% 3.73/1.03      ( v2_pre_topc(sK1) = iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_33,negated_conjecture,
% 3.73/1.03      ( l1_pre_topc(sK1) ),
% 3.73/1.03      inference(cnf_transformation,[],[f91]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_38,plain,
% 3.73/1.03      ( l1_pre_topc(sK1) = iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_30,negated_conjecture,
% 3.73/1.03      ( v1_funct_1(sK3) ),
% 3.73/1.03      inference(cnf_transformation,[],[f94]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_41,plain,
% 3.73/1.03      ( v1_funct_1(sK3) = iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_29,negated_conjecture,
% 3.73/1.03      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 3.73/1.03      inference(cnf_transformation,[],[f95]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_42,plain,
% 3.73/1.03      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4637,plain,
% 3.73/1.03      ( l1_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK2,X0_53,sK3)
% 3.73/1.03      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 3.73/1.03      | m1_pre_topc(X0_53,sK2) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,X1_53) != iProver_top
% 3.73/1.03      | v2_struct_0(X1_53) = iProver_top
% 3.73/1.03      | v2_pre_topc(X1_53) != iProver_top ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_4312,c_36,c_37,c_38,c_41,c_42]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4638,plain,
% 3.73/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_53)) = k3_tmap_1(X1_53,sK1,sK2,X0_53,sK3)
% 3.73/1.03      | m1_pre_topc(X0_53,X1_53) != iProver_top
% 3.73/1.03      | m1_pre_topc(X0_53,sK2) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,X1_53) != iProver_top
% 3.73/1.03      | v2_struct_0(X1_53) = iProver_top
% 3.73/1.03      | l1_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X1_53) != iProver_top ),
% 3.73/1.03      inference(renaming,[status(thm)],[c_4637]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4643,plain,
% 3.73/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
% 3.73/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_2640,c_4638]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_17,plain,
% 3.73/1.03      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.73/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2010,plain,
% 3.73/1.03      ( m1_pre_topc(X0_53,X0_53) | ~ l1_pre_topc(X0_53) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_17]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2628,plain,
% 3.73/1.03      ( m1_pre_topc(X0_53,X0_53) = iProver_top
% 3.73/1.03      | l1_pre_topc(X0_53) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2010]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_8,plain,
% 3.73/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.73/1.03      | ~ m1_pre_topc(X3,X1)
% 3.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.73/1.03      | v2_struct_0(X1)
% 3.73/1.03      | v2_struct_0(X2)
% 3.73/1.03      | ~ l1_pre_topc(X1)
% 3.73/1.03      | ~ l1_pre_topc(X2)
% 3.73/1.03      | ~ v2_pre_topc(X1)
% 3.73/1.03      | ~ v2_pre_topc(X2)
% 3.73/1.03      | ~ v1_funct_1(X0)
% 3.73/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.73/1.03      inference(cnf_transformation,[],[f71]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2019,plain,
% 3.73/1.03      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.73/1.03      | ~ m1_pre_topc(X2_53,X0_53)
% 3.73/1.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.73/1.03      | v2_struct_0(X1_53)
% 3.73/1.03      | v2_struct_0(X0_53)
% 3.73/1.03      | ~ l1_pre_topc(X1_53)
% 3.73/1.03      | ~ l1_pre_topc(X0_53)
% 3.73/1.03      | ~ v2_pre_topc(X1_53)
% 3.73/1.03      | ~ v2_pre_topc(X0_53)
% 3.73/1.03      | ~ v1_funct_1(X0_54)
% 3.73/1.03      | k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_54,X2_53) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2619,plain,
% 3.73/1.03      ( k2_partfun1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,u1_struct_0(X2_53)) = k2_tmap_1(X0_53,X1_53,X0_54,X2_53)
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 3.73/1.03      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 3.73/1.03      | v2_struct_0(X0_53) = iProver_top
% 3.73/1.03      | v2_struct_0(X1_53) = iProver_top
% 3.73/1.03      | l1_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | l1_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2019]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4105,plain,
% 3.73/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_53)) = k2_tmap_1(sK2,sK1,sK3,X0_53)
% 3.73/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(X0_53,sK2) != iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | v2_struct_0(sK2) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | l1_pre_topc(sK2) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK2) != iProver_top
% 3.73/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_2637,c_2619]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_32,negated_conjecture,
% 3.73/1.03      ( ~ v2_struct_0(sK2) ),
% 3.73/1.03      inference(cnf_transformation,[],[f92]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_39,plain,
% 3.73/1.03      ( v2_struct_0(sK2) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_40,plain,
% 3.73/1.03      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_6,plain,
% 3.73/1.03      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.73/1.03      inference(cnf_transformation,[],[f69]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2021,plain,
% 3.73/1.03      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.73/1.03      | ~ l1_pre_topc(X1_53)
% 3.73/1.03      | l1_pre_topc(X0_53) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_6]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2797,plain,
% 3.73/1.03      ( ~ m1_pre_topc(sK2,X0_53)
% 3.73/1.03      | ~ l1_pre_topc(X0_53)
% 3.73/1.03      | l1_pre_topc(sK2) ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2021]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2798,plain,
% 3.73/1.03      ( m1_pre_topc(sK2,X0_53) != iProver_top
% 3.73/1.03      | l1_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | l1_pre_topc(sK2) = iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2797]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2800,plain,
% 3.73/1.03      ( m1_pre_topc(sK2,sK1) != iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | l1_pre_topc(sK2) = iProver_top ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2798]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4,plain,
% 3.73/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.73/1.03      | ~ l1_pre_topc(X1)
% 3.73/1.03      | ~ v2_pre_topc(X1)
% 3.73/1.03      | v2_pre_topc(X0) ),
% 3.73/1.03      inference(cnf_transformation,[],[f67]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2023,plain,
% 3.73/1.03      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.73/1.03      | ~ l1_pre_topc(X1_53)
% 3.73/1.03      | ~ v2_pre_topc(X1_53)
% 3.73/1.03      | v2_pre_topc(X0_53) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_4]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2984,plain,
% 3.73/1.03      ( ~ m1_pre_topc(sK2,X0_53)
% 3.73/1.03      | ~ l1_pre_topc(X0_53)
% 3.73/1.03      | ~ v2_pre_topc(X0_53)
% 3.73/1.03      | v2_pre_topc(sK2) ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2023]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2985,plain,
% 3.73/1.03      ( m1_pre_topc(sK2,X0_53) != iProver_top
% 3.73/1.03      | l1_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK2) = iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2984]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2987,plain,
% 3.73/1.03      ( m1_pre_topc(sK2,sK1) != iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK2) = iProver_top ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2985]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4185,plain,
% 3.73/1.03      ( m1_pre_topc(X0_53,sK2) != iProver_top
% 3.73/1.03      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_53)) = k2_tmap_1(sK2,sK1,sK3,X0_53) ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_4105,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_2800,c_2987]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4186,plain,
% 3.73/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_53)) = k2_tmap_1(sK2,sK1,sK3,X0_53)
% 3.73/1.03      | m1_pre_topc(X0_53,sK2) != iProver_top ),
% 3.73/1.03      inference(renaming,[status(thm)],[c_4185]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4191,plain,
% 3.73/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2)
% 3.73/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_2628,c_4186]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4194,plain,
% 3.73/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_4191,c_38,c_40,c_2800]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4645,plain,
% 3.73/1.03      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2)
% 3.73/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 3.73/1.03      inference(light_normalisation,[status(thm)],[c_4643,c_4194]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3244,plain,
% 3.73/1.03      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2010]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3245,plain,
% 3.73/1.03      ( m1_pre_topc(sK2,sK2) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_3244]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4651,plain,
% 3.73/1.03      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_4645,c_36,c_37,c_38,c_40,c_2800,c_3245]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_23,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
% 3.73/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 3.73/1.03      | ~ m1_pre_topc(X0,X3)
% 3.73/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.73/1.03      | v2_struct_0(X3)
% 3.73/1.03      | v2_struct_0(X1)
% 3.73/1.03      | v2_struct_0(X0)
% 3.73/1.03      | ~ l1_pre_topc(X3)
% 3.73/1.03      | ~ l1_pre_topc(X1)
% 3.73/1.03      | ~ v2_pre_topc(X3)
% 3.73/1.03      | ~ v2_pre_topc(X1)
% 3.73/1.03      | ~ v1_funct_1(X2) ),
% 3.73/1.03      inference(cnf_transformation,[],[f86]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2006,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,k3_tmap_1(X2_53,X1_53,X0_53,X0_53,X0_54))
% 3.73/1.03      | ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.73/1.03      | ~ m1_pre_topc(X0_53,X2_53)
% 3.73/1.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.73/1.03      | v2_struct_0(X1_53)
% 3.73/1.03      | v2_struct_0(X0_53)
% 3.73/1.03      | v2_struct_0(X2_53)
% 3.73/1.03      | ~ l1_pre_topc(X1_53)
% 3.73/1.03      | ~ l1_pre_topc(X2_53)
% 3.73/1.03      | ~ v2_pre_topc(X1_53)
% 3.73/1.03      | ~ v2_pre_topc(X2_53)
% 3.73/1.03      | ~ v1_funct_1(X0_54) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_23]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2632,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,k3_tmap_1(X2_53,X1_53,X0_53,X0_53,X0_54)) = iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 3.73/1.03      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 3.73/1.03      | v2_struct_0(X0_53) = iProver_top
% 3.73/1.03      | v2_struct_0(X1_53) = iProver_top
% 3.73/1.03      | v2_struct_0(X2_53) = iProver_top
% 3.73/1.03      | l1_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | l1_pre_topc(X2_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X2_53) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2006]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4653,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top
% 3.73/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.73/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | v2_struct_0(sK2) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_4651,c_2632]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_43,plain,
% 3.73/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4848,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_4653,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_10,plain,
% 3.73/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.73/1.03      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 3.73/1.03      | ~ l1_struct_0(X1)
% 3.73/1.03      | ~ l1_struct_0(X3)
% 3.73/1.03      | ~ l1_struct_0(X2)
% 3.73/1.03      | ~ v1_funct_1(X0) ),
% 3.73/1.03      inference(cnf_transformation,[],[f75]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2017,plain,
% 3.73/1.03      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.73/1.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.73/1.03      | m1_subset_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 3.73/1.03      | ~ l1_struct_0(X1_53)
% 3.73/1.03      | ~ l1_struct_0(X2_53)
% 3.73/1.03      | ~ l1_struct_0(X0_53)
% 3.73/1.03      | ~ v1_funct_1(X0_54) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_10]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2621,plain,
% 3.73/1.03      ( v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 3.73/1.03      | m1_subset_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) = iProver_top
% 3.73/1.03      | l1_struct_0(X1_53) != iProver_top
% 3.73/1.03      | l1_struct_0(X2_53) != iProver_top
% 3.73/1.03      | l1_struct_0(X0_53) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2017]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3,plain,
% 3.73/1.03      ( ~ r2_funct_2(X0,X1,X2,X3)
% 3.73/1.03      | ~ v1_funct_2(X2,X0,X1)
% 3.73/1.03      | ~ v1_funct_2(X3,X0,X1)
% 3.73/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.73/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.73/1.03      | ~ v1_funct_1(X2)
% 3.73/1.03      | ~ v1_funct_1(X3)
% 3.73/1.03      | X3 = X2 ),
% 3.73/1.03      inference(cnf_transformation,[],[f65]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2024,plain,
% 3.73/1.03      ( ~ r2_funct_2(X0_54,X1_54,X2_54,X3_54)
% 3.73/1.03      | ~ v1_funct_2(X2_54,X0_54,X1_54)
% 3.73/1.03      | ~ v1_funct_2(X3_54,X0_54,X1_54)
% 3.73/1.03      | ~ m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 3.73/1.03      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 3.73/1.03      | ~ v1_funct_1(X2_54)
% 3.73/1.03      | ~ v1_funct_1(X3_54)
% 3.73/1.03      | X3_54 = X2_54 ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2614,plain,
% 3.73/1.03      ( X0_54 = X1_54
% 3.73/1.03      | r2_funct_2(X2_54,X3_54,X1_54,X0_54) != iProver_top
% 3.73/1.03      | v1_funct_2(X1_54,X2_54,X3_54) != iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,X2_54,X3_54) != iProver_top
% 3.73/1.03      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 3.73/1.03      | v1_funct_1(X1_54) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2024]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3898,plain,
% 3.73/1.03      ( sK3 = X0_54
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) != iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top
% 3.73/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_2637,c_2614]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4118,plain,
% 3.73/1.03      ( v1_funct_1(X0_54) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | sK3 = X0_54
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) != iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_3898,c_41,c_42]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4119,plain,
% 3.73/1.03      ( sK3 = X0_54
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) != iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(renaming,[status(thm)],[c_4118]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4124,plain,
% 3.73/1.03      ( k2_tmap_1(X0_53,sK1,X0_54,sK2) = sK3
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(X0_53,sK1,X0_54,sK2)) != iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | v1_funct_2(k2_tmap_1(X0_53,sK1,X0_54,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | l1_struct_0(X0_53) != iProver_top
% 3.73/1.03      | l1_struct_0(sK1) != iProver_top
% 3.73/1.03      | l1_struct_0(sK2) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top
% 3.73/1.03      | v1_funct_1(k2_tmap_1(X0_53,sK1,X0_54,sK2)) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_2621,c_4119]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_5,plain,
% 3.73/1.03      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.73/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_102,plain,
% 3.73/1.03      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_104,plain,
% 3.73/1.03      ( l1_struct_0(sK1) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_102]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2022,plain,
% 3.73/1.03      ( l1_struct_0(X0_53) | ~ l1_pre_topc(X0_53) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_5]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2784,plain,
% 3.73/1.03      ( l1_struct_0(sK2) | ~ l1_pre_topc(sK2) ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2022]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2785,plain,
% 3.73/1.03      ( l1_struct_0(sK2) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2784]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4212,plain,
% 3.73/1.03      ( k2_tmap_1(X0_53,sK1,X0_54,sK2) = sK3
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(X0_53,sK1,X0_54,sK2)) != iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | v1_funct_2(k2_tmap_1(X0_53,sK1,X0_54,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | l1_struct_0(X0_53) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top
% 3.73/1.03      | v1_funct_1(k2_tmap_1(X0_53,sK1,X0_54,sK2)) != iProver_top ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_4124,c_38,c_40,c_104,c_2785,c_2800]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4852,plain,
% 3.73/1.03      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 3.73/1.03      | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | l1_struct_0(sK2) != iProver_top
% 3.73/1.03      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 3.73/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_4848,c_4212]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_12,plain,
% 3.73/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.73/1.03      | ~ l1_struct_0(X1)
% 3.73/1.03      | ~ l1_struct_0(X3)
% 3.73/1.03      | ~ l1_struct_0(X2)
% 3.73/1.03      | ~ v1_funct_1(X0)
% 3.73/1.03      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 3.73/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2015,plain,
% 3.73/1.03      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.73/1.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.73/1.03      | ~ l1_struct_0(X1_53)
% 3.73/1.03      | ~ l1_struct_0(X2_53)
% 3.73/1.03      | ~ l1_struct_0(X0_53)
% 3.73/1.03      | ~ v1_funct_1(X0_54)
% 3.73/1.03      | v1_funct_1(k2_tmap_1(X0_53,X1_53,X0_54,X2_53)) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_12]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3062,plain,
% 3.73/1.03      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(sK1))
% 3.73/1.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1))))
% 3.73/1.03      | ~ l1_struct_0(X1_53)
% 3.73/1.03      | ~ l1_struct_0(X0_53)
% 3.73/1.03      | ~ l1_struct_0(sK1)
% 3.73/1.03      | ~ v1_funct_1(X0_54)
% 3.73/1.03      | v1_funct_1(k2_tmap_1(X0_53,sK1,X0_54,X1_53)) ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2015]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3518,plain,
% 3.73/1.03      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.73/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.73/1.03      | ~ l1_struct_0(X0_53)
% 3.73/1.03      | ~ l1_struct_0(sK1)
% 3.73/1.03      | ~ l1_struct_0(sK2)
% 3.73/1.03      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,X0_53))
% 3.73/1.03      | ~ v1_funct_1(sK3) ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_3062]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3724,plain,
% 3.73/1.03      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.73/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.73/1.03      | ~ l1_struct_0(sK1)
% 3.73/1.03      | ~ l1_struct_0(sK2)
% 3.73/1.03      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2))
% 3.73/1.03      | ~ v1_funct_1(sK3) ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_3518]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3727,plain,
% 3.73/1.03      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | l1_struct_0(sK1) != iProver_top
% 3.73/1.03      | l1_struct_0(sK2) != iProver_top
% 3.73/1.03      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top
% 3.73/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_3724]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_11,plain,
% 3.73/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.73/1.03      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 3.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.73/1.03      | ~ l1_struct_0(X1)
% 3.73/1.03      | ~ l1_struct_0(X3)
% 3.73/1.03      | ~ l1_struct_0(X2)
% 3.73/1.03      | ~ v1_funct_1(X0) ),
% 3.73/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2016,plain,
% 3.73/1.03      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.73/1.03      | v1_funct_2(k2_tmap_1(X0_53,X1_53,X0_54,X2_53),u1_struct_0(X2_53),u1_struct_0(X1_53))
% 3.73/1.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.73/1.03      | ~ l1_struct_0(X1_53)
% 3.73/1.03      | ~ l1_struct_0(X2_53)
% 3.73/1.03      | ~ l1_struct_0(X0_53)
% 3.73/1.03      | ~ v1_funct_1(X0_54) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_11]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4145,plain,
% 3.73/1.03      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 3.73/1.03      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.73/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.73/1.03      | ~ l1_struct_0(sK1)
% 3.73/1.03      | ~ l1_struct_0(sK2)
% 3.73/1.03      | ~ v1_funct_1(sK3) ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2016]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4146,plain,
% 3.73/1.03      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 3.73/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | l1_struct_0(sK1) != iProver_top
% 3.73/1.03      | l1_struct_0(sK2) != iProver_top
% 3.73/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_4145]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4887,plain,
% 3.73/1.03      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_4852,c_38,c_40,c_41,c_42,c_43,c_104,c_2785,c_2800,
% 3.73/1.03                 c_3727,c_4146]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_21,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 3.73/1.03      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 3.73/1.03      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 3.73/1.03      | ~ m1_pre_topc(X0,X2)
% 3.73/1.03      | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
% 3.73/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.73/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.73/1.03      | v2_struct_0(X1)
% 3.73/1.03      | v2_struct_0(X2)
% 3.73/1.03      | v2_struct_0(X0)
% 3.73/1.03      | ~ l1_pre_topc(X1)
% 3.73/1.03      | ~ l1_pre_topc(X2)
% 3.73/1.03      | ~ v2_pre_topc(X1)
% 3.73/1.03      | ~ v2_pre_topc(X2)
% 3.73/1.03      | ~ v1_funct_1(X3)
% 3.73/1.03      | ~ v1_funct_1(X4) ),
% 3.73/1.03      inference(cnf_transformation,[],[f84]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2008,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54)
% 3.73/1.03      | ~ v1_funct_2(X1_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.73/1.03      | ~ v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53))
% 3.73/1.03      | ~ m1_pre_topc(X0_53,X2_53)
% 3.73/1.03      | r2_hidden(sK0(X1_53,X2_53,X0_53,X0_54,X1_54),u1_struct_0(X0_53))
% 3.73/1.03      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.73/1.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 3.73/1.03      | v2_struct_0(X1_53)
% 3.73/1.03      | v2_struct_0(X0_53)
% 3.73/1.03      | v2_struct_0(X2_53)
% 3.73/1.03      | ~ l1_pre_topc(X1_53)
% 3.73/1.03      | ~ l1_pre_topc(X2_53)
% 3.73/1.03      | ~ v2_pre_topc(X1_53)
% 3.73/1.03      | ~ v2_pre_topc(X2_53)
% 3.73/1.03      | ~ v1_funct_1(X0_54)
% 3.73/1.03      | ~ v1_funct_1(X1_54) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_21]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2630,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X1_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
% 3.73/1.03      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 3.73/1.03      | r2_hidden(sK0(X1_53,X2_53,X0_53,X0_54,X1_54),u1_struct_0(X0_53)) = iProver_top
% 3.73/1.03      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
% 3.73/1.03      | v2_struct_0(X0_53) = iProver_top
% 3.73/1.03      | v2_struct_0(X1_53) = iProver_top
% 3.73/1.03      | v2_struct_0(X2_53) = iProver_top
% 3.73/1.03      | l1_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | l1_pre_topc(X2_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X2_53) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top
% 3.73/1.03      | v1_funct_1(X1_54) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2008]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4894,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.73/1.03      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | v2_struct_0(sK2) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | l1_pre_topc(sK2) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK2) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top
% 3.73/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_4887,c_2630]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_6260,plain,
% 3.73/1.03      ( v1_funct_1(X0_54) != iProver_top
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_4894,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_2800,
% 3.73/1.03                 c_2987,c_3245]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_6261,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK2)) = iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(renaming,[status(thm)],[c_6260]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_16,plain,
% 3.73/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.73/1.03      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.03      | ~ l1_pre_topc(X1) ),
% 3.73/1.03      inference(cnf_transformation,[],[f79]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2011,plain,
% 3.73/1.03      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.73/1.03      | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53)))
% 3.73/1.03      | ~ l1_pre_topc(X1_53) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_16]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2627,plain,
% 3.73/1.03      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 3.73/1.03      | m1_subset_1(u1_struct_0(X0_53),k1_zfmisc_1(u1_struct_0(X1_53))) = iProver_top
% 3.73/1.03      | l1_pre_topc(X1_53) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2011]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_0,plain,
% 3.73/1.03      ( ~ r2_hidden(X0,X1)
% 3.73/1.03      | m1_subset_1(X0,X2)
% 3.73/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.73/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2027,plain,
% 3.73/1.03      ( ~ r2_hidden(X0_54,X1_54)
% 3.73/1.03      | m1_subset_1(X0_54,X2_54)
% 3.73/1.03      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X2_54)) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2611,plain,
% 3.73/1.03      ( r2_hidden(X0_54,X1_54) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,X2_54) = iProver_top
% 3.73/1.03      | m1_subset_1(X1_54,k1_zfmisc_1(X2_54)) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2027]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3384,plain,
% 3.73/1.03      ( m1_pre_topc(X0_53,X1_53) != iProver_top
% 3.73/1.03      | r2_hidden(X0_54,u1_struct_0(X0_53)) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,u1_struct_0(X1_53)) = iProver_top
% 3.73/1.03      | l1_pre_topc(X1_53) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_2627,c_2611]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_6265,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,X0_53) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(X0_53)) = iProver_top
% 3.73/1.03      | l1_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_6261,c_3384]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_27,negated_conjecture,
% 3.73/1.03      ( ~ r2_hidden(X0,u1_struct_0(sK2))
% 3.73/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.73/1.03      | k1_funct_1(sK3,X0) = X0 ),
% 3.73/1.03      inference(cnf_transformation,[],[f97]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2002,negated_conjecture,
% 3.73/1.03      ( ~ r2_hidden(X0_54,u1_struct_0(sK2))
% 3.73/1.03      | ~ m1_subset_1(X0_54,u1_struct_0(sK1))
% 3.73/1.03      | k1_funct_1(sK3,X0_54) = X0_54 ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_27]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2636,plain,
% 3.73/1.03      ( k1_funct_1(sK3,X0_54) = X0_54
% 3.73/1.03      | r2_hidden(X0_54,u1_struct_0(sK2)) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,u1_struct_0(sK1)) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2002]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_6264,plain,
% 3.73/1.03      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_6261,c_2636]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_6555,plain,
% 3.73/1.03      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_6265,c_6264]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_6851,plain,
% 3.73/1.03      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_6555,c_38,c_40]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_6852,plain,
% 3.73/1.03      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(renaming,[status(thm)],[c_6851]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_6856,plain,
% 3.73/1.03      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 3.73/1.03      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_2624,c_6852]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_26,negated_conjecture,
% 3.73/1.03      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
% 3.73/1.03      inference(cnf_transformation,[],[f98]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2029,plain,( X0_54 = X0_54 ),theory(equality) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2054,plain,
% 3.73/1.03      ( sK3 = sK3 ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2029]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2,plain,
% 3.73/1.03      ( r2_funct_2(X0,X1,X2,X2)
% 3.73/1.03      | ~ v1_funct_2(X2,X0,X1)
% 3.73/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.73/1.03      | ~ v1_funct_1(X2) ),
% 3.73/1.03      inference(cnf_transformation,[],[f99]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2025,plain,
% 3.73/1.03      ( r2_funct_2(X0_54,X1_54,X2_54,X2_54)
% 3.73/1.03      | ~ v1_funct_2(X2_54,X0_54,X1_54)
% 3.73/1.03      | ~ m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 3.73/1.03      | ~ v1_funct_1(X2_54) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3167,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 3.73/1.03      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 3.73/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.73/1.03      | ~ v1_funct_1(sK3) ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2025]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2040,plain,
% 3.73/1.03      ( ~ r2_funct_2(X0_54,X1_54,X2_54,X3_54)
% 3.73/1.03      | r2_funct_2(X4_54,X5_54,X6_54,X7_54)
% 3.73/1.03      | X4_54 != X0_54
% 3.73/1.03      | X5_54 != X1_54
% 3.73/1.03      | X6_54 != X2_54
% 3.73/1.03      | X7_54 != X3_54 ),
% 3.73/1.03      theory(equality) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2767,plain,
% 3.73/1.03      ( ~ r2_funct_2(X0_54,X1_54,X2_54,X3_54)
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
% 3.73/1.03      | k4_tmap_1(sK1,sK2) != X2_54
% 3.73/1.03      | u1_struct_0(sK1) != X1_54
% 3.73/1.03      | u1_struct_0(sK2) != X0_54
% 3.73/1.03      | sK3 != X3_54 ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2040]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3204,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
% 3.73/1.03      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 3.73/1.03      | k4_tmap_1(sK1,sK2) != sK3
% 3.73/1.03      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.73/1.03      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 3.73/1.03      | sK3 != sK3 ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2767]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3297,plain,
% 3.73/1.03      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2029]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3306,plain,
% 3.73/1.03      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2029]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_15,plain,
% 3.73/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.73/1.03      | v2_struct_0(X1)
% 3.73/1.03      | ~ l1_pre_topc(X1)
% 3.73/1.03      | ~ v2_pre_topc(X1)
% 3.73/1.03      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 3.73/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2012,plain,
% 3.73/1.03      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.73/1.03      | v2_struct_0(X1_53)
% 3.73/1.03      | ~ l1_pre_topc(X1_53)
% 3.73/1.03      | ~ v2_pre_topc(X1_53)
% 3.73/1.03      | v1_funct_1(k4_tmap_1(X1_53,X0_53)) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_15]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3511,plain,
% 3.73/1.03      ( ~ m1_pre_topc(sK2,sK1)
% 3.73/1.03      | v2_struct_0(sK1)
% 3.73/1.03      | ~ l1_pre_topc(sK1)
% 3.73/1.03      | ~ v2_pre_topc(sK1)
% 3.73/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2012]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3512,plain,
% 3.73/1.03      ( m1_pre_topc(sK2,sK1) != iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_3511]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_14,plain,
% 3.73/1.03      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 3.73/1.03      | ~ m1_pre_topc(X1,X0)
% 3.73/1.03      | v2_struct_0(X0)
% 3.73/1.03      | ~ l1_pre_topc(X0)
% 3.73/1.03      | ~ v2_pre_topc(X0) ),
% 3.73/1.03      inference(cnf_transformation,[],[f77]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2013,plain,
% 3.73/1.03      ( v1_funct_2(k4_tmap_1(X0_53,X1_53),u1_struct_0(X1_53),u1_struct_0(X0_53))
% 3.73/1.03      | ~ m1_pre_topc(X1_53,X0_53)
% 3.73/1.03      | v2_struct_0(X0_53)
% 3.73/1.03      | ~ l1_pre_topc(X0_53)
% 3.73/1.03      | ~ v2_pre_topc(X0_53) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_14]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3710,plain,
% 3.73/1.03      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 3.73/1.03      | ~ m1_pre_topc(sK2,sK1)
% 3.73/1.03      | v2_struct_0(sK1)
% 3.73/1.03      | ~ l1_pre_topc(sK1)
% 3.73/1.03      | ~ v2_pre_topc(sK1) ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2013]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3711,plain,
% 3.73/1.03      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_3710]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4123,plain,
% 3.73/1.03      ( k4_tmap_1(sK1,sK2) = sK3
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
% 3.73/1.03      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_2624,c_4119]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_7098,plain,
% 3.73/1.03      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_6856,c_36,c_37,c_38,c_40,c_30,c_29,c_28,c_26,c_2054,
% 3.73/1.03                 c_3167,c_3204,c_3297,c_3306,c_3512,c_3711,c_4123]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_22,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 3.73/1.03      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 3.73/1.03      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 3.73/1.03      | ~ m1_pre_topc(X0,X2)
% 3.73/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.73/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.73/1.03      | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2))
% 3.73/1.03      | v2_struct_0(X1)
% 3.73/1.03      | v2_struct_0(X2)
% 3.73/1.03      | v2_struct_0(X0)
% 3.73/1.03      | ~ l1_pre_topc(X1)
% 3.73/1.03      | ~ l1_pre_topc(X2)
% 3.73/1.03      | ~ v2_pre_topc(X1)
% 3.73/1.03      | ~ v2_pre_topc(X2)
% 3.73/1.03      | ~ v1_funct_1(X3)
% 3.73/1.03      | ~ v1_funct_1(X4) ),
% 3.73/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2007,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54)
% 3.73/1.03      | ~ v1_funct_2(X1_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.73/1.03      | ~ v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53))
% 3.73/1.03      | ~ m1_pre_topc(X0_53,X2_53)
% 3.73/1.03      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.73/1.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 3.73/1.03      | m1_subset_1(sK0(X1_53,X2_53,X0_53,X0_54,X1_54),u1_struct_0(X2_53))
% 3.73/1.03      | v2_struct_0(X1_53)
% 3.73/1.03      | v2_struct_0(X0_53)
% 3.73/1.03      | v2_struct_0(X2_53)
% 3.73/1.03      | ~ l1_pre_topc(X1_53)
% 3.73/1.03      | ~ l1_pre_topc(X2_53)
% 3.73/1.03      | ~ v2_pre_topc(X1_53)
% 3.73/1.03      | ~ v2_pre_topc(X2_53)
% 3.73/1.03      | ~ v1_funct_1(X0_54)
% 3.73/1.03      | ~ v1_funct_1(X1_54) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_22]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2631,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X1_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
% 3.73/1.03      | m1_pre_topc(X0_53,X2_53) != iProver_top
% 3.73/1.03      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
% 3.73/1.03      | m1_subset_1(sK0(X1_53,X2_53,X0_53,X0_54,X1_54),u1_struct_0(X2_53)) = iProver_top
% 3.73/1.03      | v2_struct_0(X0_53) = iProver_top
% 3.73/1.03      | v2_struct_0(X1_53) = iProver_top
% 3.73/1.03      | v2_struct_0(X2_53) = iProver_top
% 3.73/1.03      | l1_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | l1_pre_topc(X2_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X2_53) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top
% 3.73/1.03      | v1_funct_1(X1_54) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2007]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_1,plain,
% 3.73/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.73/1.03      | ~ m1_subset_1(X3,X1)
% 3.73/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/1.03      | v1_xboole_0(X1)
% 3.73/1.03      | ~ v1_funct_1(X0)
% 3.73/1.03      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.73/1.03      inference(cnf_transformation,[],[f64]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2026,plain,
% 3.73/1.03      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 3.73/1.03      | ~ m1_subset_1(X3_54,X1_54)
% 3.73/1.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 3.73/1.03      | v1_xboole_0(X1_54)
% 3.73/1.03      | ~ v1_funct_1(X0_54)
% 3.73/1.03      | k3_funct_2(X1_54,X2_54,X0_54,X3_54) = k1_funct_1(X0_54,X3_54) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2612,plain,
% 3.73/1.03      ( k3_funct_2(X0_54,X1_54,X2_54,X3_54) = k1_funct_1(X2_54,X3_54)
% 3.73/1.03      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 3.73/1.03      | m1_subset_1(X3_54,X0_54) != iProver_top
% 3.73/1.03      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 3.73/1.03      | v1_xboole_0(X0_54) = iProver_top
% 3.73/1.03      | v1_funct_1(X2_54) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2026]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3456,plain,
% 3.73/1.03      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = k1_funct_1(sK3,X0_54)
% 3.73/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top
% 3.73/1.03      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 3.73/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_2637,c_2612]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_7,plain,
% 3.73/1.03      ( v2_struct_0(X0)
% 3.73/1.03      | ~ l1_struct_0(X0)
% 3.73/1.03      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.73/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2020,plain,
% 3.73/1.03      ( v2_struct_0(X0_53)
% 3.73/1.03      | ~ l1_struct_0(X0_53)
% 3.73/1.03      | ~ v1_xboole_0(u1_struct_0(X0_53)) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_7]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2748,plain,
% 3.73/1.03      ( v2_struct_0(sK2)
% 3.73/1.03      | ~ l1_struct_0(sK2)
% 3.73/1.03      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2020]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2749,plain,
% 3.73/1.03      ( v2_struct_0(sK2) = iProver_top
% 3.73/1.03      | l1_struct_0(sK2) != iProver_top
% 3.73/1.03      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2748]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_3736,plain,
% 3.73/1.03      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = k1_funct_1(sK3,X0_54)
% 3.73/1.03      | m1_subset_1(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_3456,c_38,c_39,c_40,c_41,c_42,c_2749,c_2785,c_2800]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4571,plain,
% 3.73/1.03      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_53,sK2,X1_53,X0_54,X1_54)) = k1_funct_1(sK3,sK0(X0_53,sK2,X1_53,X0_54,X1_54))
% 3.73/1.03      | r2_funct_2(u1_struct_0(X1_53),u1_struct_0(X0_53),k2_tmap_1(sK2,X0_53,X0_54,X1_53),X1_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X1_54,u1_struct_0(X1_53),u1_struct_0(X0_53)) != iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
% 3.73/1.03      | m1_pre_topc(X1_53,sK2) != iProver_top
% 3.73/1.03      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X0_53)))) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
% 3.73/1.03      | v2_struct_0(X1_53) = iProver_top
% 3.73/1.03      | v2_struct_0(X0_53) = iProver_top
% 3.73/1.03      | v2_struct_0(sK2) = iProver_top
% 3.73/1.03      | l1_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | l1_pre_topc(sK2) != iProver_top
% 3.73/1.03      | v2_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK2) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top
% 3.73/1.03      | v1_funct_1(X1_54) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_2631,c_3736]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4728,plain,
% 3.73/1.03      ( v2_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v2_struct_0(X0_53) = iProver_top
% 3.73/1.03      | v2_struct_0(X1_53) = iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
% 3.73/1.03      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X0_53)))) != iProver_top
% 3.73/1.03      | m1_pre_topc(X1_53,sK2) != iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
% 3.73/1.03      | v1_funct_2(X1_54,u1_struct_0(X1_53),u1_struct_0(X0_53)) != iProver_top
% 3.73/1.03      | r2_funct_2(u1_struct_0(X1_53),u1_struct_0(X0_53),k2_tmap_1(sK2,X0_53,X0_54,X1_53),X1_54) = iProver_top
% 3.73/1.03      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_53,sK2,X1_53,X0_54,X1_54)) = k1_funct_1(sK3,sK0(X0_53,sK2,X1_53,X0_54,X1_54))
% 3.73/1.03      | l1_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top
% 3.73/1.03      | v1_funct_1(X1_54) != iProver_top ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_4571,c_37,c_38,c_39,c_40,c_2800,c_2987]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4729,plain,
% 3.73/1.03      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0_53,sK2,X1_53,X0_54,X1_54)) = k1_funct_1(sK3,sK0(X0_53,sK2,X1_53,X0_54,X1_54))
% 3.73/1.03      | r2_funct_2(u1_struct_0(X1_53),u1_struct_0(X0_53),k2_tmap_1(sK2,X0_53,X0_54,X1_53),X1_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X1_54,u1_struct_0(X1_53),u1_struct_0(X0_53)) != iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(X0_53)) != iProver_top
% 3.73/1.03      | m1_pre_topc(X1_53,sK2) != iProver_top
% 3.73/1.03      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_53),u1_struct_0(X0_53)))) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_53)))) != iProver_top
% 3.73/1.03      | v2_struct_0(X0_53) = iProver_top
% 3.73/1.03      | v2_struct_0(X1_53) = iProver_top
% 3.73/1.03      | l1_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top
% 3.73/1.03      | v1_funct_1(X1_54) != iProver_top ),
% 3.73/1.03      inference(renaming,[status(thm)],[c_4728]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4902,plain,
% 3.73/1.03      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54))
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | v2_struct_0(sK2) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top
% 3.73/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_4887,c_4729]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_5321,plain,
% 3.73/1.03      ( v1_funct_1(X0_54) != iProver_top
% 3.73/1.03      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54))
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_4902,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_2800,
% 3.73/1.03                 c_3245]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_5322,plain,
% 3.73/1.03      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_54)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_54))
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(renaming,[status(thm)],[c_5321]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_5326,plain,
% 3.73/1.03      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 3.73/1.03      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_2624,c_5322]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_5398,plain,
% 3.73/1.03      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_5326,c_36,c_37,c_38,c_40,c_30,c_29,c_28,c_26,c_2054,
% 3.73/1.03                 c_3167,c_3204,c_3297,c_3306,c_3512,c_3711,c_4123]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_20,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 3.73/1.03      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 3.73/1.03      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 3.73/1.03      | ~ m1_pre_topc(X0,X2)
% 3.73/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 3.73/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 3.73/1.03      | v2_struct_0(X1)
% 3.73/1.03      | v2_struct_0(X2)
% 3.73/1.03      | v2_struct_0(X0)
% 3.73/1.03      | ~ l1_pre_topc(X1)
% 3.73/1.03      | ~ l1_pre_topc(X2)
% 3.73/1.03      | ~ v2_pre_topc(X1)
% 3.73/1.03      | ~ v2_pre_topc(X2)
% 3.73/1.03      | ~ v1_funct_1(X3)
% 3.73/1.03      | ~ v1_funct_1(X4)
% 3.73/1.03      | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK0(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK0(X1,X2,X0,X3,X4)) ),
% 3.73/1.03      inference(cnf_transformation,[],[f85]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2009,plain,
% 3.73/1.03      ( r2_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),k2_tmap_1(X2_53,X1_53,X0_54,X0_53),X1_54)
% 3.73/1.03      | ~ v1_funct_2(X1_54,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 3.73/1.03      | ~ v1_funct_2(X0_54,u1_struct_0(X2_53),u1_struct_0(X1_53))
% 3.73/1.03      | ~ m1_pre_topc(X0_53,X2_53)
% 3.73/1.03      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 3.73/1.03      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53))))
% 3.73/1.03      | v2_struct_0(X1_53)
% 3.73/1.03      | v2_struct_0(X0_53)
% 3.73/1.03      | v2_struct_0(X2_53)
% 3.73/1.03      | ~ l1_pre_topc(X1_53)
% 3.73/1.03      | ~ l1_pre_topc(X2_53)
% 3.73/1.03      | ~ v2_pre_topc(X1_53)
% 3.73/1.03      | ~ v2_pre_topc(X2_53)
% 3.73/1.03      | ~ v1_funct_1(X0_54)
% 3.73/1.03      | ~ v1_funct_1(X1_54)
% 3.73/1.03      | k3_funct_2(u1_struct_0(X2_53),u1_struct_0(X1_53),X0_54,sK0(X1_53,X2_53,X0_53,X0_54,X1_54)) != k1_funct_1(X1_54,sK0(X1_53,X2_53,X0_53,X0_54,X1_54)) ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_20]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2629,plain,
% 3.73/1.03      ( k3_funct_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_54,sK0(X1_53,X0_53,X2_53,X0_54,X1_54)) != k1_funct_1(X1_54,sK0(X1_53,X0_53,X2_53,X0_54,X1_54))
% 3.73/1.03      | r2_funct_2(u1_struct_0(X2_53),u1_struct_0(X1_53),k2_tmap_1(X0_53,X1_53,X0_54,X2_53),X1_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X1_54,u1_struct_0(X2_53),u1_struct_0(X1_53)) != iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 3.73/1.03      | m1_pre_topc(X2_53,X0_53) != iProver_top
% 3.73/1.03      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_53),u1_struct_0(X1_53)))) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 3.73/1.03      | v2_struct_0(X2_53) = iProver_top
% 3.73/1.03      | v2_struct_0(X1_53) = iProver_top
% 3.73/1.03      | v2_struct_0(X0_53) = iProver_top
% 3.73/1.03      | l1_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | l1_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X1_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top
% 3.73/1.03      | v1_funct_1(X1_54) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2009]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_5400,plain,
% 3.73/1.03      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),k4_tmap_1(sK1,sK2)) = iProver_top
% 3.73/1.03      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.73/1.03      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | v2_struct_0(sK2) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | l1_pre_topc(sK2) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK2) != iProver_top
% 3.73/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 3.73/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_5398,c_2629]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_5401,plain,
% 3.73/1.03      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 3.73/1.03      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 3.73/1.03      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | v2_struct_0(sK2) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | l1_pre_topc(sK2) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK2) != iProver_top
% 3.73/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 3.73/1.03      | v1_funct_1(sK3) != iProver_top ),
% 3.73/1.03      inference(light_normalisation,[status(thm)],[c_5400,c_4887]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4129,plain,
% 3.73/1.03      ( ~ m1_pre_topc(sK2,sK1)
% 3.73/1.03      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.73/1.03      | v2_struct_0(sK1)
% 3.73/1.03      | ~ l1_pre_topc(sK1)
% 3.73/1.03      | ~ v2_pre_topc(sK1) ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_2014]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_4130,plain,
% 3.73/1.03      ( m1_pre_topc(sK2,sK1) != iProver_top
% 3.73/1.03      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_4129]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_6460,plain,
% 3.73/1.03      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_5401,c_36,c_37,c_38,c_39,c_40,c_30,c_41,c_29,c_42,
% 3.73/1.03                 c_28,c_43,c_26,c_2054,c_2800,c_2987,c_3167,c_3204,
% 3.73/1.03                 c_3245,c_3297,c_3306,c_3512,c_3711,c_4123,c_4130]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_7100,plain,
% 3.73/1.03      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 3.73/1.03      inference(demodulation,[status(thm)],[c_7098,c_6460]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_25,plain,
% 3.73/1.03      ( ~ m1_pre_topc(X0,X1)
% 3.73/1.03      | ~ r2_hidden(X2,u1_struct_0(X0))
% 3.73/1.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.73/1.03      | v2_struct_0(X1)
% 3.73/1.03      | v2_struct_0(X0)
% 3.73/1.03      | ~ l1_pre_topc(X1)
% 3.73/1.03      | ~ v2_pre_topc(X1)
% 3.73/1.03      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 3.73/1.03      inference(cnf_transformation,[],[f88]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2004,plain,
% 3.73/1.03      ( ~ m1_pre_topc(X0_53,X1_53)
% 3.73/1.03      | ~ r2_hidden(X0_54,u1_struct_0(X0_53))
% 3.73/1.03      | ~ m1_subset_1(X0_54,u1_struct_0(X1_53))
% 3.73/1.03      | v2_struct_0(X1_53)
% 3.73/1.03      | v2_struct_0(X0_53)
% 3.73/1.03      | ~ l1_pre_topc(X1_53)
% 3.73/1.03      | ~ v2_pre_topc(X1_53)
% 3.73/1.03      | k1_funct_1(k4_tmap_1(X1_53,X0_53),X0_54) = X0_54 ),
% 3.73/1.03      inference(subtyping,[status(esa)],[c_25]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_2634,plain,
% 3.73/1.03      ( k1_funct_1(k4_tmap_1(X0_53,X1_53),X0_54) = X0_54
% 3.73/1.03      | m1_pre_topc(X1_53,X0_53) != iProver_top
% 3.73/1.03      | r2_hidden(X0_54,u1_struct_0(X1_53)) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,u1_struct_0(X0_53)) != iProver_top
% 3.73/1.03      | v2_struct_0(X1_53) = iProver_top
% 3.73/1.03      | v2_struct_0(X0_53) = iProver_top
% 3.73/1.03      | l1_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X0_53) != iProver_top ),
% 3.73/1.03      inference(predicate_to_equality,[status(thm)],[c_2004]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_6266,plain,
% 3.73/1.03      ( k1_funct_1(k4_tmap_1(X0_53,sK2),sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,X0_53) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_54),u1_struct_0(X0_53)) != iProver_top
% 3.73/1.03      | v2_struct_0(X0_53) = iProver_top
% 3.73/1.03      | v2_struct_0(sK2) = iProver_top
% 3.73/1.03      | l1_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_6261,c_2634]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_6783,plain,
% 3.73/1.03      ( v2_struct_0(X0_53) = iProver_top
% 3.73/1.03      | k1_funct_1(k4_tmap_1(X0_53,sK2),sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,X0_53) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | l1_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(global_propositional_subsumption,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_6266,c_39,c_6265]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_6784,plain,
% 3.73/1.03      ( k1_funct_1(k4_tmap_1(X0_53,sK2),sK0(sK1,sK2,sK2,sK3,X0_54)) = sK0(sK1,sK2,sK2,sK3,X0_54)
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_54) = iProver_top
% 3.73/1.03      | v1_funct_2(X0_54,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,X0_53) != iProver_top
% 3.73/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.73/1.03      | v2_struct_0(X0_53) = iProver_top
% 3.73/1.03      | l1_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v1_funct_1(X0_54) != iProver_top ),
% 3.73/1.03      inference(renaming,[status(thm)],[c_6783]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_6788,plain,
% 3.73/1.03      ( k1_funct_1(k4_tmap_1(X0_53,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 3.73/1.03      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,X0_53) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.73/1.03      | v2_struct_0(X0_53) = iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | l1_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(X0_53) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 3.73/1.03      inference(superposition,[status(thm)],[c_2624,c_6784]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(c_6791,plain,
% 3.73/1.03      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 3.73/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 3.73/1.03      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.73/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.73/1.03      | v2_struct_0(sK1) = iProver_top
% 3.73/1.03      | l1_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v2_pre_topc(sK1) != iProver_top
% 3.73/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 3.73/1.03      inference(instantiation,[status(thm)],[c_6788]) ).
% 3.73/1.03  
% 3.73/1.03  cnf(contradiction,plain,
% 3.73/1.03      ( $false ),
% 3.73/1.03      inference(minisat,
% 3.73/1.03                [status(thm)],
% 3.73/1.03                [c_7100,c_6791,c_4123,c_3711,c_3512,c_3306,c_3297,c_3204,
% 3.73/1.03                 c_3167,c_2054,c_26,c_28,c_29,c_30,c_40,c_38,c_37,c_36]) ).
% 3.73/1.03  
% 3.73/1.03  
% 3.73/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/1.03  
% 3.73/1.03  ------                               Statistics
% 3.73/1.03  
% 3.73/1.03  ------ General
% 3.73/1.03  
% 3.73/1.03  abstr_ref_over_cycles:                  0
% 3.73/1.03  abstr_ref_under_cycles:                 0
% 3.73/1.03  gc_basic_clause_elim:                   0
% 3.73/1.03  forced_gc_time:                         0
% 3.73/1.03  parsing_time:                           0.016
% 3.73/1.03  unif_index_cands_time:                  0.
% 3.73/1.03  unif_index_add_time:                    0.
% 3.73/1.03  orderings_time:                         0.
% 3.73/1.03  out_proof_time:                         0.02
% 3.73/1.03  total_time:                             0.395
% 3.73/1.03  num_of_symbols:                         58
% 3.73/1.03  num_of_terms:                           11158
% 3.73/1.03  
% 3.73/1.03  ------ Preprocessing
% 3.73/1.03  
% 3.73/1.03  num_of_splits:                          0
% 3.73/1.03  num_of_split_atoms:                     0
% 3.73/1.03  num_of_reused_defs:                     0
% 3.73/1.03  num_eq_ax_congr_red:                    59
% 3.73/1.03  num_of_sem_filtered_clauses:            1
% 3.73/1.03  num_of_subtypes:                        2
% 3.73/1.03  monotx_restored_types:                  0
% 3.73/1.03  sat_num_of_epr_types:                   0
% 3.73/1.03  sat_num_of_non_cyclic_types:            0
% 3.73/1.03  sat_guarded_non_collapsed_types:        1
% 3.73/1.03  num_pure_diseq_elim:                    0
% 3.73/1.03  simp_replaced_by:                       0
% 3.73/1.03  res_preprocessed:                       165
% 3.73/1.03  prep_upred:                             0
% 3.73/1.03  prep_unflattend:                        64
% 3.73/1.03  smt_new_axioms:                         0
% 3.73/1.03  pred_elim_cands:                        11
% 3.73/1.03  pred_elim:                              1
% 3.73/1.03  pred_elim_cl:                           2
% 3.73/1.03  pred_elim_cycles:                       7
% 3.73/1.03  merged_defs:                            0
% 3.73/1.03  merged_defs_ncl:                        0
% 3.73/1.03  bin_hyper_res:                          0
% 3.73/1.03  prep_cycles:                            4
% 3.73/1.03  pred_elim_time:                         0.045
% 3.73/1.03  splitting_time:                         0.
% 3.73/1.03  sem_filter_time:                        0.
% 3.73/1.03  monotx_time:                            0.
% 3.73/1.03  subtype_inf_time:                       0.
% 3.73/1.03  
% 3.73/1.03  ------ Problem properties
% 3.73/1.03  
% 3.73/1.03  clauses:                                34
% 3.73/1.03  conjectures:                            10
% 3.73/1.03  epr:                                    11
% 3.73/1.03  horn:                                   23
% 3.73/1.03  ground:                                 9
% 3.73/1.03  unary:                                  9
% 3.73/1.03  binary:                                 2
% 3.73/1.03  lits:                                   183
% 3.73/1.03  lits_eq:                                7
% 3.73/1.03  fd_pure:                                0
% 3.73/1.03  fd_pseudo:                              0
% 3.73/1.03  fd_cond:                                0
% 3.73/1.03  fd_pseudo_cond:                         1
% 3.73/1.03  ac_symbols:                             0
% 3.73/1.03  
% 3.73/1.03  ------ Propositional Solver
% 3.73/1.03  
% 3.73/1.03  prop_solver_calls:                      29
% 3.73/1.03  prop_fast_solver_calls:                 2973
% 3.73/1.03  smt_solver_calls:                       0
% 3.73/1.03  smt_fast_solver_calls:                  0
% 3.73/1.03  prop_num_of_clauses:                    2748
% 3.73/1.03  prop_preprocess_simplified:             8436
% 3.73/1.03  prop_fo_subsumed:                       169
% 3.73/1.03  prop_solver_time:                       0.
% 3.73/1.03  smt_solver_time:                        0.
% 3.73/1.03  smt_fast_solver_time:                   0.
% 3.73/1.03  prop_fast_solver_time:                  0.
% 3.73/1.03  prop_unsat_core_time:                   0.
% 3.73/1.03  
% 3.73/1.03  ------ QBF
% 3.73/1.03  
% 3.73/1.03  qbf_q_res:                              0
% 3.73/1.03  qbf_num_tautologies:                    0
% 3.73/1.03  qbf_prep_cycles:                        0
% 3.73/1.03  
% 3.73/1.03  ------ BMC1
% 3.73/1.03  
% 3.73/1.03  bmc1_current_bound:                     -1
% 3.73/1.03  bmc1_last_solved_bound:                 -1
% 3.73/1.03  bmc1_unsat_core_size:                   -1
% 3.73/1.03  bmc1_unsat_core_parents_size:           -1
% 3.73/1.03  bmc1_merge_next_fun:                    0
% 3.73/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.73/1.03  
% 3.73/1.03  ------ Instantiation
% 3.73/1.03  
% 3.73/1.03  inst_num_of_clauses:                    725
% 3.73/1.03  inst_num_in_passive:                    108
% 3.73/1.03  inst_num_in_active:                     368
% 3.73/1.03  inst_num_in_unprocessed:                249
% 3.73/1.03  inst_num_of_loops:                      470
% 3.73/1.03  inst_num_of_learning_restarts:          0
% 3.73/1.03  inst_num_moves_active_passive:          98
% 3.73/1.03  inst_lit_activity:                      0
% 3.73/1.03  inst_lit_activity_moves:                0
% 3.73/1.03  inst_num_tautologies:                   0
% 3.73/1.03  inst_num_prop_implied:                  0
% 3.73/1.03  inst_num_existing_simplified:           0
% 3.73/1.03  inst_num_eq_res_simplified:             0
% 3.73/1.03  inst_num_child_elim:                    0
% 3.73/1.03  inst_num_of_dismatching_blockings:      267
% 3.73/1.03  inst_num_of_non_proper_insts:           912
% 3.73/1.03  inst_num_of_duplicates:                 0
% 3.73/1.03  inst_inst_num_from_inst_to_res:         0
% 3.73/1.03  inst_dismatching_checking_time:         0.
% 3.73/1.03  
% 3.73/1.03  ------ Resolution
% 3.73/1.03  
% 3.73/1.03  res_num_of_clauses:                     0
% 3.73/1.03  res_num_in_passive:                     0
% 3.73/1.03  res_num_in_active:                      0
% 3.73/1.03  res_num_of_loops:                       169
% 3.73/1.03  res_forward_subset_subsumed:            47
% 3.73/1.03  res_backward_subset_subsumed:           0
% 3.73/1.03  res_forward_subsumed:                   0
% 3.73/1.03  res_backward_subsumed:                  0
% 3.73/1.03  res_forward_subsumption_resolution:     0
% 3.73/1.03  res_backward_subsumption_resolution:    0
% 3.73/1.03  res_clause_to_clause_subsumption:       508
% 3.73/1.03  res_orphan_elimination:                 0
% 3.73/1.03  res_tautology_del:                      42
% 3.73/1.03  res_num_eq_res_simplified:              0
% 3.73/1.03  res_num_sel_changes:                    0
% 3.73/1.03  res_moves_from_active_to_pass:          0
% 3.73/1.03  
% 3.73/1.03  ------ Superposition
% 3.73/1.03  
% 3.73/1.03  sup_time_total:                         0.
% 3.73/1.03  sup_time_generating:                    0.
% 3.73/1.03  sup_time_sim_full:                      0.
% 3.73/1.03  sup_time_sim_immed:                     0.
% 3.73/1.03  
% 3.73/1.03  sup_num_of_clauses:                     98
% 3.73/1.03  sup_num_in_active:                      82
% 3.73/1.03  sup_num_in_passive:                     16
% 3.73/1.03  sup_num_of_loops:                       92
% 3.73/1.03  sup_fw_superposition:                   58
% 3.73/1.03  sup_bw_superposition:                   38
% 3.73/1.03  sup_immediate_simplified:               19
% 3.73/1.03  sup_given_eliminated:                   0
% 3.73/1.03  comparisons_done:                       0
% 3.73/1.03  comparisons_avoided:                    6
% 3.73/1.03  
% 3.73/1.03  ------ Simplifications
% 3.73/1.03  
% 3.73/1.03  
% 3.73/1.03  sim_fw_subset_subsumed:                 13
% 3.73/1.03  sim_bw_subset_subsumed:                 1
% 3.73/1.03  sim_fw_subsumed:                        3
% 3.73/1.03  sim_bw_subsumed:                        4
% 3.73/1.03  sim_fw_subsumption_res:                 0
% 3.73/1.03  sim_bw_subsumption_res:                 0
% 3.73/1.03  sim_tautology_del:                      5
% 3.73/1.03  sim_eq_tautology_del:                   2
% 3.73/1.03  sim_eq_res_simp:                        0
% 3.73/1.03  sim_fw_demodulated:                     0
% 3.73/1.03  sim_bw_demodulated:                     6
% 3.73/1.03  sim_light_normalised:                   3
% 3.73/1.03  sim_joinable_taut:                      0
% 3.73/1.03  sim_joinable_simp:                      0
% 3.73/1.03  sim_ac_normalised:                      0
% 3.73/1.03  sim_smt_subsumption:                    0
% 3.73/1.03  
%------------------------------------------------------------------------------
