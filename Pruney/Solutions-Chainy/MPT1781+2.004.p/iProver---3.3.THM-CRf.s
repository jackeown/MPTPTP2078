%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:43 EST 2020

% Result     : Theorem 11.00s
% Output     : CNFRefutation 11.00s
% Verified   : 
% Statistics : Number of formulae       :  275 (12306 expanded)
%              Number of clauses        :  185 (3345 expanded)
%              Number of leaves         :   23 (3824 expanded)
%              Depth                    :   38
%              Number of atoms          : 1815 (123821 expanded)
%              Number of equality atoms :  724 (16916 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal clause size      :   24 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f49,f55,f54,f53])).

fof(f84,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f81,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f82,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
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
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
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
    inference(flattening,[],[f34])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
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
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f35])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
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
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

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

fof(f50,plain,(
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

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f51,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
        & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f51])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
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

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f61])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f52])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1131,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | m1_subset_1(k4_tmap_1(X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1742,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_subset_1(k4_tmap_1(X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1131])).

cnf(c_16,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1127,plain,
    ( m1_pre_topc(X0_51,X0_51)
    | ~ l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1746,plain,
    ( m1_pre_topc(X0_51,X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1127])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1115,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1758,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1115])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1118,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1755,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1118])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f65])).

cnf(c_1135,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X2_51,X0_51)
    | ~ m1_pre_topc(X0_51,X3_51)
    | ~ m1_pre_topc(X2_51,X3_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X3_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X3_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X3_51)
    | ~ v1_funct_1(X0_52)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1738,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52)
    | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | m1_pre_topc(X2_51,X3_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X3_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X3_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1135])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1122,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X0_51)
    | m1_pre_topc(X2_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1751,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X2_51,X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1122])).

cnf(c_2044,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52)
    | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X3_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X3_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X3_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X3_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1738,c_1751])).

cnf(c_6129,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1755,c_2044])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_33,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_35,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6362,plain,
    ( l1_pre_topc(X1_51) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6129,c_33,c_34,c_35,c_38,c_39])).

cnf(c_6363,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_6362])).

cnf(c_6374,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(sK1,sK1,sK2,X0_51,sK3)
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1758,c_6363])).

cnf(c_6585,plain,
    ( m1_pre_topc(X0_51,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(sK1,sK1,sK2,X0_51,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6374,c_33,c_34,c_35])).

cnf(c_6586,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(sK1,sK1,sK2,X0_51,sK3)
    | m1_pre_topc(X0_51,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6585])).

cnf(c_6593,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1746,c_6586])).

cnf(c_7,plain,
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
    inference(cnf_transformation,[],[f64])).

cnf(c_1136,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X2_51,X0_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X0_51)
    | ~ v1_funct_1(X0_52)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_52,X2_51) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1737,plain,
    ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_52,X2_51)
    | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1136])).

cnf(c_3933,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1755,c_1737])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1137,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1736,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1137])).

cnf(c_2568,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1758,c_1736])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1138,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | v2_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1735,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1138])).

cnf(c_2878,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1758,c_1735])).

cnf(c_4626,plain,
    ( m1_pre_topc(X0_51,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3933,c_33,c_34,c_35,c_36,c_38,c_39,c_2568,c_2878])).

cnf(c_4627,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51)
    | m1_pre_topc(X0_51,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4626])).

cnf(c_4634,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1746,c_4627])).

cnf(c_4712,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4634,c_35,c_2568])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1132,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1741,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X3_51,X2_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1132])).

cnf(c_3996,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1755,c_1741])).

cnf(c_4699,plain,
    ( v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3996,c_33,c_34,c_35,c_38,c_39])).

cnf(c_4700,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4699])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1133,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),u1_struct_0(X3_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1740,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),u1_struct_0(X3_51),u1_struct_0(X1_51)) = iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X3_51,X2_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1133])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f77])).

cnf(c_1123,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,k3_tmap_1(X2_51,X1_51,X0_51,X0_51,X0_52))
    | ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1750,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,k3_tmap_1(X2_51,X1_51,X0_51,X0_51,X0_52)) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1123])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1134,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_pre_topc(X3_51,X2_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | m1_subset_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1739,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_pre_topc(X3_51,X2_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51)))) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1134])).

cnf(c_4,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1139,plain,
    ( ~ r2_funct_2(X0_52,X1_52,X2_52,X3_52)
    | ~ v1_funct_2(X2_52,X0_52,X1_52)
    | ~ v1_funct_2(X3_52,X0_52,X1_52)
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X2_52)
    | ~ v1_funct_1(X3_52)
    | X3_52 = X2_52 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1734,plain,
    ( X0_52 = X1_52
    | r2_funct_2(X2_52,X3_52,X1_52,X0_52) != iProver_top
    | v1_funct_2(X1_52,X2_52,X3_52) != iProver_top
    | v1_funct_2(X0_52,X2_52,X3_52) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(c_3601,plain,
    ( sK3 = X0_52
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1755,c_1734])).

cnf(c_3705,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | sK3 = X0_52
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3601,c_38,c_39])).

cnf(c_3706,plain,
    ( sK3 = X0_52
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_3705])).

cnf(c_4377,plain,
    ( k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X1_51),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_51),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_3706])).

cnf(c_4851,plain,
    ( v2_pre_topc(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_51),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X1_51),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top
    | k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52) = sK3
    | l1_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4377,c_33,c_34,c_35])).

cnf(c_4852,plain,
    ( k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X1_51),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_51),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4851])).

cnf(c_4867,plain,
    ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
    | v1_funct_2(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1750,c_4852])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4872,plain,
    ( v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3)) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v1_funct_2(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4867,c_33,c_34,c_35,c_36,c_38,c_39,c_40])).

cnf(c_4873,plain,
    ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
    | v1_funct_2(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4872])).

cnf(c_4885,plain,
    ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1740,c_4873])).

cnf(c_5066,plain,
    ( v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3)) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
    | v2_struct_0(X0_51) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4885,c_33,c_34,c_35,c_38,c_39,c_40])).

cnf(c_5067,plain,
    ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5066])).

cnf(c_5078,plain,
    ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_4700,c_5067])).

cnf(c_5088,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1758,c_5078])).

cnf(c_37,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5080,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5078])).

cnf(c_5135,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5088,c_33,c_34,c_35,c_37,c_5080])).

cnf(c_6594,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6593,c_4712,c_5135])).

cnf(c_6597,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6594,c_35,c_2568])).

cnf(c_18,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1125,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52)
    | ~ v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
    | r2_hidden(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X0_51))
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1748,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
    | r2_hidden(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X0_51)) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_6602,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6597,c_1748])).

cnf(c_2529,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_2534,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2529])).

cnf(c_7351,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6602,c_33,c_34,c_35,c_36,c_38,c_39,c_40,c_2534,c_2568,c_2878])).

cnf(c_7352,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_7351])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1121,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_subset_1(X0_52,u1_struct_0(X1_51))
    | ~ r2_hidden(X0_52,u1_struct_0(X0_51))
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | k1_funct_1(k4_tmap_1(X1_51,X0_51),X0_52) = X0_52 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1752,plain,
    ( k1_funct_1(k4_tmap_1(X0_51,X1_51),X0_52) = X0_52
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | r2_hidden(X0_52,u1_struct_0(X1_51)) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1121])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1128,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | m1_subset_1(u1_struct_0(X0_51),k1_zfmisc_1(u1_struct_0(X1_51)))
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1745,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_subset_1(u1_struct_0(X0_51),k1_zfmisc_1(u1_struct_0(X1_51))) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1128])).

cnf(c_1,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1142,plain,
    ( m1_subset_1(X0_52,X1_52)
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(X1_52))
    | ~ r2_hidden(X0_52,X2_52) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1731,plain,
    ( m1_subset_1(X0_52,X1_52) = iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(X1_52)) != iProver_top
    | r2_hidden(X0_52,X2_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1142])).

cnf(c_2869,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X1_51)) = iProver_top
    | r2_hidden(X0_52,u1_struct_0(X0_51)) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_1731])).

cnf(c_3853,plain,
    ( k1_funct_1(k4_tmap_1(X0_51,X1_51),X0_52) = X0_52
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | r2_hidden(X0_52,u1_struct_0(X1_51)) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1752,c_2869])).

cnf(c_7362,plain,
    ( k1_funct_1(k4_tmap_1(X0_51,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_7352,c_3853])).

cnf(c_22464,plain,
    ( v2_struct_0(X0_51) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | k1_funct_1(k4_tmap_1(X0_51,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7362,c_36])).

cnf(c_22465,plain,
    ( k1_funct_1(k4_tmap_1(X0_51,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_22464])).

cnf(c_22478,plain,
    ( k1_funct_1(k4_tmap_1(X0_51,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_22465])).

cnf(c_22560,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_22478])).

cnf(c_7360,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_7352,c_2869])).

cnf(c_24,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,u1_struct_0(sK2))
    | k1_funct_1(sK3,X0) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1119,negated_conjecture,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK1))
    | ~ r2_hidden(X0_52,u1_struct_0(sK2))
    | k1_funct_1(sK3,X0_52) = X0_52 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1754,plain,
    ( k1_funct_1(sK3,X0_52) = X0_52
    | m1_subset_1(X0_52,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1119])).

cnf(c_16198,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_7360,c_1754])).

cnf(c_16581,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16198,c_35,c_37,c_7352])).

cnf(c_16582,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_16581])).

cnf(c_16591,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_16582])).

cnf(c_23,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1145,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_1168,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_3,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1140,plain,
    ( r2_funct_2(X0_52,X1_52,X2_52,X2_52)
    | ~ v1_funct_2(X2_52,X0_52,X1_52)
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X2_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2257,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_2418,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_2429,plain,
    ( u1_struct_0(X0_51) = u1_struct_0(X0_51) ),
    inference(instantiation,[status(thm)],[c_1145])).

cnf(c_2676,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2429])).

cnf(c_3715,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_3706])).

cnf(c_3734,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3715,c_33,c_34,c_35,c_37])).

cnf(c_13,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1130,plain,
    ( v1_funct_2(k4_tmap_1(X0_51,X1_51),u1_struct_0(X1_51),u1_struct_0(X0_51))
    | ~ m1_pre_topc(X1_51,X0_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v2_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2540,plain,
    ( v1_funct_2(k4_tmap_1(sK1,X0_51),u1_struct_0(X0_51),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_51,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1130])).

cnf(c_4307,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2540])).

cnf(c_4310,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4307])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1129,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | v2_struct_0(X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | v1_funct_1(k4_tmap_1(X1_51,X0_51)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_4742,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_4743,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4742])).

cnf(c_1155,plain,
    ( ~ r2_funct_2(X0_52,X1_52,X2_52,X3_52)
    | r2_funct_2(X4_52,X5_52,X6_52,X7_52)
    | X4_52 != X0_52
    | X5_52 != X1_52
    | X6_52 != X2_52
    | X7_52 != X3_52 ),
    theory(equality)).

cnf(c_2378,plain,
    ( r2_funct_2(X0_52,X1_52,X2_52,X3_52)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | X1_52 != u1_struct_0(sK1)
    | X0_52 != u1_struct_0(sK2)
    | X2_52 != sK3
    | X3_52 != sK3 ),
    inference(instantiation,[status(thm)],[c_1155])).

cnf(c_2639,plain,
    ( r2_funct_2(X0_52,u1_struct_0(sK1),X1_52,X2_52)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | X0_52 != u1_struct_0(sK2)
    | X1_52 != sK3
    | X2_52 != sK3
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2378])).

cnf(c_3665,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,X1_52)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | X0_52 != sK3
    | X1_52 != sK3
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2639])).

cnf(c_6257,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | k4_tmap_1(sK1,sK2) != sK3
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3665])).

cnf(c_17118,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16591,c_33,c_34,c_35,c_37,c_27,c_26,c_25,c_23,c_1168,c_2257,c_2418,c_2676,c_3734,c_4310,c_4743,c_6257])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_1124,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52)
    | ~ v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
    | m1_subset_1(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X2_51))
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1749,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_subset_1(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X2_51)) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1124])).

cnf(c_6601,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6597,c_1749])).

cnf(c_6930,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6601,c_33,c_34,c_35,c_36,c_38,c_39,c_40,c_2534,c_2568,c_2878])).

cnf(c_6931,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_6930])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1141,plain,
    ( ~ v1_funct_2(X0_52,X1_52,X2_52)
    | ~ m1_subset_1(X3_52,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | ~ v1_funct_1(X0_52)
    | v1_xboole_0(X1_52)
    | k3_funct_2(X1_52,X2_52,X0_52,X3_52) = k1_funct_1(X0_52,X3_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1732,plain,
    ( k3_funct_2(X0_52,X1_52,X2_52,X3_52) = k1_funct_1(X2_52,X3_52)
    | v1_funct_2(X2_52,X0_52,X1_52) != iProver_top
    | m1_subset_1(X3_52,X0_52) != iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X2_52) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1141])).

cnf(c_3081,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1755,c_1732])).

cnf(c_3583,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3081,c_38,c_39])).

cnf(c_3584,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3583])).

cnf(c_6940,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6931,c_3584])).

cnf(c_7079,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_6940])).

cnf(c_7136,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7079,c_33,c_34,c_35,c_37,c_27,c_26,c_25,c_23,c_1168,c_2257,c_2418,c_2676,c_3734,c_4310,c_4743,c_6257])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1143,plain,
    ( ~ r2_hidden(X0_52,X1_52)
    | ~ v1_xboole_0(X1_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1730,plain,
    ( r2_hidden(X0_52,X1_52) != iProver_top
    | v1_xboole_0(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1143])).

cnf(c_7361,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7352,c_1730])).

cnf(c_7629,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_7361])).

cnf(c_7682,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7629,c_33,c_34,c_35,c_37,c_27,c_26,c_25,c_23,c_1168,c_2257,c_2418,c_2676,c_3734,c_4310,c_4743,c_6257])).

cnf(c_7687,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_7136,c_7682])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_1126,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52)
    | ~ v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X0_51,X2_51)
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | v2_struct_0(X2_51)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(X2_51)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(X2_51)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52)
    | k3_funct_2(u1_struct_0(X2_51),u1_struct_0(X1_51),X0_52,sK0(X1_51,X2_51,X0_51,X0_52,X1_52)) != k1_funct_1(X1_52,sK0(X1_51,X2_51,X0_51,X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1747,plain,
    ( k3_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,sK0(X1_51,X0_51,X2_51,X0_52,X1_52)) != k1_funct_1(X1_52,sK0(X1_51,X0_51,X2_51,X0_52,X1_52))
    | r2_funct_2(u1_struct_0(X2_51),u1_struct_0(X1_51),k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X2_51,X0_51) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1126])).

cnf(c_8599,plain,
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
    inference(superposition,[status(thm)],[c_7687,c_1747])).

cnf(c_8600,plain,
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
    inference(light_normalisation,[status(thm)],[c_8599,c_6597])).

cnf(c_2574,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2568])).

cnf(c_2886,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2878])).

cnf(c_3736,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | k4_tmap_1(sK1,sK2) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3734])).

cnf(c_8601,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8600])).

cnf(c_8831,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_13383,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8600,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25,c_23,c_1168,c_2257,c_2418,c_2529,c_2574,c_2676,c_2886,c_3736,c_4307,c_4742,c_6257,c_8601,c_8831])).

cnf(c_17121,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_17118,c_13383])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22560,c_17121,c_6257,c_4743,c_4310,c_3734,c_2676,c_2418,c_2257,c_1168,c_23,c_25,c_26,c_27,c_37,c_35,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:38:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.00/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.00/1.99  
% 11.00/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.00/1.99  
% 11.00/1.99  ------  iProver source info
% 11.00/1.99  
% 11.00/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.00/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.00/1.99  git: non_committed_changes: false
% 11.00/1.99  git: last_make_outside_of_git: false
% 11.00/1.99  
% 11.00/1.99  ------ 
% 11.00/1.99  
% 11.00/1.99  ------ Input Options
% 11.00/1.99  
% 11.00/1.99  --out_options                           all
% 11.00/1.99  --tptp_safe_out                         true
% 11.00/1.99  --problem_path                          ""
% 11.00/1.99  --include_path                          ""
% 11.00/1.99  --clausifier                            res/vclausify_rel
% 11.00/1.99  --clausifier_options                    --mode clausify
% 11.00/1.99  --stdin                                 false
% 11.00/1.99  --stats_out                             all
% 11.00/1.99  
% 11.00/1.99  ------ General Options
% 11.00/1.99  
% 11.00/1.99  --fof                                   false
% 11.00/1.99  --time_out_real                         305.
% 11.00/1.99  --time_out_virtual                      -1.
% 11.00/1.99  --symbol_type_check                     false
% 11.00/1.99  --clausify_out                          false
% 11.00/1.99  --sig_cnt_out                           false
% 11.00/1.99  --trig_cnt_out                          false
% 11.00/1.99  --trig_cnt_out_tolerance                1.
% 11.00/1.99  --trig_cnt_out_sk_spl                   false
% 11.00/1.99  --abstr_cl_out                          false
% 11.00/1.99  
% 11.00/1.99  ------ Global Options
% 11.00/1.99  
% 11.00/1.99  --schedule                              default
% 11.00/1.99  --add_important_lit                     false
% 11.00/1.99  --prop_solver_per_cl                    1000
% 11.00/1.99  --min_unsat_core                        false
% 11.00/1.99  --soft_assumptions                      false
% 11.00/1.99  --soft_lemma_size                       3
% 11.00/1.99  --prop_impl_unit_size                   0
% 11.00/1.99  --prop_impl_unit                        []
% 11.00/1.99  --share_sel_clauses                     true
% 11.00/1.99  --reset_solvers                         false
% 11.00/1.99  --bc_imp_inh                            [conj_cone]
% 11.00/1.99  --conj_cone_tolerance                   3.
% 11.00/1.99  --extra_neg_conj                        none
% 11.00/1.99  --large_theory_mode                     true
% 11.00/1.99  --prolific_symb_bound                   200
% 11.00/1.99  --lt_threshold                          2000
% 11.00/1.99  --clause_weak_htbl                      true
% 11.00/1.99  --gc_record_bc_elim                     false
% 11.00/1.99  
% 11.00/1.99  ------ Preprocessing Options
% 11.00/1.99  
% 11.00/1.99  --preprocessing_flag                    true
% 11.00/1.99  --time_out_prep_mult                    0.1
% 11.00/1.99  --splitting_mode                        input
% 11.00/1.99  --splitting_grd                         true
% 11.00/1.99  --splitting_cvd                         false
% 11.00/1.99  --splitting_cvd_svl                     false
% 11.00/1.99  --splitting_nvd                         32
% 11.00/1.99  --sub_typing                            true
% 11.00/1.99  --prep_gs_sim                           true
% 11.00/1.99  --prep_unflatten                        true
% 11.00/1.99  --prep_res_sim                          true
% 11.00/1.99  --prep_upred                            true
% 11.00/1.99  --prep_sem_filter                       exhaustive
% 11.00/1.99  --prep_sem_filter_out                   false
% 11.00/1.99  --pred_elim                             true
% 11.00/1.99  --res_sim_input                         true
% 11.00/1.99  --eq_ax_congr_red                       true
% 11.00/1.99  --pure_diseq_elim                       true
% 11.00/1.99  --brand_transform                       false
% 11.00/1.99  --non_eq_to_eq                          false
% 11.00/1.99  --prep_def_merge                        true
% 11.00/1.99  --prep_def_merge_prop_impl              false
% 11.00/1.99  --prep_def_merge_mbd                    true
% 11.00/1.99  --prep_def_merge_tr_red                 false
% 11.00/1.99  --prep_def_merge_tr_cl                  false
% 11.00/1.99  --smt_preprocessing                     true
% 11.00/1.99  --smt_ac_axioms                         fast
% 11.00/1.99  --preprocessed_out                      false
% 11.00/1.99  --preprocessed_stats                    false
% 11.00/1.99  
% 11.00/1.99  ------ Abstraction refinement Options
% 11.00/1.99  
% 11.00/1.99  --abstr_ref                             []
% 11.00/1.99  --abstr_ref_prep                        false
% 11.00/1.99  --abstr_ref_until_sat                   false
% 11.00/1.99  --abstr_ref_sig_restrict                funpre
% 11.00/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.00/1.99  --abstr_ref_under                       []
% 11.00/1.99  
% 11.00/1.99  ------ SAT Options
% 11.00/1.99  
% 11.00/1.99  --sat_mode                              false
% 11.00/1.99  --sat_fm_restart_options                ""
% 11.00/1.99  --sat_gr_def                            false
% 11.00/1.99  --sat_epr_types                         true
% 11.00/1.99  --sat_non_cyclic_types                  false
% 11.00/1.99  --sat_finite_models                     false
% 11.00/1.99  --sat_fm_lemmas                         false
% 11.00/1.99  --sat_fm_prep                           false
% 11.00/1.99  --sat_fm_uc_incr                        true
% 11.00/1.99  --sat_out_model                         small
% 11.00/1.99  --sat_out_clauses                       false
% 11.00/1.99  
% 11.00/1.99  ------ QBF Options
% 11.00/1.99  
% 11.00/1.99  --qbf_mode                              false
% 11.00/1.99  --qbf_elim_univ                         false
% 11.00/1.99  --qbf_dom_inst                          none
% 11.00/1.99  --qbf_dom_pre_inst                      false
% 11.00/1.99  --qbf_sk_in                             false
% 11.00/1.99  --qbf_pred_elim                         true
% 11.00/1.99  --qbf_split                             512
% 11.00/1.99  
% 11.00/1.99  ------ BMC1 Options
% 11.00/1.99  
% 11.00/1.99  --bmc1_incremental                      false
% 11.00/1.99  --bmc1_axioms                           reachable_all
% 11.00/1.99  --bmc1_min_bound                        0
% 11.00/1.99  --bmc1_max_bound                        -1
% 11.00/1.99  --bmc1_max_bound_default                -1
% 11.00/1.99  --bmc1_symbol_reachability              true
% 11.00/1.99  --bmc1_property_lemmas                  false
% 11.00/1.99  --bmc1_k_induction                      false
% 11.00/1.99  --bmc1_non_equiv_states                 false
% 11.00/1.99  --bmc1_deadlock                         false
% 11.00/1.99  --bmc1_ucm                              false
% 11.00/1.99  --bmc1_add_unsat_core                   none
% 11.00/1.99  --bmc1_unsat_core_children              false
% 11.00/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.00/1.99  --bmc1_out_stat                         full
% 11.00/1.99  --bmc1_ground_init                      false
% 11.00/1.99  --bmc1_pre_inst_next_state              false
% 11.00/1.99  --bmc1_pre_inst_state                   false
% 11.00/1.99  --bmc1_pre_inst_reach_state             false
% 11.00/1.99  --bmc1_out_unsat_core                   false
% 11.00/1.99  --bmc1_aig_witness_out                  false
% 11.00/1.99  --bmc1_verbose                          false
% 11.00/1.99  --bmc1_dump_clauses_tptp                false
% 11.00/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.00/1.99  --bmc1_dump_file                        -
% 11.00/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.00/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.00/1.99  --bmc1_ucm_extend_mode                  1
% 11.00/1.99  --bmc1_ucm_init_mode                    2
% 11.00/1.99  --bmc1_ucm_cone_mode                    none
% 11.00/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.00/1.99  --bmc1_ucm_relax_model                  4
% 11.00/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.00/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.00/1.99  --bmc1_ucm_layered_model                none
% 11.00/1.99  --bmc1_ucm_max_lemma_size               10
% 11.00/1.99  
% 11.00/1.99  ------ AIG Options
% 11.00/1.99  
% 11.00/1.99  --aig_mode                              false
% 11.00/1.99  
% 11.00/1.99  ------ Instantiation Options
% 11.00/1.99  
% 11.00/1.99  --instantiation_flag                    true
% 11.00/1.99  --inst_sos_flag                         false
% 11.00/1.99  --inst_sos_phase                        true
% 11.00/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.00/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.00/1.99  --inst_lit_sel_side                     num_symb
% 11.00/1.99  --inst_solver_per_active                1400
% 11.00/1.99  --inst_solver_calls_frac                1.
% 11.00/1.99  --inst_passive_queue_type               priority_queues
% 11.00/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.00/1.99  --inst_passive_queues_freq              [25;2]
% 11.00/1.99  --inst_dismatching                      true
% 11.00/1.99  --inst_eager_unprocessed_to_passive     true
% 11.00/1.99  --inst_prop_sim_given                   true
% 11.00/1.99  --inst_prop_sim_new                     false
% 11.00/1.99  --inst_subs_new                         false
% 11.00/1.99  --inst_eq_res_simp                      false
% 11.00/1.99  --inst_subs_given                       false
% 11.00/1.99  --inst_orphan_elimination               true
% 11.00/1.99  --inst_learning_loop_flag               true
% 11.00/1.99  --inst_learning_start                   3000
% 11.00/1.99  --inst_learning_factor                  2
% 11.00/1.99  --inst_start_prop_sim_after_learn       3
% 11.00/1.99  --inst_sel_renew                        solver
% 11.00/1.99  --inst_lit_activity_flag                true
% 11.00/1.99  --inst_restr_to_given                   false
% 11.00/1.99  --inst_activity_threshold               500
% 11.00/1.99  --inst_out_proof                        true
% 11.00/1.99  
% 11.00/1.99  ------ Resolution Options
% 11.00/1.99  
% 11.00/1.99  --resolution_flag                       true
% 11.00/1.99  --res_lit_sel                           adaptive
% 11.00/1.99  --res_lit_sel_side                      none
% 11.00/1.99  --res_ordering                          kbo
% 11.00/1.99  --res_to_prop_solver                    active
% 11.00/1.99  --res_prop_simpl_new                    false
% 11.00/1.99  --res_prop_simpl_given                  true
% 11.00/1.99  --res_passive_queue_type                priority_queues
% 11.00/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.00/1.99  --res_passive_queues_freq               [15;5]
% 11.00/1.99  --res_forward_subs                      full
% 11.00/1.99  --res_backward_subs                     full
% 11.00/1.99  --res_forward_subs_resolution           true
% 11.00/1.99  --res_backward_subs_resolution          true
% 11.00/1.99  --res_orphan_elimination                true
% 11.00/1.99  --res_time_limit                        2.
% 11.00/1.99  --res_out_proof                         true
% 11.00/1.99  
% 11.00/1.99  ------ Superposition Options
% 11.00/1.99  
% 11.00/1.99  --superposition_flag                    true
% 11.00/1.99  --sup_passive_queue_type                priority_queues
% 11.00/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.00/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.00/1.99  --demod_completeness_check              fast
% 11.00/1.99  --demod_use_ground                      true
% 11.00/1.99  --sup_to_prop_solver                    passive
% 11.00/1.99  --sup_prop_simpl_new                    true
% 11.00/1.99  --sup_prop_simpl_given                  true
% 11.00/1.99  --sup_fun_splitting                     false
% 11.00/1.99  --sup_smt_interval                      50000
% 11.00/1.99  
% 11.00/1.99  ------ Superposition Simplification Setup
% 11.00/1.99  
% 11.00/1.99  --sup_indices_passive                   []
% 11.00/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.00/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.00/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.00/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.00/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.00/1.99  --sup_full_bw                           [BwDemod]
% 11.00/1.99  --sup_immed_triv                        [TrivRules]
% 11.00/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.00/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.00/1.99  --sup_immed_bw_main                     []
% 11.00/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.00/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.00/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.00/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.00/1.99  
% 11.00/1.99  ------ Combination Options
% 11.00/1.99  
% 11.00/1.99  --comb_res_mult                         3
% 11.00/1.99  --comb_sup_mult                         2
% 11.00/1.99  --comb_inst_mult                        10
% 11.00/1.99  
% 11.00/1.99  ------ Debug Options
% 11.00/1.99  
% 11.00/1.99  --dbg_backtrace                         false
% 11.00/1.99  --dbg_dump_prop_clauses                 false
% 11.00/1.99  --dbg_dump_prop_clauses_file            -
% 11.00/1.99  --dbg_out_stat                          false
% 11.00/1.99  ------ Parsing...
% 11.00/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.00/1.99  
% 11.00/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.00/1.99  
% 11.00/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.00/1.99  
% 11.00/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.00/1.99  ------ Proving...
% 11.00/1.99  ------ Problem Properties 
% 11.00/1.99  
% 11.00/1.99  
% 11.00/1.99  clauses                                 33
% 11.00/1.99  conjectures                             10
% 11.00/1.99  EPR                                     11
% 11.00/1.99  Horn                                    19
% 11.00/1.99  unary                                   9
% 11.00/1.99  binary                                  2
% 11.00/1.99  lits                                    195
% 11.00/1.99  lits eq                                 7
% 11.00/1.99  fd_pure                                 0
% 11.00/1.99  fd_pseudo                               0
% 11.00/1.99  fd_cond                                 0
% 11.00/1.99  fd_pseudo_cond                          1
% 11.00/1.99  AC symbols                              0
% 11.00/1.99  
% 11.00/1.99  ------ Schedule dynamic 5 is on 
% 11.00/1.99  
% 11.00/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.00/1.99  
% 11.00/1.99  
% 11.00/1.99  ------ 
% 11.00/1.99  Current options:
% 11.00/1.99  ------ 
% 11.00/1.99  
% 11.00/1.99  ------ Input Options
% 11.00/1.99  
% 11.00/1.99  --out_options                           all
% 11.00/1.99  --tptp_safe_out                         true
% 11.00/1.99  --problem_path                          ""
% 11.00/1.99  --include_path                          ""
% 11.00/1.99  --clausifier                            res/vclausify_rel
% 11.00/1.99  --clausifier_options                    --mode clausify
% 11.00/1.99  --stdin                                 false
% 11.00/1.99  --stats_out                             all
% 11.00/1.99  
% 11.00/1.99  ------ General Options
% 11.00/1.99  
% 11.00/1.99  --fof                                   false
% 11.00/1.99  --time_out_real                         305.
% 11.00/1.99  --time_out_virtual                      -1.
% 11.00/1.99  --symbol_type_check                     false
% 11.00/1.99  --clausify_out                          false
% 11.00/1.99  --sig_cnt_out                           false
% 11.00/1.99  --trig_cnt_out                          false
% 11.00/1.99  --trig_cnt_out_tolerance                1.
% 11.00/1.99  --trig_cnt_out_sk_spl                   false
% 11.00/1.99  --abstr_cl_out                          false
% 11.00/1.99  
% 11.00/1.99  ------ Global Options
% 11.00/1.99  
% 11.00/1.99  --schedule                              default
% 11.00/1.99  --add_important_lit                     false
% 11.00/1.99  --prop_solver_per_cl                    1000
% 11.00/1.99  --min_unsat_core                        false
% 11.00/1.99  --soft_assumptions                      false
% 11.00/1.99  --soft_lemma_size                       3
% 11.00/1.99  --prop_impl_unit_size                   0
% 11.00/1.99  --prop_impl_unit                        []
% 11.00/1.99  --share_sel_clauses                     true
% 11.00/1.99  --reset_solvers                         false
% 11.00/1.99  --bc_imp_inh                            [conj_cone]
% 11.00/1.99  --conj_cone_tolerance                   3.
% 11.00/1.99  --extra_neg_conj                        none
% 11.00/1.99  --large_theory_mode                     true
% 11.00/1.99  --prolific_symb_bound                   200
% 11.00/1.99  --lt_threshold                          2000
% 11.00/1.99  --clause_weak_htbl                      true
% 11.00/1.99  --gc_record_bc_elim                     false
% 11.00/1.99  
% 11.00/1.99  ------ Preprocessing Options
% 11.00/1.99  
% 11.00/1.99  --preprocessing_flag                    true
% 11.00/1.99  --time_out_prep_mult                    0.1
% 11.00/1.99  --splitting_mode                        input
% 11.00/1.99  --splitting_grd                         true
% 11.00/1.99  --splitting_cvd                         false
% 11.00/1.99  --splitting_cvd_svl                     false
% 11.00/1.99  --splitting_nvd                         32
% 11.00/1.99  --sub_typing                            true
% 11.00/1.99  --prep_gs_sim                           true
% 11.00/1.99  --prep_unflatten                        true
% 11.00/1.99  --prep_res_sim                          true
% 11.00/1.99  --prep_upred                            true
% 11.00/1.99  --prep_sem_filter                       exhaustive
% 11.00/1.99  --prep_sem_filter_out                   false
% 11.00/1.99  --pred_elim                             true
% 11.00/1.99  --res_sim_input                         true
% 11.00/1.99  --eq_ax_congr_red                       true
% 11.00/1.99  --pure_diseq_elim                       true
% 11.00/1.99  --brand_transform                       false
% 11.00/1.99  --non_eq_to_eq                          false
% 11.00/1.99  --prep_def_merge                        true
% 11.00/1.99  --prep_def_merge_prop_impl              false
% 11.00/1.99  --prep_def_merge_mbd                    true
% 11.00/1.99  --prep_def_merge_tr_red                 false
% 11.00/1.99  --prep_def_merge_tr_cl                  false
% 11.00/1.99  --smt_preprocessing                     true
% 11.00/1.99  --smt_ac_axioms                         fast
% 11.00/1.99  --preprocessed_out                      false
% 11.00/1.99  --preprocessed_stats                    false
% 11.00/1.99  
% 11.00/1.99  ------ Abstraction refinement Options
% 11.00/1.99  
% 11.00/1.99  --abstr_ref                             []
% 11.00/1.99  --abstr_ref_prep                        false
% 11.00/1.99  --abstr_ref_until_sat                   false
% 11.00/1.99  --abstr_ref_sig_restrict                funpre
% 11.00/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.00/1.99  --abstr_ref_under                       []
% 11.00/1.99  
% 11.00/1.99  ------ SAT Options
% 11.00/1.99  
% 11.00/1.99  --sat_mode                              false
% 11.00/1.99  --sat_fm_restart_options                ""
% 11.00/1.99  --sat_gr_def                            false
% 11.00/1.99  --sat_epr_types                         true
% 11.00/1.99  --sat_non_cyclic_types                  false
% 11.00/1.99  --sat_finite_models                     false
% 11.00/1.99  --sat_fm_lemmas                         false
% 11.00/1.99  --sat_fm_prep                           false
% 11.00/1.99  --sat_fm_uc_incr                        true
% 11.00/1.99  --sat_out_model                         small
% 11.00/1.99  --sat_out_clauses                       false
% 11.00/1.99  
% 11.00/1.99  ------ QBF Options
% 11.00/1.99  
% 11.00/1.99  --qbf_mode                              false
% 11.00/1.99  --qbf_elim_univ                         false
% 11.00/1.99  --qbf_dom_inst                          none
% 11.00/1.99  --qbf_dom_pre_inst                      false
% 11.00/1.99  --qbf_sk_in                             false
% 11.00/1.99  --qbf_pred_elim                         true
% 11.00/1.99  --qbf_split                             512
% 11.00/1.99  
% 11.00/1.99  ------ BMC1 Options
% 11.00/1.99  
% 11.00/1.99  --bmc1_incremental                      false
% 11.00/1.99  --bmc1_axioms                           reachable_all
% 11.00/1.99  --bmc1_min_bound                        0
% 11.00/1.99  --bmc1_max_bound                        -1
% 11.00/1.99  --bmc1_max_bound_default                -1
% 11.00/1.99  --bmc1_symbol_reachability              true
% 11.00/1.99  --bmc1_property_lemmas                  false
% 11.00/1.99  --bmc1_k_induction                      false
% 11.00/1.99  --bmc1_non_equiv_states                 false
% 11.00/1.99  --bmc1_deadlock                         false
% 11.00/1.99  --bmc1_ucm                              false
% 11.00/1.99  --bmc1_add_unsat_core                   none
% 11.00/1.99  --bmc1_unsat_core_children              false
% 11.00/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.00/1.99  --bmc1_out_stat                         full
% 11.00/1.99  --bmc1_ground_init                      false
% 11.00/1.99  --bmc1_pre_inst_next_state              false
% 11.00/1.99  --bmc1_pre_inst_state                   false
% 11.00/1.99  --bmc1_pre_inst_reach_state             false
% 11.00/1.99  --bmc1_out_unsat_core                   false
% 11.00/1.99  --bmc1_aig_witness_out                  false
% 11.00/1.99  --bmc1_verbose                          false
% 11.00/1.99  --bmc1_dump_clauses_tptp                false
% 11.00/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.00/1.99  --bmc1_dump_file                        -
% 11.00/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.00/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.00/1.99  --bmc1_ucm_extend_mode                  1
% 11.00/1.99  --bmc1_ucm_init_mode                    2
% 11.00/1.99  --bmc1_ucm_cone_mode                    none
% 11.00/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.00/1.99  --bmc1_ucm_relax_model                  4
% 11.00/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.00/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.00/1.99  --bmc1_ucm_layered_model                none
% 11.00/1.99  --bmc1_ucm_max_lemma_size               10
% 11.00/1.99  
% 11.00/1.99  ------ AIG Options
% 11.00/1.99  
% 11.00/1.99  --aig_mode                              false
% 11.00/1.99  
% 11.00/1.99  ------ Instantiation Options
% 11.00/1.99  
% 11.00/1.99  --instantiation_flag                    true
% 11.00/1.99  --inst_sos_flag                         false
% 11.00/1.99  --inst_sos_phase                        true
% 11.00/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.00/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.00/1.99  --inst_lit_sel_side                     none
% 11.00/1.99  --inst_solver_per_active                1400
% 11.00/1.99  --inst_solver_calls_frac                1.
% 11.00/1.99  --inst_passive_queue_type               priority_queues
% 11.00/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.00/1.99  --inst_passive_queues_freq              [25;2]
% 11.00/1.99  --inst_dismatching                      true
% 11.00/1.99  --inst_eager_unprocessed_to_passive     true
% 11.00/1.99  --inst_prop_sim_given                   true
% 11.00/1.99  --inst_prop_sim_new                     false
% 11.00/1.99  --inst_subs_new                         false
% 11.00/1.99  --inst_eq_res_simp                      false
% 11.00/1.99  --inst_subs_given                       false
% 11.00/1.99  --inst_orphan_elimination               true
% 11.00/1.99  --inst_learning_loop_flag               true
% 11.00/1.99  --inst_learning_start                   3000
% 11.00/1.99  --inst_learning_factor                  2
% 11.00/1.99  --inst_start_prop_sim_after_learn       3
% 11.00/1.99  --inst_sel_renew                        solver
% 11.00/1.99  --inst_lit_activity_flag                true
% 11.00/1.99  --inst_restr_to_given                   false
% 11.00/1.99  --inst_activity_threshold               500
% 11.00/1.99  --inst_out_proof                        true
% 11.00/1.99  
% 11.00/1.99  ------ Resolution Options
% 11.00/1.99  
% 11.00/1.99  --resolution_flag                       false
% 11.00/1.99  --res_lit_sel                           adaptive
% 11.00/1.99  --res_lit_sel_side                      none
% 11.00/1.99  --res_ordering                          kbo
% 11.00/1.99  --res_to_prop_solver                    active
% 11.00/1.99  --res_prop_simpl_new                    false
% 11.00/1.99  --res_prop_simpl_given                  true
% 11.00/1.99  --res_passive_queue_type                priority_queues
% 11.00/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.00/1.99  --res_passive_queues_freq               [15;5]
% 11.00/1.99  --res_forward_subs                      full
% 11.00/1.99  --res_backward_subs                     full
% 11.00/1.99  --res_forward_subs_resolution           true
% 11.00/1.99  --res_backward_subs_resolution          true
% 11.00/1.99  --res_orphan_elimination                true
% 11.00/1.99  --res_time_limit                        2.
% 11.00/1.99  --res_out_proof                         true
% 11.00/1.99  
% 11.00/1.99  ------ Superposition Options
% 11.00/1.99  
% 11.00/1.99  --superposition_flag                    true
% 11.00/1.99  --sup_passive_queue_type                priority_queues
% 11.00/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.00/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.00/1.99  --demod_completeness_check              fast
% 11.00/1.99  --demod_use_ground                      true
% 11.00/1.99  --sup_to_prop_solver                    passive
% 11.00/1.99  --sup_prop_simpl_new                    true
% 11.00/1.99  --sup_prop_simpl_given                  true
% 11.00/1.99  --sup_fun_splitting                     false
% 11.00/1.99  --sup_smt_interval                      50000
% 11.00/1.99  
% 11.00/1.99  ------ Superposition Simplification Setup
% 11.00/1.99  
% 11.00/1.99  --sup_indices_passive                   []
% 11.00/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.00/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.00/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.00/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.00/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.00/1.99  --sup_full_bw                           [BwDemod]
% 11.00/1.99  --sup_immed_triv                        [TrivRules]
% 11.00/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.00/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.00/1.99  --sup_immed_bw_main                     []
% 11.00/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.00/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.00/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.00/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.00/1.99  
% 11.00/1.99  ------ Combination Options
% 11.00/1.99  
% 11.00/1.99  --comb_res_mult                         3
% 11.00/1.99  --comb_sup_mult                         2
% 11.00/1.99  --comb_inst_mult                        10
% 11.00/1.99  
% 11.00/1.99  ------ Debug Options
% 11.00/1.99  
% 11.00/1.99  --dbg_backtrace                         false
% 11.00/1.99  --dbg_dump_prop_clauses                 false
% 11.00/1.99  --dbg_dump_prop_clauses_file            -
% 11.00/1.99  --dbg_out_stat                          false
% 11.00/1.99  
% 11.00/1.99  
% 11.00/1.99  
% 11.00/1.99  
% 11.00/1.99  ------ Proving...
% 11.00/1.99  
% 11.00/1.99  
% 11.00/1.99  % SZS status Theorem for theBenchmark.p
% 11.00/1.99  
% 11.00/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.00/1.99  
% 11.00/1.99  fof(f10,axiom,(
% 11.00/1.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f36,plain,(
% 11.00/1.99    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.00/1.99    inference(ennf_transformation,[],[f10])).
% 11.00/1.99  
% 11.00/1.99  fof(f37,plain,(
% 11.00/1.99    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.00/1.99    inference(flattening,[],[f36])).
% 11.00/1.99  
% 11.00/1.99  fof(f71,plain,(
% 11.00/1.99    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f37])).
% 11.00/1.99  
% 11.00/1.99  fof(f12,axiom,(
% 11.00/1.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f39,plain,(
% 11.00/1.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 11.00/1.99    inference(ennf_transformation,[],[f12])).
% 11.00/1.99  
% 11.00/1.99  fof(f73,plain,(
% 11.00/1.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f39])).
% 11.00/1.99  
% 11.00/1.99  fof(f17,conjecture,(
% 11.00/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f18,negated_conjecture,(
% 11.00/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 11.00/1.99    inference(negated_conjecture,[],[f17])).
% 11.00/1.99  
% 11.00/1.99  fof(f48,plain,(
% 11.00/1.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.00/1.99    inference(ennf_transformation,[],[f18])).
% 11.00/1.99  
% 11.00/1.99  fof(f49,plain,(
% 11.00/1.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.00/1.99    inference(flattening,[],[f48])).
% 11.00/1.99  
% 11.00/1.99  fof(f55,plain,(
% 11.00/1.99    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 11.00/1.99    introduced(choice_axiom,[])).
% 11.00/1.99  
% 11.00/1.99  fof(f54,plain,(
% 11.00/1.99    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 11.00/1.99    introduced(choice_axiom,[])).
% 11.00/1.99  
% 11.00/1.99  fof(f53,plain,(
% 11.00/1.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 11.00/1.99    introduced(choice_axiom,[])).
% 11.00/1.99  
% 11.00/1.99  fof(f56,plain,(
% 11.00/1.99    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 11.00/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f49,f55,f54,f53])).
% 11.00/1.99  
% 11.00/1.99  fof(f84,plain,(
% 11.00/1.99    m1_pre_topc(sK2,sK1)),
% 11.00/1.99    inference(cnf_transformation,[],[f56])).
% 11.00/1.99  
% 11.00/1.99  fof(f87,plain,(
% 11.00/1.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 11.00/1.99    inference(cnf_transformation,[],[f56])).
% 11.00/1.99  
% 11.00/1.99  fof(f8,axiom,(
% 11.00/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f32,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.00/1.99    inference(ennf_transformation,[],[f8])).
% 11.00/1.99  
% 11.00/1.99  fof(f33,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.00/1.99    inference(flattening,[],[f32])).
% 11.00/1.99  
% 11.00/1.99  fof(f65,plain,(
% 11.00/1.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f33])).
% 11.00/1.99  
% 11.00/1.99  fof(f15,axiom,(
% 11.00/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f44,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.00/1.99    inference(ennf_transformation,[],[f15])).
% 11.00/1.99  
% 11.00/1.99  fof(f45,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.00/1.99    inference(flattening,[],[f44])).
% 11.00/1.99  
% 11.00/1.99  fof(f78,plain,(
% 11.00/1.99    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f45])).
% 11.00/1.99  
% 11.00/1.99  fof(f80,plain,(
% 11.00/1.99    ~v2_struct_0(sK1)),
% 11.00/1.99    inference(cnf_transformation,[],[f56])).
% 11.00/1.99  
% 11.00/1.99  fof(f81,plain,(
% 11.00/1.99    v2_pre_topc(sK1)),
% 11.00/1.99    inference(cnf_transformation,[],[f56])).
% 11.00/1.99  
% 11.00/1.99  fof(f82,plain,(
% 11.00/1.99    l1_pre_topc(sK1)),
% 11.00/1.99    inference(cnf_transformation,[],[f56])).
% 11.00/1.99  
% 11.00/1.99  fof(f85,plain,(
% 11.00/1.99    v1_funct_1(sK3)),
% 11.00/1.99    inference(cnf_transformation,[],[f56])).
% 11.00/1.99  
% 11.00/1.99  fof(f86,plain,(
% 11.00/1.99    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 11.00/1.99    inference(cnf_transformation,[],[f56])).
% 11.00/1.99  
% 11.00/1.99  fof(f7,axiom,(
% 11.00/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f30,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.00/1.99    inference(ennf_transformation,[],[f7])).
% 11.00/1.99  
% 11.00/1.99  fof(f31,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.00/1.99    inference(flattening,[],[f30])).
% 11.00/1.99  
% 11.00/1.99  fof(f64,plain,(
% 11.00/1.99    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f31])).
% 11.00/1.99  
% 11.00/1.99  fof(f83,plain,(
% 11.00/1.99    ~v2_struct_0(sK2)),
% 11.00/1.99    inference(cnf_transformation,[],[f56])).
% 11.00/1.99  
% 11.00/1.99  fof(f6,axiom,(
% 11.00/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f29,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.00/1.99    inference(ennf_transformation,[],[f6])).
% 11.00/1.99  
% 11.00/1.99  fof(f63,plain,(
% 11.00/1.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f29])).
% 11.00/1.99  
% 11.00/1.99  fof(f5,axiom,(
% 11.00/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f27,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.00/1.99    inference(ennf_transformation,[],[f5])).
% 11.00/1.99  
% 11.00/1.99  fof(f28,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.00/1.99    inference(flattening,[],[f27])).
% 11.00/1.99  
% 11.00/1.99  fof(f62,plain,(
% 11.00/1.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f28])).
% 11.00/1.99  
% 11.00/1.99  fof(f9,axiom,(
% 11.00/1.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f34,plain,(
% 11.00/1.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.00/1.99    inference(ennf_transformation,[],[f9])).
% 11.00/1.99  
% 11.00/1.99  fof(f35,plain,(
% 11.00/1.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.00/1.99    inference(flattening,[],[f34])).
% 11.00/1.99  
% 11.00/1.99  fof(f66,plain,(
% 11.00/1.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f35])).
% 11.00/1.99  
% 11.00/1.99  fof(f67,plain,(
% 11.00/1.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f35])).
% 11.00/1.99  
% 11.00/1.99  fof(f14,axiom,(
% 11.00/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f42,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.00/1.99    inference(ennf_transformation,[],[f14])).
% 11.00/1.99  
% 11.00/1.99  fof(f43,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.00/1.99    inference(flattening,[],[f42])).
% 11.00/1.99  
% 11.00/1.99  fof(f77,plain,(
% 11.00/1.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f43])).
% 11.00/1.99  
% 11.00/1.99  fof(f68,plain,(
% 11.00/1.99    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f35])).
% 11.00/1.99  
% 11.00/1.99  fof(f4,axiom,(
% 11.00/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f25,plain,(
% 11.00/1.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.00/1.99    inference(ennf_transformation,[],[f4])).
% 11.00/1.99  
% 11.00/1.99  fof(f26,plain,(
% 11.00/1.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.00/1.99    inference(flattening,[],[f25])).
% 11.00/1.99  
% 11.00/1.99  fof(f50,plain,(
% 11.00/1.99    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.00/1.99    inference(nnf_transformation,[],[f26])).
% 11.00/1.99  
% 11.00/1.99  fof(f60,plain,(
% 11.00/1.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f50])).
% 11.00/1.99  
% 11.00/1.99  fof(f13,axiom,(
% 11.00/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f40,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.00/1.99    inference(ennf_transformation,[],[f13])).
% 11.00/1.99  
% 11.00/1.99  fof(f41,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.00/1.99    inference(flattening,[],[f40])).
% 11.00/1.99  
% 11.00/1.99  fof(f51,plain,(
% 11.00/1.99    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) => (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))))),
% 11.00/1.99    introduced(choice_axiom,[])).
% 11.00/1.99  
% 11.00/1.99  fof(f52,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.00/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f51])).
% 11.00/1.99  
% 11.00/1.99  fof(f75,plain,(
% 11.00/1.99    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f52])).
% 11.00/1.99  
% 11.00/1.99  fof(f16,axiom,(
% 11.00/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f46,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.00/1.99    inference(ennf_transformation,[],[f16])).
% 11.00/1.99  
% 11.00/1.99  fof(f47,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.00/1.99    inference(flattening,[],[f46])).
% 11.00/1.99  
% 11.00/1.99  fof(f79,plain,(
% 11.00/1.99    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f47])).
% 11.00/1.99  
% 11.00/1.99  fof(f11,axiom,(
% 11.00/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f38,plain,(
% 11.00/1.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.00/1.99    inference(ennf_transformation,[],[f11])).
% 11.00/1.99  
% 11.00/1.99  fof(f72,plain,(
% 11.00/1.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f38])).
% 11.00/1.99  
% 11.00/1.99  fof(f2,axiom,(
% 11.00/1.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f21,plain,(
% 11.00/1.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 11.00/1.99    inference(ennf_transformation,[],[f2])).
% 11.00/1.99  
% 11.00/1.99  fof(f22,plain,(
% 11.00/1.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.00/1.99    inference(flattening,[],[f21])).
% 11.00/1.99  
% 11.00/1.99  fof(f58,plain,(
% 11.00/1.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f22])).
% 11.00/1.99  
% 11.00/1.99  fof(f88,plain,(
% 11.00/1.99    ( ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) )),
% 11.00/1.99    inference(cnf_transformation,[],[f56])).
% 11.00/1.99  
% 11.00/1.99  fof(f89,plain,(
% 11.00/1.99    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)),
% 11.00/1.99    inference(cnf_transformation,[],[f56])).
% 11.00/1.99  
% 11.00/1.99  fof(f61,plain,(
% 11.00/1.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f50])).
% 11.00/1.99  
% 11.00/1.99  fof(f90,plain,(
% 11.00/1.99    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.00/1.99    inference(equality_resolution,[],[f61])).
% 11.00/1.99  
% 11.00/1.99  fof(f70,plain,(
% 11.00/1.99    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f37])).
% 11.00/1.99  
% 11.00/1.99  fof(f69,plain,(
% 11.00/1.99    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f37])).
% 11.00/1.99  
% 11.00/1.99  fof(f74,plain,(
% 11.00/1.99    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.00/1.99    inference(cnf_transformation,[],[f52])).
% 11.00/1.99  
% 11.00/1.99  fof(f3,axiom,(
% 11.00/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 11.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/1.99  
% 11.00/1.99  fof(f23,plain,(
% 11.00/1.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 11.00/1.99    inference(ennf_transformation,[],[f3])).
% 11.00/1.99  
% 11.00/1.99  fof(f24,plain,(
% 11.00/1.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 11.00/1.99    inference(flattening,[],[f23])).
% 11.00/1.99  
% 11.00/1.99  fof(f59,plain,(
% 11.00/1.99    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 11.00/2.00    inference(cnf_transformation,[],[f24])).
% 11.00/2.00  
% 11.00/2.00  fof(f1,axiom,(
% 11.00/2.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.00/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.00/2.00  
% 11.00/2.00  fof(f19,plain,(
% 11.00/2.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 11.00/2.00    inference(unused_predicate_definition_removal,[],[f1])).
% 11.00/2.00  
% 11.00/2.00  fof(f20,plain,(
% 11.00/2.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 11.00/2.00    inference(ennf_transformation,[],[f19])).
% 11.00/2.00  
% 11.00/2.00  fof(f57,plain,(
% 11.00/2.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 11.00/2.00    inference(cnf_transformation,[],[f20])).
% 11.00/2.00  
% 11.00/2.00  fof(f76,plain,(
% 11.00/2.00    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.00/2.00    inference(cnf_transformation,[],[f52])).
% 11.00/2.00  
% 11.00/2.00  cnf(c_12,plain,
% 11.00/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.00/2.00      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 11.00/2.00      | v2_struct_0(X1)
% 11.00/2.00      | ~ l1_pre_topc(X1)
% 11.00/2.00      | ~ v2_pre_topc(X1) ),
% 11.00/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1131,plain,
% 11.00/2.00      ( ~ m1_pre_topc(X0_51,X1_51)
% 11.00/2.00      | m1_subset_1(k4_tmap_1(X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.00/2.00      | v2_struct_0(X1_51)
% 11.00/2.00      | ~ l1_pre_topc(X1_51)
% 11.00/2.00      | ~ v2_pre_topc(X1_51) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_12]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1742,plain,
% 11.00/2.00      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.00/2.00      | m1_subset_1(k4_tmap_1(X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) = iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1131]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_16,plain,
% 11.00/2.00      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 11.00/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1127,plain,
% 11.00/2.00      ( m1_pre_topc(X0_51,X0_51) | ~ l1_pre_topc(X0_51) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_16]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1746,plain,
% 11.00/2.00      ( m1_pre_topc(X0_51,X0_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1127]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_28,negated_conjecture,
% 11.00/2.00      ( m1_pre_topc(sK2,sK1) ),
% 11.00/2.00      inference(cnf_transformation,[],[f84]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1115,negated_conjecture,
% 11.00/2.00      ( m1_pre_topc(sK2,sK1) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_28]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1758,plain,
% 11.00/2.00      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1115]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_25,negated_conjecture,
% 11.00/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 11.00/2.00      inference(cnf_transformation,[],[f87]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1118,negated_conjecture,
% 11.00/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_25]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1755,plain,
% 11.00/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1118]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_8,plain,
% 11.00/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.00/2.00      | ~ m1_pre_topc(X3,X4)
% 11.00/2.00      | ~ m1_pre_topc(X3,X1)
% 11.00/2.00      | ~ m1_pre_topc(X1,X4)
% 11.00/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.00/2.00      | v2_struct_0(X4)
% 11.00/2.00      | v2_struct_0(X2)
% 11.00/2.00      | ~ l1_pre_topc(X4)
% 11.00/2.00      | ~ l1_pre_topc(X2)
% 11.00/2.00      | ~ v2_pre_topc(X4)
% 11.00/2.00      | ~ v2_pre_topc(X2)
% 11.00/2.00      | ~ v1_funct_1(X0)
% 11.00/2.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 11.00/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1135,plain,
% 11.00/2.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.00/2.00      | ~ m1_pre_topc(X2_51,X0_51)
% 11.00/2.00      | ~ m1_pre_topc(X0_51,X3_51)
% 11.00/2.00      | ~ m1_pre_topc(X2_51,X3_51)
% 11.00/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.00/2.00      | v2_struct_0(X1_51)
% 11.00/2.00      | v2_struct_0(X3_51)
% 11.00/2.00      | ~ l1_pre_topc(X1_51)
% 11.00/2.00      | ~ l1_pre_topc(X3_51)
% 11.00/2.00      | ~ v2_pre_topc(X1_51)
% 11.00/2.00      | ~ v2_pre_topc(X3_51)
% 11.00/2.00      | ~ v1_funct_1(X0_52)
% 11.00/2.00      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_8]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1738,plain,
% 11.00/2.00      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52)
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.00/2.00      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(X2_51,X3_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X3_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(X3_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X3_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1135]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_21,plain,
% 11.00/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.00/2.00      | ~ m1_pre_topc(X2,X0)
% 11.00/2.00      | m1_pre_topc(X2,X1)
% 11.00/2.00      | ~ l1_pre_topc(X1)
% 11.00/2.00      | ~ v2_pre_topc(X1) ),
% 11.00/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1122,plain,
% 11.00/2.00      ( ~ m1_pre_topc(X0_51,X1_51)
% 11.00/2.00      | ~ m1_pre_topc(X2_51,X0_51)
% 11.00/2.00      | m1_pre_topc(X2_51,X1_51)
% 11.00/2.00      | ~ l1_pre_topc(X1_51)
% 11.00/2.00      | ~ v2_pre_topc(X1_51) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_21]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1751,plain,
% 11.00/2.00      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(X2_51,X1_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1122]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2044,plain,
% 11.00/2.00      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52)
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.00/2.00      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X3_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(X3_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X3_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(forward_subsumption_resolution,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_1738,c_1751]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6129,plain,
% 11.00/2.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
% 11.00/2.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(X0_51,sK2) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X1_51) != iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1755,c_2044]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_32,negated_conjecture,
% 11.00/2.00      ( ~ v2_struct_0(sK1) ),
% 11.00/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_33,plain,
% 11.00/2.00      ( v2_struct_0(sK1) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_31,negated_conjecture,
% 11.00/2.00      ( v2_pre_topc(sK1) ),
% 11.00/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_34,plain,
% 11.00/2.00      ( v2_pre_topc(sK1) = iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_30,negated_conjecture,
% 11.00/2.00      ( l1_pre_topc(sK1) ),
% 11.00/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_35,plain,
% 11.00/2.00      ( l1_pre_topc(sK1) = iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_27,negated_conjecture,
% 11.00/2.00      ( v1_funct_1(sK3) ),
% 11.00/2.00      inference(cnf_transformation,[],[f85]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_38,plain,
% 11.00/2.00      ( v1_funct_1(sK3) = iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_26,negated_conjecture,
% 11.00/2.00      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 11.00/2.00      inference(cnf_transformation,[],[f86]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_39,plain,
% 11.00/2.00      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6362,plain,
% 11.00/2.00      ( l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
% 11.00/2.00      | m1_pre_topc(X0_51,sK2) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X1_51) != iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_6129,c_33,c_34,c_35,c_38,c_39]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6363,plain,
% 11.00/2.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
% 11.00/2.00      | m1_pre_topc(X0_51,sK2) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X1_51) != iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top ),
% 11.00/2.00      inference(renaming,[status(thm)],[c_6362]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6374,plain,
% 11.00/2.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(sK1,sK1,sK2,X0_51,sK3)
% 11.00/2.00      | m1_pre_topc(X0_51,sK2) != iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1758,c_6363]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6585,plain,
% 11.00/2.00      ( m1_pre_topc(X0_51,sK2) != iProver_top
% 11.00/2.00      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(sK1,sK1,sK2,X0_51,sK3) ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_6374,c_33,c_34,c_35]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6586,plain,
% 11.00/2.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(sK1,sK1,sK2,X0_51,sK3)
% 11.00/2.00      | m1_pre_topc(X0_51,sK2) != iProver_top ),
% 11.00/2.00      inference(renaming,[status(thm)],[c_6585]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6593,plain,
% 11.00/2.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
% 11.00/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1746,c_6586]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_7,plain,
% 11.00/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.00/2.00      | ~ m1_pre_topc(X3,X1)
% 11.00/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.00/2.00      | v2_struct_0(X1)
% 11.00/2.00      | v2_struct_0(X2)
% 11.00/2.00      | ~ l1_pre_topc(X1)
% 11.00/2.00      | ~ l1_pre_topc(X2)
% 11.00/2.00      | ~ v2_pre_topc(X1)
% 11.00/2.00      | ~ v2_pre_topc(X2)
% 11.00/2.00      | ~ v1_funct_1(X0)
% 11.00/2.00      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 11.00/2.00      inference(cnf_transformation,[],[f64]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1136,plain,
% 11.00/2.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.00/2.00      | ~ m1_pre_topc(X2_51,X0_51)
% 11.00/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.00/2.00      | v2_struct_0(X1_51)
% 11.00/2.00      | v2_struct_0(X0_51)
% 11.00/2.00      | ~ l1_pre_topc(X1_51)
% 11.00/2.00      | ~ l1_pre_topc(X0_51)
% 11.00/2.00      | ~ v2_pre_topc(X1_51)
% 11.00/2.00      | ~ v2_pre_topc(X0_51)
% 11.00/2.00      | ~ v1_funct_1(X0_52)
% 11.00/2.00      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_52,X2_51) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_7]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1737,plain,
% 11.00/2.00      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_52,X2_51)
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.00/2.00      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1136]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_3933,plain,
% 11.00/2.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51)
% 11.00/2.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(X0_51,sK2) != iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | v2_struct_0(sK2) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | l1_pre_topc(sK2) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK2) != iProver_top
% 11.00/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1755,c_1737]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_29,negated_conjecture,
% 11.00/2.00      ( ~ v2_struct_0(sK2) ),
% 11.00/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_36,plain,
% 11.00/2.00      ( v2_struct_0(sK2) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6,plain,
% 11.00/2.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 11.00/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1137,plain,
% 11.00/2.00      ( ~ m1_pre_topc(X0_51,X1_51)
% 11.00/2.00      | ~ l1_pre_topc(X1_51)
% 11.00/2.00      | l1_pre_topc(X0_51) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_6]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1736,plain,
% 11.00/2.00      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) = iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1137]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2568,plain,
% 11.00/2.00      ( l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | l1_pre_topc(sK2) = iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1758,c_1736]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_5,plain,
% 11.00/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.00/2.00      | ~ l1_pre_topc(X1)
% 11.00/2.00      | ~ v2_pre_topc(X1)
% 11.00/2.00      | v2_pre_topc(X0) ),
% 11.00/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1138,plain,
% 11.00/2.00      ( ~ m1_pre_topc(X0_51,X1_51)
% 11.00/2.00      | ~ l1_pre_topc(X1_51)
% 11.00/2.00      | ~ v2_pre_topc(X1_51)
% 11.00/2.00      | v2_pre_topc(X0_51) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_5]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1735,plain,
% 11.00/2.00      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) = iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1138]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2878,plain,
% 11.00/2.00      ( l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK2) = iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1758,c_1735]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4626,plain,
% 11.00/2.00      ( m1_pre_topc(X0_51,sK2) != iProver_top
% 11.00/2.00      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51) ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_3933,c_33,c_34,c_35,c_36,c_38,c_39,c_2568,c_2878]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4627,plain,
% 11.00/2.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51)
% 11.00/2.00      | m1_pre_topc(X0_51,sK2) != iProver_top ),
% 11.00/2.00      inference(renaming,[status(thm)],[c_4626]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4634,plain,
% 11.00/2.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2)
% 11.00/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1746,c_4627]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4712,plain,
% 11.00/2.00      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_4634,c_35,c_2568]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_11,plain,
% 11.00/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.00/2.00      | ~ m1_pre_topc(X3,X4)
% 11.00/2.00      | ~ m1_pre_topc(X1,X4)
% 11.00/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.00/2.00      | v2_struct_0(X4)
% 11.00/2.00      | v2_struct_0(X2)
% 11.00/2.00      | ~ l1_pre_topc(X4)
% 11.00/2.00      | ~ l1_pre_topc(X2)
% 11.00/2.00      | ~ v2_pre_topc(X4)
% 11.00/2.00      | ~ v2_pre_topc(X2)
% 11.00/2.00      | ~ v1_funct_1(X0)
% 11.00/2.00      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 11.00/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1132,plain,
% 11.00/2.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.00/2.00      | ~ m1_pre_topc(X0_51,X2_51)
% 11.00/2.00      | ~ m1_pre_topc(X3_51,X2_51)
% 11.00/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.00/2.00      | v2_struct_0(X1_51)
% 11.00/2.00      | v2_struct_0(X2_51)
% 11.00/2.00      | ~ l1_pre_topc(X1_51)
% 11.00/2.00      | ~ l1_pre_topc(X2_51)
% 11.00/2.00      | ~ v2_pre_topc(X1_51)
% 11.00/2.00      | ~ v2_pre_topc(X2_51)
% 11.00/2.00      | ~ v1_funct_1(X0_52)
% 11.00/2.00      | v1_funct_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52)) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_11]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1741,plain,
% 11.00/2.00      ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.00/2.00      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(X3_51,X2_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X2_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(X2_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X2_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.00/2.00      | v1_funct_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52)) = iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1132]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_3996,plain,
% 11.00/2.00      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X1_51) != iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)) = iProver_top
% 11.00/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1755,c_1741]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4699,plain,
% 11.00/2.00      ( v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X1_51) != iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_3996,c_33,c_34,c_35,c_38,c_39]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4700,plain,
% 11.00/2.00      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X1_51) != iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)) = iProver_top ),
% 11.00/2.00      inference(renaming,[status(thm)],[c_4699]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_10,plain,
% 11.00/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.00/2.00      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 11.00/2.00      | ~ m1_pre_topc(X4,X3)
% 11.00/2.00      | ~ m1_pre_topc(X1,X3)
% 11.00/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.00/2.00      | v2_struct_0(X3)
% 11.00/2.00      | v2_struct_0(X2)
% 11.00/2.00      | ~ l1_pre_topc(X3)
% 11.00/2.00      | ~ l1_pre_topc(X2)
% 11.00/2.00      | ~ v2_pre_topc(X3)
% 11.00/2.00      | ~ v2_pre_topc(X2)
% 11.00/2.00      | ~ v1_funct_1(X0) ),
% 11.00/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1133,plain,
% 11.00/2.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.00/2.00      | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),u1_struct_0(X3_51),u1_struct_0(X1_51))
% 11.00/2.00      | ~ m1_pre_topc(X0_51,X2_51)
% 11.00/2.00      | ~ m1_pre_topc(X3_51,X2_51)
% 11.00/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.00/2.00      | v2_struct_0(X1_51)
% 11.00/2.00      | v2_struct_0(X2_51)
% 11.00/2.00      | ~ l1_pre_topc(X1_51)
% 11.00/2.00      | ~ l1_pre_topc(X2_51)
% 11.00/2.00      | ~ v2_pre_topc(X1_51)
% 11.00/2.00      | ~ v2_pre_topc(X2_51)
% 11.00/2.00      | ~ v1_funct_1(X0_52) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_10]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1740,plain,
% 11.00/2.00      ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.00/2.00      | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),u1_struct_0(X3_51),u1_struct_0(X1_51)) = iProver_top
% 11.00/2.00      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(X3_51,X2_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X2_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(X2_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X2_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1133]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_20,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
% 11.00/2.00      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 11.00/2.00      | ~ m1_pre_topc(X0,X3)
% 11.00/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 11.00/2.00      | v2_struct_0(X3)
% 11.00/2.00      | v2_struct_0(X1)
% 11.00/2.00      | v2_struct_0(X0)
% 11.00/2.00      | ~ l1_pre_topc(X3)
% 11.00/2.00      | ~ l1_pre_topc(X1)
% 11.00/2.00      | ~ v2_pre_topc(X3)
% 11.00/2.00      | ~ v2_pre_topc(X1)
% 11.00/2.00      | ~ v1_funct_1(X2) ),
% 11.00/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1123,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,k3_tmap_1(X2_51,X1_51,X0_51,X0_51,X0_52))
% 11.00/2.00      | ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.00/2.00      | ~ m1_pre_topc(X0_51,X2_51)
% 11.00/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.00/2.00      | v2_struct_0(X1_51)
% 11.00/2.00      | v2_struct_0(X0_51)
% 11.00/2.00      | v2_struct_0(X2_51)
% 11.00/2.00      | ~ l1_pre_topc(X1_51)
% 11.00/2.00      | ~ l1_pre_topc(X2_51)
% 11.00/2.00      | ~ v2_pre_topc(X1_51)
% 11.00/2.00      | ~ v2_pre_topc(X2_51)
% 11.00/2.00      | ~ v1_funct_1(X0_52) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_20]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1750,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,k3_tmap_1(X2_51,X1_51,X0_51,X0_51,X0_52)) = iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.00/2.00      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X2_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(X2_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X2_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1123]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_9,plain,
% 11.00/2.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.00/2.00      | ~ m1_pre_topc(X3,X4)
% 11.00/2.00      | ~ m1_pre_topc(X1,X4)
% 11.00/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.00/2.00      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 11.00/2.00      | v2_struct_0(X4)
% 11.00/2.00      | v2_struct_0(X2)
% 11.00/2.00      | ~ l1_pre_topc(X4)
% 11.00/2.00      | ~ l1_pre_topc(X2)
% 11.00/2.00      | ~ v2_pre_topc(X4)
% 11.00/2.00      | ~ v2_pre_topc(X2)
% 11.00/2.00      | ~ v1_funct_1(X0) ),
% 11.00/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1134,plain,
% 11.00/2.00      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.00/2.00      | ~ m1_pre_topc(X0_51,X2_51)
% 11.00/2.00      | ~ m1_pre_topc(X3_51,X2_51)
% 11.00/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.00/2.00      | m1_subset_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
% 11.00/2.00      | v2_struct_0(X1_51)
% 11.00/2.00      | v2_struct_0(X2_51)
% 11.00/2.00      | ~ l1_pre_topc(X1_51)
% 11.00/2.00      | ~ l1_pre_topc(X2_51)
% 11.00/2.00      | ~ v2_pre_topc(X1_51)
% 11.00/2.00      | ~ v2_pre_topc(X2_51)
% 11.00/2.00      | ~ v1_funct_1(X0_52) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_9]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1739,plain,
% 11.00/2.00      ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.00/2.00      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(X3_51,X2_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.00/2.00      | m1_subset_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51)))) = iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X2_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(X2_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X2_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1134]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4,plain,
% 11.00/2.00      ( ~ r2_funct_2(X0,X1,X2,X3)
% 11.00/2.00      | ~ v1_funct_2(X2,X0,X1)
% 11.00/2.00      | ~ v1_funct_2(X3,X0,X1)
% 11.00/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.00/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.00/2.00      | ~ v1_funct_1(X2)
% 11.00/2.00      | ~ v1_funct_1(X3)
% 11.00/2.00      | X3 = X2 ),
% 11.00/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1139,plain,
% 11.00/2.00      ( ~ r2_funct_2(X0_52,X1_52,X2_52,X3_52)
% 11.00/2.00      | ~ v1_funct_2(X2_52,X0_52,X1_52)
% 11.00/2.00      | ~ v1_funct_2(X3_52,X0_52,X1_52)
% 11.00/2.00      | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 11.00/2.00      | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 11.00/2.00      | ~ v1_funct_1(X2_52)
% 11.00/2.00      | ~ v1_funct_1(X3_52)
% 11.00/2.00      | X3_52 = X2_52 ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_4]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1734,plain,
% 11.00/2.00      ( X0_52 = X1_52
% 11.00/2.00      | r2_funct_2(X2_52,X3_52,X1_52,X0_52) != iProver_top
% 11.00/2.00      | v1_funct_2(X1_52,X2_52,X3_52) != iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,X2_52,X3_52) != iProver_top
% 11.00/2.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
% 11.00/2.00      | v1_funct_1(X1_52) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1139]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_3601,plain,
% 11.00/2.00      ( sK3 = X0_52
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) != iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.00/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1755,c_1734]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_3705,plain,
% 11.00/2.00      ( v1_funct_1(X0_52) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | sK3 = X0_52
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) != iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_3601,c_38,c_39]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_3706,plain,
% 11.00/2.00      ( sK3 = X0_52
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) != iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(renaming,[status(thm)],[c_3705]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4377,plain,
% 11.00/2.00      ( k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52) = sK3
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(X1_51),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | v1_funct_2(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_51),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.00/2.00      | v1_funct_1(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1739,c_3706]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4851,plain,
% 11.00/2.00      ( v2_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_51),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 11.00/2.00      | v1_funct_2(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(X1_51),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top
% 11.00/2.00      | k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52) = sK3
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.00/2.00      | v1_funct_1(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_4377,c_33,c_34,c_35]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4852,plain,
% 11.00/2.00      ( k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52) = sK3
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(X1_51),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | v1_funct_2(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_51),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.00/2.00      | v1_funct_1(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top ),
% 11.00/2.00      inference(renaming,[status(thm)],[c_4851]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4867,plain,
% 11.00/2.00      ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
% 11.00/2.00      | v1_funct_2(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 11.00/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | v2_struct_0(sK2) = iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3)) != iProver_top
% 11.00/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1750,c_4852]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_40,plain,
% 11.00/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4872,plain,
% 11.00/2.00      ( v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3)) != iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | v1_funct_2(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
% 11.00/2.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_4867,c_33,c_34,c_35,c_36,c_38,c_39,c_40]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4873,plain,
% 11.00/2.00      ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
% 11.00/2.00      | v1_funct_2(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3)) != iProver_top ),
% 11.00/2.00      inference(renaming,[status(thm)],[c_4872]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4885,plain,
% 11.00/2.00      ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
% 11.00/2.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 11.00/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3)) != iProver_top
% 11.00/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1740,c_4873]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_5066,plain,
% 11.00/2.00      ( v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3)) != iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 11.00/2.00      | k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_4885,c_33,c_34,c_35,c_38,c_39,c_40]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_5067,plain,
% 11.00/2.00      ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
% 11.00/2.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3)) != iProver_top ),
% 11.00/2.00      inference(renaming,[status(thm)],[c_5066]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_5078,plain,
% 11.00/2.00      ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
% 11.00/2.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_4700,c_5067]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_5088,plain,
% 11.00/2.00      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1758,c_5078]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_37,plain,
% 11.00/2.00      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_5080,plain,
% 11.00/2.00      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
% 11.00/2.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_5078]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_5135,plain,
% 11.00/2.00      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3 ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_5088,c_33,c_34,c_35,c_37,c_5080]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6594,plain,
% 11.00/2.00      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 11.00/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.00/2.00      inference(light_normalisation,[status(thm)],[c_6593,c_4712,c_5135]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6597,plain,
% 11.00/2.00      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_6594,c_35,c_2568]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_18,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 11.00/2.00      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 11.00/2.00      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 11.00/2.00      | ~ m1_pre_topc(X0,X2)
% 11.00/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 11.00/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 11.00/2.00      | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
% 11.00/2.00      | v2_struct_0(X1)
% 11.00/2.00      | v2_struct_0(X2)
% 11.00/2.00      | v2_struct_0(X0)
% 11.00/2.00      | ~ l1_pre_topc(X1)
% 11.00/2.00      | ~ l1_pre_topc(X2)
% 11.00/2.00      | ~ v2_pre_topc(X1)
% 11.00/2.00      | ~ v2_pre_topc(X2)
% 11.00/2.00      | ~ v1_funct_1(X3)
% 11.00/2.00      | ~ v1_funct_1(X4) ),
% 11.00/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1125,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52)
% 11.00/2.00      | ~ v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.00/2.00      | ~ v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51))
% 11.00/2.00      | ~ m1_pre_topc(X0_51,X2_51)
% 11.00/2.00      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.00/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
% 11.00/2.00      | r2_hidden(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X0_51))
% 11.00/2.00      | v2_struct_0(X1_51)
% 11.00/2.00      | v2_struct_0(X0_51)
% 11.00/2.00      | v2_struct_0(X2_51)
% 11.00/2.00      | ~ l1_pre_topc(X1_51)
% 11.00/2.00      | ~ l1_pre_topc(X2_51)
% 11.00/2.00      | ~ v2_pre_topc(X1_51)
% 11.00/2.00      | ~ v2_pre_topc(X2_51)
% 11.00/2.00      | ~ v1_funct_1(X0_52)
% 11.00/2.00      | ~ v1_funct_1(X1_52) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_18]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1748,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
% 11.00/2.00      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
% 11.00/2.00      | r2_hidden(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X0_51)) = iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X2_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(X2_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X2_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.00/2.00      | v1_funct_1(X1_52) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1125]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6602,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | v2_struct_0(sK2) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | l1_pre_topc(sK2) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK2) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.00/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_6597,c_1748]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2529,plain,
% 11.00/2.00      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_1127]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2534,plain,
% 11.00/2.00      ( m1_pre_topc(sK2,sK2) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK2) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_2529]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_7351,plain,
% 11.00/2.00      ( v1_funct_1(X0_52) != iProver_top
% 11.00/2.00      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_6602,c_33,c_34,c_35,c_36,c_38,c_39,c_40,c_2534,c_2568,
% 11.00/2.00                 c_2878]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_7352,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(renaming,[status(thm)],[c_7351]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_22,plain,
% 11.00/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.00/2.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 11.00/2.00      | ~ r2_hidden(X2,u1_struct_0(X0))
% 11.00/2.00      | v2_struct_0(X1)
% 11.00/2.00      | v2_struct_0(X0)
% 11.00/2.00      | ~ l1_pre_topc(X1)
% 11.00/2.00      | ~ v2_pre_topc(X1)
% 11.00/2.00      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 11.00/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1121,plain,
% 11.00/2.00      ( ~ m1_pre_topc(X0_51,X1_51)
% 11.00/2.00      | ~ m1_subset_1(X0_52,u1_struct_0(X1_51))
% 11.00/2.00      | ~ r2_hidden(X0_52,u1_struct_0(X0_51))
% 11.00/2.00      | v2_struct_0(X1_51)
% 11.00/2.00      | v2_struct_0(X0_51)
% 11.00/2.00      | ~ l1_pre_topc(X1_51)
% 11.00/2.00      | ~ v2_pre_topc(X1_51)
% 11.00/2.00      | k1_funct_1(k4_tmap_1(X1_51,X0_51),X0_52) = X0_52 ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_22]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1752,plain,
% 11.00/2.00      ( k1_funct_1(k4_tmap_1(X0_51,X1_51),X0_52) = X0_52
% 11.00/2.00      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
% 11.00/2.00      | r2_hidden(X0_52,u1_struct_0(X1_51)) != iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1121]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_15,plain,
% 11.00/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.00/2.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.00/2.00      | ~ l1_pre_topc(X1) ),
% 11.00/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1128,plain,
% 11.00/2.00      ( ~ m1_pre_topc(X0_51,X1_51)
% 11.00/2.00      | m1_subset_1(u1_struct_0(X0_51),k1_zfmisc_1(u1_struct_0(X1_51)))
% 11.00/2.00      | ~ l1_pre_topc(X1_51) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_15]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1745,plain,
% 11.00/2.00      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.00/2.00      | m1_subset_1(u1_struct_0(X0_51),k1_zfmisc_1(u1_struct_0(X1_51))) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1128]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1,plain,
% 11.00/2.00      ( m1_subset_1(X0,X1)
% 11.00/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.00/2.00      | ~ r2_hidden(X0,X2) ),
% 11.00/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1142,plain,
% 11.00/2.00      ( m1_subset_1(X0_52,X1_52)
% 11.00/2.00      | ~ m1_subset_1(X2_52,k1_zfmisc_1(X1_52))
% 11.00/2.00      | ~ r2_hidden(X0_52,X2_52) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_1]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1731,plain,
% 11.00/2.00      ( m1_subset_1(X0_52,X1_52) = iProver_top
% 11.00/2.00      | m1_subset_1(X2_52,k1_zfmisc_1(X1_52)) != iProver_top
% 11.00/2.00      | r2_hidden(X0_52,X2_52) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1142]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2869,plain,
% 11.00/2.00      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,u1_struct_0(X1_51)) = iProver_top
% 11.00/2.00      | r2_hidden(X0_52,u1_struct_0(X0_51)) != iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1745,c_1731]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_3853,plain,
% 11.00/2.00      ( k1_funct_1(k4_tmap_1(X0_51,X1_51),X0_52) = X0_52
% 11.00/2.00      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 11.00/2.00      | r2_hidden(X0_52,u1_struct_0(X1_51)) != iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top ),
% 11.00/2.00      inference(forward_subsumption_resolution,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_1752,c_2869]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_7362,plain,
% 11.00/2.00      ( k1_funct_1(k4_tmap_1(X0_51,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | v2_struct_0(sK2) = iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_7352,c_3853]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_22464,plain,
% 11.00/2.00      ( v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.00/2.00      | k1_funct_1(k4_tmap_1(X0_51,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_7362,c_36]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_22465,plain,
% 11.00/2.00      ( k1_funct_1(k4_tmap_1(X0_51,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(renaming,[status(thm)],[c_22464]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_22478,plain,
% 11.00/2.00      ( k1_funct_1(k4_tmap_1(X0_51,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 11.00/2.00      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1742,c_22465]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_22560,plain,
% 11.00/2.00      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 11.00/2.00      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_22478]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_7360,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,X0_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) = iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_7352,c_2869]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_24,negated_conjecture,
% 11.00/2.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 11.00/2.00      | ~ r2_hidden(X0,u1_struct_0(sK2))
% 11.00/2.00      | k1_funct_1(sK3,X0) = X0 ),
% 11.00/2.00      inference(cnf_transformation,[],[f88]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1119,negated_conjecture,
% 11.00/2.00      ( ~ m1_subset_1(X0_52,u1_struct_0(sK1))
% 11.00/2.00      | ~ r2_hidden(X0_52,u1_struct_0(sK2))
% 11.00/2.00      | k1_funct_1(sK3,X0_52) = X0_52 ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_24]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1754,plain,
% 11.00/2.00      ( k1_funct_1(sK3,X0_52) = X0_52
% 11.00/2.00      | m1_subset_1(X0_52,u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | r2_hidden(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1119]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_16198,plain,
% 11.00/2.00      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) != iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_7360,c_1754]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_16581,plain,
% 11.00/2.00      ( v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.00/2.00      | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_16198,c_35,c_37,c_7352]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_16582,plain,
% 11.00/2.00      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(renaming,[status(thm)],[c_16581]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_16591,plain,
% 11.00/2.00      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 11.00/2.00      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1742,c_16582]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_23,negated_conjecture,
% 11.00/2.00      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
% 11.00/2.00      inference(cnf_transformation,[],[f89]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1145,plain,( X0_52 = X0_52 ),theory(equality) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1168,plain,
% 11.00/2.00      ( sK3 = sK3 ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_1145]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_3,plain,
% 11.00/2.00      ( r2_funct_2(X0,X1,X2,X2)
% 11.00/2.00      | ~ v1_funct_2(X2,X0,X1)
% 11.00/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.00/2.00      | ~ v1_funct_1(X2) ),
% 11.00/2.00      inference(cnf_transformation,[],[f90]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1140,plain,
% 11.00/2.00      ( r2_funct_2(X0_52,X1_52,X2_52,X2_52)
% 11.00/2.00      | ~ v1_funct_2(X2_52,X0_52,X1_52)
% 11.00/2.00      | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 11.00/2.00      | ~ v1_funct_1(X2_52) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_3]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2257,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 11.00/2.00      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 11.00/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.00/2.00      | ~ v1_funct_1(sK3) ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_1140]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2418,plain,
% 11.00/2.00      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_1145]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2429,plain,
% 11.00/2.00      ( u1_struct_0(X0_51) = u1_struct_0(X0_51) ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_1145]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2676,plain,
% 11.00/2.00      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_2429]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_3715,plain,
% 11.00/2.00      ( k4_tmap_1(sK1,sK2) = sK3
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
% 11.00/2.00      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1742,c_3706]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_3734,plain,
% 11.00/2.00      ( k4_tmap_1(sK1,sK2) = sK3
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
% 11.00/2.00      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_3715,c_33,c_34,c_35,c_37]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_13,plain,
% 11.00/2.00      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 11.00/2.00      | ~ m1_pre_topc(X1,X0)
% 11.00/2.00      | v2_struct_0(X0)
% 11.00/2.00      | ~ l1_pre_topc(X0)
% 11.00/2.00      | ~ v2_pre_topc(X0) ),
% 11.00/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1130,plain,
% 11.00/2.00      ( v1_funct_2(k4_tmap_1(X0_51,X1_51),u1_struct_0(X1_51),u1_struct_0(X0_51))
% 11.00/2.00      | ~ m1_pre_topc(X1_51,X0_51)
% 11.00/2.00      | v2_struct_0(X0_51)
% 11.00/2.00      | ~ l1_pre_topc(X0_51)
% 11.00/2.00      | ~ v2_pre_topc(X0_51) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_13]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2540,plain,
% 11.00/2.00      ( v1_funct_2(k4_tmap_1(sK1,X0_51),u1_struct_0(X0_51),u1_struct_0(sK1))
% 11.00/2.00      | ~ m1_pre_topc(X0_51,sK1)
% 11.00/2.00      | v2_struct_0(sK1)
% 11.00/2.00      | ~ l1_pre_topc(sK1)
% 11.00/2.00      | ~ v2_pre_topc(sK1) ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_1130]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4307,plain,
% 11.00/2.00      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 11.00/2.00      | ~ m1_pre_topc(sK2,sK1)
% 11.00/2.00      | v2_struct_0(sK1)
% 11.00/2.00      | ~ l1_pre_topc(sK1)
% 11.00/2.00      | ~ v2_pre_topc(sK1) ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_2540]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4310,plain,
% 11.00/2.00      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_4307]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_14,plain,
% 11.00/2.00      ( ~ m1_pre_topc(X0,X1)
% 11.00/2.00      | v2_struct_0(X1)
% 11.00/2.00      | ~ l1_pre_topc(X1)
% 11.00/2.00      | ~ v2_pre_topc(X1)
% 11.00/2.00      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 11.00/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1129,plain,
% 11.00/2.00      ( ~ m1_pre_topc(X0_51,X1_51)
% 11.00/2.00      | v2_struct_0(X1_51)
% 11.00/2.00      | ~ l1_pre_topc(X1_51)
% 11.00/2.00      | ~ v2_pre_topc(X1_51)
% 11.00/2.00      | v1_funct_1(k4_tmap_1(X1_51,X0_51)) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_14]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4742,plain,
% 11.00/2.00      ( ~ m1_pre_topc(sK2,sK1)
% 11.00/2.00      | v2_struct_0(sK1)
% 11.00/2.00      | ~ l1_pre_topc(sK1)
% 11.00/2.00      | ~ v2_pre_topc(sK1)
% 11.00/2.00      | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_1129]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_4743,plain,
% 11.00/2.00      ( m1_pre_topc(sK2,sK1) != iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_4742]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1155,plain,
% 11.00/2.00      ( ~ r2_funct_2(X0_52,X1_52,X2_52,X3_52)
% 11.00/2.00      | r2_funct_2(X4_52,X5_52,X6_52,X7_52)
% 11.00/2.00      | X4_52 != X0_52
% 11.00/2.00      | X5_52 != X1_52
% 11.00/2.00      | X6_52 != X2_52
% 11.00/2.00      | X7_52 != X3_52 ),
% 11.00/2.00      theory(equality) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2378,plain,
% 11.00/2.00      ( r2_funct_2(X0_52,X1_52,X2_52,X3_52)
% 11.00/2.00      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 11.00/2.00      | X1_52 != u1_struct_0(sK1)
% 11.00/2.00      | X0_52 != u1_struct_0(sK2)
% 11.00/2.00      | X2_52 != sK3
% 11.00/2.00      | X3_52 != sK3 ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_1155]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2639,plain,
% 11.00/2.00      ( r2_funct_2(X0_52,u1_struct_0(sK1),X1_52,X2_52)
% 11.00/2.00      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 11.00/2.00      | X0_52 != u1_struct_0(sK2)
% 11.00/2.00      | X1_52 != sK3
% 11.00/2.00      | X2_52 != sK3
% 11.00/2.00      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_2378]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_3665,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,X1_52)
% 11.00/2.00      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 11.00/2.00      | X0_52 != sK3
% 11.00/2.00      | X1_52 != sK3
% 11.00/2.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 11.00/2.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_2639]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6257,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
% 11.00/2.00      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 11.00/2.00      | k4_tmap_1(sK1,sK2) != sK3
% 11.00/2.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 11.00/2.00      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 11.00/2.00      | sK3 != sK3 ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_3665]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_17118,plain,
% 11.00/2.00      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_16591,c_33,c_34,c_35,c_37,c_27,c_26,c_25,c_23,c_1168,
% 11.00/2.00                 c_2257,c_2418,c_2676,c_3734,c_4310,c_4743,c_6257]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_19,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 11.00/2.00      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 11.00/2.00      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 11.00/2.00      | ~ m1_pre_topc(X0,X2)
% 11.00/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 11.00/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 11.00/2.00      | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2))
% 11.00/2.00      | v2_struct_0(X1)
% 11.00/2.00      | v2_struct_0(X2)
% 11.00/2.00      | v2_struct_0(X0)
% 11.00/2.00      | ~ l1_pre_topc(X1)
% 11.00/2.00      | ~ l1_pre_topc(X2)
% 11.00/2.00      | ~ v2_pre_topc(X1)
% 11.00/2.00      | ~ v2_pre_topc(X2)
% 11.00/2.00      | ~ v1_funct_1(X3)
% 11.00/2.00      | ~ v1_funct_1(X4) ),
% 11.00/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1124,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52)
% 11.00/2.00      | ~ v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.00/2.00      | ~ v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51))
% 11.00/2.00      | ~ m1_pre_topc(X0_51,X2_51)
% 11.00/2.00      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.00/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
% 11.00/2.00      | m1_subset_1(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X2_51))
% 11.00/2.00      | v2_struct_0(X1_51)
% 11.00/2.00      | v2_struct_0(X0_51)
% 11.00/2.00      | v2_struct_0(X2_51)
% 11.00/2.00      | ~ l1_pre_topc(X1_51)
% 11.00/2.00      | ~ l1_pre_topc(X2_51)
% 11.00/2.00      | ~ v2_pre_topc(X1_51)
% 11.00/2.00      | ~ v2_pre_topc(X2_51)
% 11.00/2.00      | ~ v1_funct_1(X0_52)
% 11.00/2.00      | ~ v1_funct_1(X1_52) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_19]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1749,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
% 11.00/2.00      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
% 11.00/2.00      | m1_subset_1(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X2_51)) = iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X2_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(X2_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X2_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.00/2.00      | v1_funct_1(X1_52) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1124]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6601,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 11.00/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | v2_struct_0(sK2) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | l1_pre_topc(sK2) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK2) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.00/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_6597,c_1749]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6930,plain,
% 11.00/2.00      ( v1_funct_1(X0_52) != iProver_top
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_6601,c_33,c_34,c_35,c_36,c_38,c_39,c_40,c_2534,c_2568,
% 11.00/2.00                 c_2878]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6931,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top ),
% 11.00/2.00      inference(renaming,[status(thm)],[c_6930]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2,plain,
% 11.00/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.00/2.00      | ~ m1_subset_1(X3,X1)
% 11.00/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.00/2.00      | ~ v1_funct_1(X0)
% 11.00/2.00      | v1_xboole_0(X1)
% 11.00/2.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 11.00/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1141,plain,
% 11.00/2.00      ( ~ v1_funct_2(X0_52,X1_52,X2_52)
% 11.00/2.00      | ~ m1_subset_1(X3_52,X1_52)
% 11.00/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 11.00/2.00      | ~ v1_funct_1(X0_52)
% 11.00/2.00      | v1_xboole_0(X1_52)
% 11.00/2.00      | k3_funct_2(X1_52,X2_52,X0_52,X3_52) = k1_funct_1(X0_52,X3_52) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_2]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1732,plain,
% 11.00/2.00      ( k3_funct_2(X0_52,X1_52,X2_52,X3_52) = k1_funct_1(X2_52,X3_52)
% 11.00/2.00      | v1_funct_2(X2_52,X0_52,X1_52) != iProver_top
% 11.00/2.00      | m1_subset_1(X3_52,X0_52) != iProver_top
% 11.00/2.00      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 11.00/2.00      | v1_funct_1(X2_52) != iProver_top
% 11.00/2.00      | v1_xboole_0(X0_52) = iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1141]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_3081,plain,
% 11.00/2.00      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
% 11.00/2.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 11.00/2.00      | v1_funct_1(sK3) != iProver_top
% 11.00/2.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1755,c_1732]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_3583,plain,
% 11.00/2.00      ( m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 11.00/2.00      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
% 11.00/2.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_3081,c_38,c_39]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_3584,plain,
% 11.00/2.00      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
% 11.00/2.00      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 11.00/2.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 11.00/2.00      inference(renaming,[status(thm)],[c_3583]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_6940,plain,
% 11.00/2.00      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52))
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.00/2.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_6931,c_3584]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_7079,plain,
% 11.00/2.00      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 11.00/2.00      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 11.00/2.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1742,c_6940]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_7136,plain,
% 11.00/2.00      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 11.00/2.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_7079,c_33,c_34,c_35,c_37,c_27,c_26,c_25,c_23,c_1168,
% 11.00/2.00                 c_2257,c_2418,c_2676,c_3734,c_4310,c_4743,c_6257]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_0,plain,
% 11.00/2.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.00/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1143,plain,
% 11.00/2.00      ( ~ r2_hidden(X0_52,X1_52) | ~ v1_xboole_0(X1_52) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_0]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1730,plain,
% 11.00/2.00      ( r2_hidden(X0_52,X1_52) != iProver_top
% 11.00/2.00      | v1_xboole_0(X1_52) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1143]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_7361,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.00/2.00      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_7352,c_1730]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_7629,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 11.00/2.00      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,sK1) != iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 11.00/2.00      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_1742,c_7361]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_7682,plain,
% 11.00/2.00      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_7629,c_33,c_34,c_35,c_37,c_27,c_26,c_25,c_23,c_1168,
% 11.00/2.00                 c_2257,c_2418,c_2676,c_3734,c_4310,c_4743,c_6257]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_7687,plain,
% 11.00/2.00      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_7136,c_7682]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_17,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 11.00/2.00      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 11.00/2.00      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 11.00/2.00      | ~ m1_pre_topc(X0,X2)
% 11.00/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 11.00/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 11.00/2.00      | v2_struct_0(X1)
% 11.00/2.00      | v2_struct_0(X2)
% 11.00/2.00      | v2_struct_0(X0)
% 11.00/2.00      | ~ l1_pre_topc(X1)
% 11.00/2.00      | ~ l1_pre_topc(X2)
% 11.00/2.00      | ~ v2_pre_topc(X1)
% 11.00/2.00      | ~ v2_pre_topc(X2)
% 11.00/2.00      | ~ v1_funct_1(X3)
% 11.00/2.00      | ~ v1_funct_1(X4)
% 11.00/2.00      | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK0(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK0(X1,X2,X0,X3,X4)) ),
% 11.00/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1126,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52)
% 11.00/2.00      | ~ v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 11.00/2.00      | ~ v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51))
% 11.00/2.00      | ~ m1_pre_topc(X0_51,X2_51)
% 11.00/2.00      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 11.00/2.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
% 11.00/2.00      | v2_struct_0(X1_51)
% 11.00/2.00      | v2_struct_0(X0_51)
% 11.00/2.00      | v2_struct_0(X2_51)
% 11.00/2.00      | ~ l1_pre_topc(X1_51)
% 11.00/2.00      | ~ l1_pre_topc(X2_51)
% 11.00/2.00      | ~ v2_pre_topc(X1_51)
% 11.00/2.00      | ~ v2_pre_topc(X2_51)
% 11.00/2.00      | ~ v1_funct_1(X0_52)
% 11.00/2.00      | ~ v1_funct_1(X1_52)
% 11.00/2.00      | k3_funct_2(u1_struct_0(X2_51),u1_struct_0(X1_51),X0_52,sK0(X1_51,X2_51,X0_51,X0_52,X1_52)) != k1_funct_1(X1_52,sK0(X1_51,X2_51,X0_51,X0_52,X1_52)) ),
% 11.00/2.00      inference(subtyping,[status(esa)],[c_17]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_1747,plain,
% 11.00/2.00      ( k3_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,sK0(X1_51,X0_51,X2_51,X0_52,X1_52)) != k1_funct_1(X1_52,sK0(X1_51,X0_51,X2_51,X0_52,X1_52))
% 11.00/2.00      | r2_funct_2(u1_struct_0(X2_51),u1_struct_0(X1_51),k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52) = iProver_top
% 11.00/2.00      | v1_funct_2(X1_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
% 11.00/2.00      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 11.00/2.00      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 11.00/2.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
% 11.00/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 11.00/2.00      | v2_struct_0(X2_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X1_51) = iProver_top
% 11.00/2.00      | v2_struct_0(X0_51) = iProver_top
% 11.00/2.00      | l1_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | l1_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X1_51) != iProver_top
% 11.00/2.00      | v2_pre_topc(X0_51) != iProver_top
% 11.00/2.00      | v1_funct_1(X0_52) != iProver_top
% 11.00/2.00      | v1_funct_1(X1_52) != iProver_top ),
% 11.00/2.00      inference(predicate_to_equality,[status(thm)],[c_1126]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_8599,plain,
% 11.00/2.00      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),k4_tmap_1(sK1,sK2)) = iProver_top
% 11.00/2.00      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.00/2.00      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | v2_struct_0(sK2) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | l1_pre_topc(sK2) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK2) != iProver_top
% 11.00/2.00      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 11.00/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.00/2.00      inference(superposition,[status(thm)],[c_7687,c_1747]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_8600,plain,
% 11.00/2.00      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 11.00/2.00      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 11.00/2.00      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.00/2.00      | m1_pre_topc(sK2,sK2) != iProver_top
% 11.00/2.00      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 11.00/2.00      | v2_struct_0(sK1) = iProver_top
% 11.00/2.00      | v2_struct_0(sK2) = iProver_top
% 11.00/2.00      | l1_pre_topc(sK1) != iProver_top
% 11.00/2.00      | l1_pre_topc(sK2) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK1) != iProver_top
% 11.00/2.00      | v2_pre_topc(sK2) != iProver_top
% 11.00/2.00      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 11.00/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.00/2.00      inference(light_normalisation,[status(thm)],[c_8599,c_6597]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2574,plain,
% 11.00/2.00      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK2) ),
% 11.00/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_2568]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_2886,plain,
% 11.00/2.00      ( ~ l1_pre_topc(sK1) | ~ v2_pre_topc(sK1) | v2_pre_topc(sK2) ),
% 11.00/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_2878]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_3736,plain,
% 11.00/2.00      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
% 11.00/2.00      | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 11.00/2.00      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 11.00/2.00      | k4_tmap_1(sK1,sK2) = sK3 ),
% 11.00/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_3734]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_8601,plain,
% 11.00/2.00      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2))
% 11.00/2.00      | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 11.00/2.00      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 11.00/2.00      | ~ m1_pre_topc(sK2,sK2)
% 11.00/2.00      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.00/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.00/2.00      | v2_struct_0(sK1)
% 11.00/2.00      | v2_struct_0(sK2)
% 11.00/2.00      | ~ l1_pre_topc(sK1)
% 11.00/2.00      | ~ l1_pre_topc(sK2)
% 11.00/2.00      | ~ v2_pre_topc(sK1)
% 11.00/2.00      | ~ v2_pre_topc(sK2)
% 11.00/2.00      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 11.00/2.00      | ~ v1_funct_1(sK3)
% 11.00/2.00      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
% 11.00/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_8600]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_8831,plain,
% 11.00/2.00      ( ~ m1_pre_topc(sK2,sK1)
% 11.00/2.00      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 11.00/2.00      | v2_struct_0(sK1)
% 11.00/2.00      | ~ l1_pre_topc(sK1)
% 11.00/2.00      | ~ v2_pre_topc(sK1) ),
% 11.00/2.00      inference(instantiation,[status(thm)],[c_1131]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_13383,plain,
% 11.00/2.00      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
% 11.00/2.00      inference(global_propositional_subsumption,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_8600,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25,c_23,
% 11.00/2.00                 c_1168,c_2257,c_2418,c_2529,c_2574,c_2676,c_2886,c_3736,
% 11.00/2.00                 c_4307,c_4742,c_6257,c_8601,c_8831]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(c_17121,plain,
% 11.00/2.00      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 11.00/2.00      inference(demodulation,[status(thm)],[c_17118,c_13383]) ).
% 11.00/2.00  
% 11.00/2.00  cnf(contradiction,plain,
% 11.00/2.00      ( $false ),
% 11.00/2.00      inference(minisat,
% 11.00/2.00                [status(thm)],
% 11.00/2.00                [c_22560,c_17121,c_6257,c_4743,c_4310,c_3734,c_2676,
% 11.00/2.00                 c_2418,c_2257,c_1168,c_23,c_25,c_26,c_27,c_37,c_35,c_34,
% 11.00/2.00                 c_33]) ).
% 11.00/2.00  
% 11.00/2.00  
% 11.00/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.00/2.00  
% 11.00/2.00  ------                               Statistics
% 11.00/2.00  
% 11.00/2.00  ------ General
% 11.00/2.00  
% 11.00/2.00  abstr_ref_over_cycles:                  0
% 11.00/2.00  abstr_ref_under_cycles:                 0
% 11.00/2.00  gc_basic_clause_elim:                   0
% 11.00/2.00  forced_gc_time:                         0
% 11.00/2.00  parsing_time:                           0.011
% 11.00/2.00  unif_index_cands_time:                  0.
% 11.00/2.00  unif_index_add_time:                    0.
% 11.00/2.00  orderings_time:                         0.
% 11.00/2.00  out_proof_time:                         0.023
% 11.00/2.00  total_time:                             1.018
% 11.00/2.00  num_of_symbols:                         56
% 11.00/2.00  num_of_terms:                           27890
% 11.00/2.00  
% 11.00/2.00  ------ Preprocessing
% 11.00/2.00  
% 11.00/2.00  num_of_splits:                          0
% 11.00/2.00  num_of_split_atoms:                     0
% 11.00/2.00  num_of_reused_defs:                     0
% 11.00/2.00  num_eq_ax_congr_red:                    42
% 11.00/2.00  num_of_sem_filtered_clauses:            1
% 11.00/2.00  num_of_subtypes:                        2
% 11.00/2.00  monotx_restored_types:                  0
% 11.00/2.00  sat_num_of_epr_types:                   0
% 11.00/2.00  sat_num_of_non_cyclic_types:            0
% 11.00/2.00  sat_guarded_non_collapsed_types:        1
% 11.00/2.00  num_pure_diseq_elim:                    0
% 11.00/2.00  simp_replaced_by:                       0
% 11.00/2.00  res_preprocessed:                       124
% 11.00/2.00  prep_upred:                             0
% 11.00/2.00  prep_unflattend:                        33
% 11.00/2.00  smt_new_axioms:                         0
% 11.00/2.00  pred_elim_cands:                        10
% 11.00/2.00  pred_elim:                              0
% 11.00/2.00  pred_elim_cl:                           0
% 11.00/2.00  pred_elim_cycles:                       3
% 11.00/2.00  merged_defs:                            0
% 11.00/2.00  merged_defs_ncl:                        0
% 11.00/2.00  bin_hyper_res:                          0
% 11.00/2.00  prep_cycles:                            3
% 11.00/2.00  pred_elim_time:                         0.027
% 11.00/2.00  splitting_time:                         0.
% 11.00/2.00  sem_filter_time:                        0.
% 11.00/2.00  monotx_time:                            0.
% 11.00/2.00  subtype_inf_time:                       0.001
% 11.00/2.00  
% 11.00/2.00  ------ Problem properties
% 11.00/2.00  
% 11.00/2.00  clauses:                                33
% 11.00/2.00  conjectures:                            10
% 11.00/2.00  epr:                                    11
% 11.00/2.00  horn:                                   19
% 11.00/2.00  ground:                                 9
% 11.00/2.00  unary:                                  9
% 11.00/2.00  binary:                                 2
% 11.00/2.00  lits:                                   195
% 11.00/2.00  lits_eq:                                7
% 11.00/2.00  fd_pure:                                0
% 11.00/2.00  fd_pseudo:                              0
% 11.00/2.00  fd_cond:                                0
% 11.00/2.00  fd_pseudo_cond:                         1
% 11.00/2.00  ac_symbols:                             0
% 11.00/2.00  
% 11.00/2.00  ------ Propositional Solver
% 11.00/2.00  
% 11.00/2.00  prop_solver_calls:                      26
% 11.00/2.00  prop_fast_solver_calls:                 3882
% 11.00/2.00  smt_solver_calls:                       0
% 11.00/2.00  smt_fast_solver_calls:                  0
% 11.00/2.00  prop_num_of_clauses:                    6878
% 11.00/2.00  prop_preprocess_simplified:             15723
% 11.00/2.00  prop_fo_subsumed:                       544
% 11.00/2.00  prop_solver_time:                       0.
% 11.00/2.00  smt_solver_time:                        0.
% 11.00/2.00  smt_fast_solver_time:                   0.
% 11.00/2.00  prop_fast_solver_time:                  0.
% 11.00/2.00  prop_unsat_core_time:                   0.001
% 11.00/2.00  
% 11.00/2.00  ------ QBF
% 11.00/2.00  
% 11.00/2.00  qbf_q_res:                              0
% 11.00/2.00  qbf_num_tautologies:                    0
% 11.00/2.00  qbf_prep_cycles:                        0
% 11.00/2.00  
% 11.00/2.00  ------ BMC1
% 11.00/2.00  
% 11.00/2.00  bmc1_current_bound:                     -1
% 11.00/2.00  bmc1_last_solved_bound:                 -1
% 11.00/2.00  bmc1_unsat_core_size:                   -1
% 11.00/2.00  bmc1_unsat_core_parents_size:           -1
% 11.00/2.00  bmc1_merge_next_fun:                    0
% 11.00/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.00/2.00  
% 11.00/2.00  ------ Instantiation
% 11.00/2.00  
% 11.00/2.00  inst_num_of_clauses:                    1798
% 11.00/2.00  inst_num_in_passive:                    660
% 11.00/2.00  inst_num_in_active:                     886
% 11.00/2.00  inst_num_in_unprocessed:                252
% 11.00/2.00  inst_num_of_loops:                      970
% 11.00/2.00  inst_num_of_learning_restarts:          0
% 11.00/2.00  inst_num_moves_active_passive:          80
% 11.00/2.00  inst_lit_activity:                      0
% 11.00/2.00  inst_lit_activity_moves:                1
% 11.00/2.00  inst_num_tautologies:                   0
% 11.00/2.00  inst_num_prop_implied:                  0
% 11.00/2.00  inst_num_existing_simplified:           0
% 11.00/2.00  inst_num_eq_res_simplified:             0
% 11.00/2.00  inst_num_child_elim:                    0
% 11.00/2.00  inst_num_of_dismatching_blockings:      1107
% 11.00/2.00  inst_num_of_non_proper_insts:           2190
% 11.00/2.00  inst_num_of_duplicates:                 0
% 11.00/2.00  inst_inst_num_from_inst_to_res:         0
% 11.00/2.00  inst_dismatching_checking_time:         0.
% 11.00/2.00  
% 11.00/2.00  ------ Resolution
% 11.00/2.00  
% 11.00/2.00  res_num_of_clauses:                     0
% 11.00/2.00  res_num_in_passive:                     0
% 11.00/2.00  res_num_in_active:                      0
% 11.00/2.00  res_num_of_loops:                       127
% 11.00/2.00  res_forward_subset_subsumed:            51
% 11.00/2.00  res_backward_subset_subsumed:           2
% 11.00/2.00  res_forward_subsumed:                   0
% 11.00/2.00  res_backward_subsumed:                  0
% 11.00/2.00  res_forward_subsumption_resolution:     0
% 11.00/2.00  res_backward_subsumption_resolution:    0
% 11.00/2.00  res_clause_to_clause_subsumption:       2302
% 11.00/2.00  res_orphan_elimination:                 0
% 11.00/2.00  res_tautology_del:                      119
% 11.00/2.00  res_num_eq_res_simplified:              0
% 11.00/2.00  res_num_sel_changes:                    0
% 11.00/2.00  res_moves_from_active_to_pass:          0
% 11.00/2.00  
% 11.00/2.00  ------ Superposition
% 11.00/2.00  
% 11.00/2.00  sup_time_total:                         0.
% 11.00/2.00  sup_time_generating:                    0.
% 11.00/2.00  sup_time_sim_full:                      0.
% 11.00/2.00  sup_time_sim_immed:                     0.
% 11.00/2.00  
% 11.00/2.00  sup_num_of_clauses:                     293
% 11.00/2.00  sup_num_in_active:                      170
% 11.00/2.00  sup_num_in_passive:                     123
% 11.00/2.00  sup_num_of_loops:                       193
% 11.00/2.00  sup_fw_superposition:                   222
% 11.00/2.00  sup_bw_superposition:                   149
% 11.00/2.00  sup_immediate_simplified:               96
% 11.00/2.00  sup_given_eliminated:                   0
% 11.00/2.00  comparisons_done:                       0
% 11.00/2.00  comparisons_avoided:                    22
% 11.00/2.00  
% 11.00/2.00  ------ Simplifications
% 11.00/2.00  
% 11.00/2.00  
% 11.00/2.00  sim_fw_subset_subsumed:                 35
% 11.00/2.00  sim_bw_subset_subsumed:                 18
% 11.00/2.00  sim_fw_subsumed:                        14
% 11.00/2.00  sim_bw_subsumed:                        1
% 11.00/2.00  sim_fw_subsumption_res:                 24
% 11.00/2.00  sim_bw_subsumption_res:                 7
% 11.00/2.00  sim_tautology_del:                      7
% 11.00/2.00  sim_eq_tautology_del:                   15
% 11.00/2.00  sim_eq_res_simp:                        0
% 11.00/2.00  sim_fw_demodulated:                     14
% 11.00/2.00  sim_bw_demodulated:                     20
% 11.00/2.00  sim_light_normalised:                   40
% 11.00/2.00  sim_joinable_taut:                      0
% 11.00/2.00  sim_joinable_simp:                      0
% 11.00/2.00  sim_ac_normalised:                      0
% 11.00/2.00  sim_smt_subsumption:                    0
% 11.00/2.00  
%------------------------------------------------------------------------------
