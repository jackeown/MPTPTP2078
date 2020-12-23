%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:45 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :  276 (8402 expanded)
%              Number of clauses        :  191 (2369 expanded)
%              Number of leaves         :   22 (2556 expanded)
%              Depth                    :   47
%              Number of atoms          : 1883 (83971 expanded)
%              Number of equality atoms :  790 (11486 expanded)
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

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f47,plain,(
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
    inference(flattening,[],[f47])).

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,
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

fof(f55,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f48,f54,f53,f52])).

fof(f83,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f31,plain,(
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
    inference(flattening,[],[f31])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f80,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f29,plain,(
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
    inference(flattening,[],[f29])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f33,plain,(
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
    inference(flattening,[],[f33])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f34])).

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

fof(f41,plain,(
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
    inference(flattening,[],[f41])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f34])).

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

fof(f22,plain,(
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

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f34])).

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

fof(f39,plain,(
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
    inference(flattening,[],[f39])).

fof(f50,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
        & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f50])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f59])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f51])).

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

fof(f45,plain,(
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
    inference(flattening,[],[f45])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1079,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | m1_subset_1(k4_tmap_1(X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1658,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_subset_1(k4_tmap_1(X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1079])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1063,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1674,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1066,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1671,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1066])).

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
    inference(cnf_transformation,[],[f64])).

cnf(c_1083,plain,
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

cnf(c_1654,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1083])).

cnf(c_4696,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1671,c_1654])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_33,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_34,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4922,plain,
    ( l1_pre_topc(X1_51) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4696,c_33,c_34,c_35,c_38,c_39])).

cnf(c_4923,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_4922])).

cnf(c_4928,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1674,c_4923])).

cnf(c_16,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1075,plain,
    ( m1_pre_topc(X0_51,X0_51)
    | ~ l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1662,plain,
    ( m1_pre_topc(X0_51,X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1075])).

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
    inference(cnf_transformation,[],[f63])).

cnf(c_1084,plain,
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

cnf(c_1653,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1084])).

cnf(c_3741,plain,
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
    inference(superposition,[status(thm)],[c_1671,c_1653])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_36,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_37,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1086,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1854,plain,
    ( ~ m1_pre_topc(sK2,X0_51)
    | ~ l1_pre_topc(X0_51)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1086])).

cnf(c_1855,plain,
    ( m1_pre_topc(sK2,X0_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1854])).

cnf(c_1857,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1855])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1087,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | v2_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2110,plain,
    ( ~ m1_pre_topc(sK2,X0_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v2_pre_topc(X0_51)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1087])).

cnf(c_2111,plain,
    ( m1_pre_topc(sK2,X0_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2110])).

cnf(c_2113,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2111])).

cnf(c_4126,plain,
    ( m1_pre_topc(X0_51,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3741,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_1857,c_2113])).

cnf(c_4127,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51)
    | m1_pre_topc(X0_51,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4126])).

cnf(c_4132,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_4127])).

cnf(c_4188,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4132,c_35,c_37,c_1857])).

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
    inference(cnf_transformation,[],[f66])).

cnf(c_1081,plain,
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

cnf(c_1656,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1081])).

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
    inference(cnf_transformation,[],[f76])).

cnf(c_1071,plain,
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

cnf(c_1666,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1071])).

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
    inference(cnf_transformation,[],[f67])).

cnf(c_1082,plain,
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

cnf(c_1655,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1082])).

cnf(c_3,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1088,plain,
    ( ~ r2_funct_2(X0_52,X1_52,X2_52,X3_52)
    | ~ v1_funct_2(X2_52,X0_52,X1_52)
    | ~ v1_funct_2(X3_52,X0_52,X1_52)
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X2_52)
    | ~ v1_funct_1(X3_52)
    | X3_52 = X2_52 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1649,plain,
    ( X0_52 = X1_52
    | r2_funct_2(X2_52,X3_52,X1_52,X0_52) != iProver_top
    | v1_funct_2(X1_52,X2_52,X3_52) != iProver_top
    | v1_funct_2(X0_52,X2_52,X3_52) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1088])).

cnf(c_3512,plain,
    ( sK3 = X0_52
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1671,c_1649])).

cnf(c_3584,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | sK3 = X0_52
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3512,c_38,c_39])).

cnf(c_3585,plain,
    ( sK3 = X0_52
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_3584])).

cnf(c_4103,plain,
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
    inference(superposition,[status(thm)],[c_1655,c_3585])).

cnf(c_4351,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_4103,c_33,c_34,c_35])).

cnf(c_4352,plain,
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
    inference(renaming,[status(thm)],[c_4351])).

cnf(c_4355,plain,
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
    inference(superposition,[status(thm)],[c_1666,c_4352])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

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
    inference(cnf_transformation,[],[f65])).

cnf(c_1080,plain,
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

cnf(c_1730,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(X2_51,X1_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | v2_struct_0(X1_51)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k3_tmap_1(X1_51,sK1,X0_51,X2_51,X0_52)) ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_1876,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_pre_topc(sK2,X1_51)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(X1_51)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_51)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_51)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1730])).

cnf(c_3652,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,X0_51)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(X0_51)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1876])).

cnf(c_3653,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3652])).

cnf(c_4360,plain,
    ( v2_pre_topc(X0_51) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
    | v1_funct_2(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4355,c_33,c_34,c_35,c_36,c_38,c_39,c_40,c_3653])).

cnf(c_4361,plain,
    ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
    | v1_funct_2(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_4360])).

cnf(c_4366,plain,
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
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1656,c_4361])).

cnf(c_4581,plain,
    ( l1_pre_topc(X0_51) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
    | v2_struct_0(X0_51) = iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4366,c_33,c_34,c_35,c_38,c_39,c_40])).

cnf(c_4582,plain,
    ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_4581])).

cnf(c_4587,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1674,c_4582])).

cnf(c_4368,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4366])).

cnf(c_4592,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4587,c_33,c_34,c_35,c_37,c_38,c_39,c_40,c_4368])).

cnf(c_4930,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4928,c_4188,c_4592])).

cnf(c_2584,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1075])).

cnf(c_2585,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2584])).

cnf(c_4936,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4930,c_33,c_34,c_35,c_37,c_1857,c_2585])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_1073,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52)
    | ~ v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
    | ~ v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51))
    | ~ m1_pre_topc(X0_51,X2_51)
    | r2_hidden(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X0_51))
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
    | ~ v1_funct_1(X1_52) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1664,plain,
    ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
    | m1_pre_topc(X0_51,X2_51) != iProver_top
    | r2_hidden(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X0_51)) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X2_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X2_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X2_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1073])).

cnf(c_4940,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4936,c_1664])).

cnf(c_6403,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4940,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_1857,c_2113,c_2585])).

cnf(c_6404,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_6403])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k1_funct_1(sK3,X0) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1067,negated_conjecture,
    ( ~ r2_hidden(X0_52,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_52,u1_struct_0(sK1))
    | k1_funct_1(sK3,X0_52) = X0_52 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1670,plain,
    ( k1_funct_1(sK3,X0_52) = X0_52
    | r2_hidden(X0_52,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1067])).

cnf(c_6407,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_6404,c_1670])).

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
    inference(cnf_transformation,[],[f73])).

cnf(c_1072,plain,
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

cnf(c_1665,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1072])).

cnf(c_4939,plain,
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
    inference(superposition,[status(thm)],[c_4936,c_1665])).

cnf(c_5060,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4939,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_1857,c_2113,c_2585])).

cnf(c_5061,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5060])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1085,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | m1_subset_1(X0_52,u1_struct_0(X1_51))
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1652,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X1_51)) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1085])).

cnf(c_5065,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_5061,c_1652])).

cnf(c_5248,plain,
    ( v2_struct_0(X0_51) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5065,c_36])).

cnf(c_5249,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5248])).

cnf(c_5254,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X1_51)) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_5249,c_1652])).

cnf(c_1128,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1086])).

cnf(c_5350,plain,
    ( v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X1_51)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5254,c_1128])).

cnf(c_5351,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X1_51)) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5350])).

cnf(c_5354,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1674,c_5351])).

cnf(c_5358,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5354,c_33,c_35,c_36,c_37,c_1857,c_2585])).

cnf(c_5359,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5358])).

cnf(c_6462,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6407,c_5359])).

cnf(c_6463,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_6462])).

cnf(c_6467,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1658,c_6463])).

cnf(c_23,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1093,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_1116,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_2,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1089,plain,
    ( r2_funct_2(X0_52,X1_52,X2_52,X2_52)
    | ~ v1_funct_2(X2_52,X0_52,X1_52)
    | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X2_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2558,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1089])).

cnf(c_2706,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_1103,plain,
    ( ~ r2_funct_2(X0_52,X1_52,X2_52,X3_52)
    | r2_funct_2(X4_52,X5_52,X6_52,X7_52)
    | X4_52 != X0_52
    | X5_52 != X1_52
    | X6_52 != X2_52
    | X7_52 != X3_52 ),
    theory(equality)).

cnf(c_1837,plain,
    ( ~ r2_funct_2(X0_52,X1_52,X2_52,X3_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
    | k4_tmap_1(sK1,sK2) != X2_52
    | u1_struct_0(sK1) != X1_52
    | u1_struct_0(sK2) != X0_52
    | sK3 != X3_52 ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_3478,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
    | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
    | k4_tmap_1(sK1,sK2) != sK3
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1837])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1077,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | v2_struct_0(X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | v1_funct_1(k4_tmap_1(X1_51,X0_51)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3580,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1077])).

cnf(c_3581,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3580])).

cnf(c_3589,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1658,c_3585])).

cnf(c_3592,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
    | k4_tmap_1(sK1,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3589,c_33,c_34,c_35,c_37,c_3581])).

cnf(c_3593,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3592])).

cnf(c_3650,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_13,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1078,plain,
    ( v1_funct_2(k4_tmap_1(X0_51,X1_51),u1_struct_0(X1_51),u1_struct_0(X0_51))
    | ~ m1_pre_topc(X1_51,X0_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v2_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_5412,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_5413,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5412])).

cnf(c_6474,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6467,c_33,c_34,c_35,c_37,c_27,c_26,c_25,c_23,c_1116,c_2558,c_2706,c_3478,c_3581,c_3593,c_3650,c_5413])).

cnf(c_1659,plain,
    ( v1_funct_2(k4_tmap_1(X0_51,X1_51),u1_struct_0(X1_51),u1_struct_0(X0_51)) = iProver_top
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1078])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1090,plain,
    ( ~ v1_funct_2(X0_52,X1_52,X2_52)
    | ~ m1_subset_1(X3_52,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | ~ v1_funct_1(X0_52)
    | v1_xboole_0(X1_52)
    | k3_funct_2(X1_52,X2_52,X0_52,X3_52) = k1_funct_1(X0_52,X3_52) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1647,plain,
    ( k3_funct_2(X0_52,X1_52,X2_52,X3_52) = k1_funct_1(X2_52,X3_52)
    | v1_funct_2(X2_52,X0_52,X1_52) != iProver_top
    | m1_subset_1(X3_52,X0_52) != iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X2_52) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1090])).

cnf(c_2738,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1671,c_1647])).

cnf(c_3187,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2738,c_38,c_39])).

cnf(c_3188,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3187])).

cnf(c_5066,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5061,c_3188])).

cnf(c_5131,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1658,c_5066])).

cnf(c_5138,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5131,c_33,c_34,c_35,c_37,c_27,c_26,c_25,c_23,c_1116,c_2558,c_2706,c_3478,c_3581,c_3593,c_3650])).

cnf(c_5139,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5138])).

cnf(c_5142,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1659,c_5139])).

cnf(c_5243,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5142,c_33,c_34,c_35,c_37])).

cnf(c_6476,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6474,c_5243])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1076,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | m1_subset_1(u1_struct_0(X0_51),k1_zfmisc_1(u1_struct_0(X1_51)))
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1661,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_subset_1(u1_struct_0(X0_51),k1_zfmisc_1(u1_struct_0(X1_51))) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1076])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1091,plain,
    ( ~ r2_hidden(X0_52,X1_52)
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(X2_52))
    | ~ v1_xboole_0(X2_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1646,plain,
    ( r2_hidden(X0_52,X1_52) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(X2_52)) != iProver_top
    | v1_xboole_0(X2_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1091])).

cnf(c_2260,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | r2_hidden(X0_52,u1_struct_0(X0_51)) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X1_51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1661,c_1646])).

cnf(c_6408,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6404,c_2260])).

cnf(c_7343,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1658,c_6408])).

cnf(c_7458,plain,
    ( l1_pre_topc(X0_51) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7343,c_33,c_34,c_35,c_37,c_27,c_26,c_25,c_23,c_1116,c_2558,c_2706,c_3478,c_3581,c_3593,c_3650,c_5413])).

cnf(c_7459,plain,
    ( m1_pre_topc(sK2,X0_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_51)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7458])).

cnf(c_7465,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_7459])).

cnf(c_7543,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7465,c_35,c_37,c_1857])).

cnf(c_7547,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_6476,c_7543])).

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
    inference(cnf_transformation,[],[f75])).

cnf(c_1074,plain,
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

cnf(c_1663,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1074])).

cnf(c_7659,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
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
    inference(superposition,[status(thm)],[c_7547,c_1663])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1069,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ r2_hidden(X0_52,u1_struct_0(X0_51))
    | ~ m1_subset_1(X0_52,u1_struct_0(X1_51))
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | k1_funct_1(k4_tmap_1(X1_51,X0_51),X0_52) = X0_52 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1668,plain,
    ( k1_funct_1(k4_tmap_1(X0_51,X1_51),X0_52) = X0_52
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | r2_hidden(X0_52,u1_struct_0(X1_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1069])).

cnf(c_5363,plain,
    ( k1_funct_1(k4_tmap_1(sK1,X0_51),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK1) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_5359,c_1668])).

cnf(c_5612,plain,
    ( v2_struct_0(X0_51) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) != iProver_top
    | m1_pre_topc(X0_51,sK1) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | k1_funct_1(k4_tmap_1(sK1,X0_51),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5363,c_33,c_34,c_35])).

cnf(c_5613,plain,
    ( k1_funct_1(k4_tmap_1(sK1,X0_51),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK1) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5612])).

cnf(c_6409,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_6404,c_5613])).

cnf(c_7149,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6409,c_36,c_37])).

cnf(c_7150,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_7149])).

cnf(c_7154,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1658,c_7150])).

cnf(c_7605,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7154,c_33,c_34,c_35,c_37,c_27,c_26,c_25,c_23,c_1116,c_2558,c_2706,c_3478,c_3581,c_3593,c_3650,c_5413])).

cnf(c_7660,plain,
    ( sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
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
    inference(light_normalisation,[status(thm)],[c_7659,c_4936,c_7605])).

cnf(c_7661,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
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
    inference(equality_resolution_simp,[status(thm)],[c_7660])).

cnf(c_5573,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_5574,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5573])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7661,c_5574,c_5413,c_3650,c_3593,c_3581,c_3478,c_2706,c_2585,c_2558,c_2113,c_1857,c_1116,c_23,c_40,c_25,c_39,c_26,c_38,c_27,c_37,c_36,c_35,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:27:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.49/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/1.49  
% 7.49/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.49/1.49  
% 7.49/1.49  ------  iProver source info
% 7.49/1.49  
% 7.49/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.49/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.49/1.49  git: non_committed_changes: false
% 7.49/1.49  git: last_make_outside_of_git: false
% 7.49/1.49  
% 7.49/1.49  ------ 
% 7.49/1.49  
% 7.49/1.49  ------ Input Options
% 7.49/1.49  
% 7.49/1.49  --out_options                           all
% 7.49/1.49  --tptp_safe_out                         true
% 7.49/1.49  --problem_path                          ""
% 7.49/1.49  --include_path                          ""
% 7.49/1.49  --clausifier                            res/vclausify_rel
% 7.49/1.49  --clausifier_options                    ""
% 7.49/1.49  --stdin                                 false
% 7.49/1.49  --stats_out                             all
% 7.49/1.49  
% 7.49/1.49  ------ General Options
% 7.49/1.49  
% 7.49/1.49  --fof                                   false
% 7.49/1.49  --time_out_real                         305.
% 7.49/1.49  --time_out_virtual                      -1.
% 7.49/1.49  --symbol_type_check                     false
% 7.49/1.49  --clausify_out                          false
% 7.49/1.49  --sig_cnt_out                           false
% 7.49/1.49  --trig_cnt_out                          false
% 7.49/1.49  --trig_cnt_out_tolerance                1.
% 7.49/1.49  --trig_cnt_out_sk_spl                   false
% 7.49/1.49  --abstr_cl_out                          false
% 7.49/1.49  
% 7.49/1.49  ------ Global Options
% 7.49/1.49  
% 7.49/1.49  --schedule                              default
% 7.49/1.49  --add_important_lit                     false
% 7.49/1.49  --prop_solver_per_cl                    1000
% 7.49/1.49  --min_unsat_core                        false
% 7.49/1.49  --soft_assumptions                      false
% 7.49/1.49  --soft_lemma_size                       3
% 7.49/1.49  --prop_impl_unit_size                   0
% 7.49/1.49  --prop_impl_unit                        []
% 7.49/1.49  --share_sel_clauses                     true
% 7.49/1.49  --reset_solvers                         false
% 7.49/1.49  --bc_imp_inh                            [conj_cone]
% 7.49/1.49  --conj_cone_tolerance                   3.
% 7.49/1.49  --extra_neg_conj                        none
% 7.49/1.49  --large_theory_mode                     true
% 7.49/1.49  --prolific_symb_bound                   200
% 7.49/1.49  --lt_threshold                          2000
% 7.49/1.49  --clause_weak_htbl                      true
% 7.49/1.49  --gc_record_bc_elim                     false
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing Options
% 7.49/1.49  
% 7.49/1.49  --preprocessing_flag                    true
% 7.49/1.49  --time_out_prep_mult                    0.1
% 7.49/1.49  --splitting_mode                        input
% 7.49/1.49  --splitting_grd                         true
% 7.49/1.49  --splitting_cvd                         false
% 7.49/1.49  --splitting_cvd_svl                     false
% 7.49/1.49  --splitting_nvd                         32
% 7.49/1.49  --sub_typing                            true
% 7.49/1.49  --prep_gs_sim                           true
% 7.49/1.49  --prep_unflatten                        true
% 7.49/1.49  --prep_res_sim                          true
% 7.49/1.49  --prep_upred                            true
% 7.49/1.49  --prep_sem_filter                       exhaustive
% 7.49/1.49  --prep_sem_filter_out                   false
% 7.49/1.49  --pred_elim                             true
% 7.49/1.49  --res_sim_input                         true
% 7.49/1.49  --eq_ax_congr_red                       true
% 7.49/1.49  --pure_diseq_elim                       true
% 7.49/1.49  --brand_transform                       false
% 7.49/1.49  --non_eq_to_eq                          false
% 7.49/1.49  --prep_def_merge                        true
% 7.49/1.49  --prep_def_merge_prop_impl              false
% 7.49/1.49  --prep_def_merge_mbd                    true
% 7.49/1.49  --prep_def_merge_tr_red                 false
% 7.49/1.49  --prep_def_merge_tr_cl                  false
% 7.49/1.49  --smt_preprocessing                     true
% 7.49/1.49  --smt_ac_axioms                         fast
% 7.49/1.49  --preprocessed_out                      false
% 7.49/1.49  --preprocessed_stats                    false
% 7.49/1.49  
% 7.49/1.49  ------ Abstraction refinement Options
% 7.49/1.49  
% 7.49/1.49  --abstr_ref                             []
% 7.49/1.49  --abstr_ref_prep                        false
% 7.49/1.49  --abstr_ref_until_sat                   false
% 7.49/1.49  --abstr_ref_sig_restrict                funpre
% 7.49/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.49  --abstr_ref_under                       []
% 7.49/1.49  
% 7.49/1.49  ------ SAT Options
% 7.49/1.49  
% 7.49/1.49  --sat_mode                              false
% 7.49/1.49  --sat_fm_restart_options                ""
% 7.49/1.49  --sat_gr_def                            false
% 7.49/1.49  --sat_epr_types                         true
% 7.49/1.49  --sat_non_cyclic_types                  false
% 7.49/1.49  --sat_finite_models                     false
% 7.49/1.49  --sat_fm_lemmas                         false
% 7.49/1.49  --sat_fm_prep                           false
% 7.49/1.49  --sat_fm_uc_incr                        true
% 7.49/1.49  --sat_out_model                         small
% 7.49/1.49  --sat_out_clauses                       false
% 7.49/1.49  
% 7.49/1.49  ------ QBF Options
% 7.49/1.49  
% 7.49/1.49  --qbf_mode                              false
% 7.49/1.49  --qbf_elim_univ                         false
% 7.49/1.49  --qbf_dom_inst                          none
% 7.49/1.49  --qbf_dom_pre_inst                      false
% 7.49/1.49  --qbf_sk_in                             false
% 7.49/1.49  --qbf_pred_elim                         true
% 7.49/1.49  --qbf_split                             512
% 7.49/1.49  
% 7.49/1.49  ------ BMC1 Options
% 7.49/1.49  
% 7.49/1.49  --bmc1_incremental                      false
% 7.49/1.49  --bmc1_axioms                           reachable_all
% 7.49/1.49  --bmc1_min_bound                        0
% 7.49/1.49  --bmc1_max_bound                        -1
% 7.49/1.49  --bmc1_max_bound_default                -1
% 7.49/1.49  --bmc1_symbol_reachability              true
% 7.49/1.49  --bmc1_property_lemmas                  false
% 7.49/1.49  --bmc1_k_induction                      false
% 7.49/1.49  --bmc1_non_equiv_states                 false
% 7.49/1.49  --bmc1_deadlock                         false
% 7.49/1.49  --bmc1_ucm                              false
% 7.49/1.49  --bmc1_add_unsat_core                   none
% 7.49/1.49  --bmc1_unsat_core_children              false
% 7.49/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.49  --bmc1_out_stat                         full
% 7.49/1.49  --bmc1_ground_init                      false
% 7.49/1.49  --bmc1_pre_inst_next_state              false
% 7.49/1.49  --bmc1_pre_inst_state                   false
% 7.49/1.49  --bmc1_pre_inst_reach_state             false
% 7.49/1.49  --bmc1_out_unsat_core                   false
% 7.49/1.49  --bmc1_aig_witness_out                  false
% 7.49/1.49  --bmc1_verbose                          false
% 7.49/1.49  --bmc1_dump_clauses_tptp                false
% 7.49/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.49  --bmc1_dump_file                        -
% 7.49/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.49  --bmc1_ucm_extend_mode                  1
% 7.49/1.49  --bmc1_ucm_init_mode                    2
% 7.49/1.49  --bmc1_ucm_cone_mode                    none
% 7.49/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.49  --bmc1_ucm_relax_model                  4
% 7.49/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.49  --bmc1_ucm_layered_model                none
% 7.49/1.49  --bmc1_ucm_max_lemma_size               10
% 7.49/1.49  
% 7.49/1.49  ------ AIG Options
% 7.49/1.49  
% 7.49/1.49  --aig_mode                              false
% 7.49/1.49  
% 7.49/1.49  ------ Instantiation Options
% 7.49/1.49  
% 7.49/1.49  --instantiation_flag                    true
% 7.49/1.49  --inst_sos_flag                         true
% 7.49/1.49  --inst_sos_phase                        true
% 7.49/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.49  --inst_lit_sel_side                     num_symb
% 7.49/1.49  --inst_solver_per_active                1400
% 7.49/1.49  --inst_solver_calls_frac                1.
% 7.49/1.49  --inst_passive_queue_type               priority_queues
% 7.49/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.49  --inst_passive_queues_freq              [25;2]
% 7.49/1.49  --inst_dismatching                      true
% 7.49/1.49  --inst_eager_unprocessed_to_passive     true
% 7.49/1.49  --inst_prop_sim_given                   true
% 7.49/1.49  --inst_prop_sim_new                     false
% 7.49/1.49  --inst_subs_new                         false
% 7.49/1.49  --inst_eq_res_simp                      false
% 7.49/1.49  --inst_subs_given                       false
% 7.49/1.49  --inst_orphan_elimination               true
% 7.49/1.49  --inst_learning_loop_flag               true
% 7.49/1.49  --inst_learning_start                   3000
% 7.49/1.49  --inst_learning_factor                  2
% 7.49/1.49  --inst_start_prop_sim_after_learn       3
% 7.49/1.49  --inst_sel_renew                        solver
% 7.49/1.49  --inst_lit_activity_flag                true
% 7.49/1.49  --inst_restr_to_given                   false
% 7.49/1.49  --inst_activity_threshold               500
% 7.49/1.49  --inst_out_proof                        true
% 7.49/1.49  
% 7.49/1.49  ------ Resolution Options
% 7.49/1.49  
% 7.49/1.49  --resolution_flag                       true
% 7.49/1.49  --res_lit_sel                           adaptive
% 7.49/1.49  --res_lit_sel_side                      none
% 7.49/1.49  --res_ordering                          kbo
% 7.49/1.49  --res_to_prop_solver                    active
% 7.49/1.49  --res_prop_simpl_new                    false
% 7.49/1.49  --res_prop_simpl_given                  true
% 7.49/1.49  --res_passive_queue_type                priority_queues
% 7.49/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.49  --res_passive_queues_freq               [15;5]
% 7.49/1.49  --res_forward_subs                      full
% 7.49/1.49  --res_backward_subs                     full
% 7.49/1.49  --res_forward_subs_resolution           true
% 7.49/1.49  --res_backward_subs_resolution          true
% 7.49/1.49  --res_orphan_elimination                true
% 7.49/1.49  --res_time_limit                        2.
% 7.49/1.49  --res_out_proof                         true
% 7.49/1.49  
% 7.49/1.49  ------ Superposition Options
% 7.49/1.49  
% 7.49/1.49  --superposition_flag                    true
% 7.49/1.49  --sup_passive_queue_type                priority_queues
% 7.49/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.49  --demod_completeness_check              fast
% 7.49/1.49  --demod_use_ground                      true
% 7.49/1.49  --sup_to_prop_solver                    passive
% 7.49/1.49  --sup_prop_simpl_new                    true
% 7.49/1.49  --sup_prop_simpl_given                  true
% 7.49/1.49  --sup_fun_splitting                     true
% 7.49/1.49  --sup_smt_interval                      50000
% 7.49/1.49  
% 7.49/1.49  ------ Superposition Simplification Setup
% 7.49/1.49  
% 7.49/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.49/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.49/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.49/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.49/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.49/1.49  --sup_immed_triv                        [TrivRules]
% 7.49/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.49  --sup_immed_bw_main                     []
% 7.49/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.49/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.49  --sup_input_bw                          []
% 7.49/1.49  
% 7.49/1.49  ------ Combination Options
% 7.49/1.49  
% 7.49/1.49  --comb_res_mult                         3
% 7.49/1.49  --comb_sup_mult                         2
% 7.49/1.49  --comb_inst_mult                        10
% 7.49/1.49  
% 7.49/1.49  ------ Debug Options
% 7.49/1.49  
% 7.49/1.49  --dbg_backtrace                         false
% 7.49/1.49  --dbg_dump_prop_clauses                 false
% 7.49/1.49  --dbg_dump_prop_clauses_file            -
% 7.49/1.49  --dbg_out_stat                          false
% 7.49/1.49  ------ Parsing...
% 7.49/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.49/1.49  ------ Proving...
% 7.49/1.49  ------ Problem Properties 
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  clauses                                 33
% 7.49/1.49  conjectures                             10
% 7.49/1.49  EPR                                     10
% 7.49/1.49  Horn                                    18
% 7.49/1.49  unary                                   9
% 7.49/1.49  binary                                  1
% 7.49/1.49  lits                                    199
% 7.49/1.49  lits eq                                 7
% 7.49/1.49  fd_pure                                 0
% 7.49/1.49  fd_pseudo                               0
% 7.49/1.49  fd_cond                                 0
% 7.49/1.49  fd_pseudo_cond                          1
% 7.49/1.49  AC symbols                              0
% 7.49/1.49  
% 7.49/1.49  ------ Schedule dynamic 5 is on 
% 7.49/1.49  
% 7.49/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  ------ 
% 7.49/1.49  Current options:
% 7.49/1.49  ------ 
% 7.49/1.49  
% 7.49/1.49  ------ Input Options
% 7.49/1.49  
% 7.49/1.49  --out_options                           all
% 7.49/1.49  --tptp_safe_out                         true
% 7.49/1.49  --problem_path                          ""
% 7.49/1.49  --include_path                          ""
% 7.49/1.49  --clausifier                            res/vclausify_rel
% 7.49/1.49  --clausifier_options                    ""
% 7.49/1.49  --stdin                                 false
% 7.49/1.49  --stats_out                             all
% 7.49/1.49  
% 7.49/1.49  ------ General Options
% 7.49/1.49  
% 7.49/1.49  --fof                                   false
% 7.49/1.49  --time_out_real                         305.
% 7.49/1.49  --time_out_virtual                      -1.
% 7.49/1.49  --symbol_type_check                     false
% 7.49/1.49  --clausify_out                          false
% 7.49/1.49  --sig_cnt_out                           false
% 7.49/1.49  --trig_cnt_out                          false
% 7.49/1.49  --trig_cnt_out_tolerance                1.
% 7.49/1.49  --trig_cnt_out_sk_spl                   false
% 7.49/1.49  --abstr_cl_out                          false
% 7.49/1.49  
% 7.49/1.49  ------ Global Options
% 7.49/1.49  
% 7.49/1.49  --schedule                              default
% 7.49/1.49  --add_important_lit                     false
% 7.49/1.49  --prop_solver_per_cl                    1000
% 7.49/1.49  --min_unsat_core                        false
% 7.49/1.49  --soft_assumptions                      false
% 7.49/1.49  --soft_lemma_size                       3
% 7.49/1.49  --prop_impl_unit_size                   0
% 7.49/1.49  --prop_impl_unit                        []
% 7.49/1.49  --share_sel_clauses                     true
% 7.49/1.49  --reset_solvers                         false
% 7.49/1.49  --bc_imp_inh                            [conj_cone]
% 7.49/1.49  --conj_cone_tolerance                   3.
% 7.49/1.49  --extra_neg_conj                        none
% 7.49/1.49  --large_theory_mode                     true
% 7.49/1.49  --prolific_symb_bound                   200
% 7.49/1.49  --lt_threshold                          2000
% 7.49/1.49  --clause_weak_htbl                      true
% 7.49/1.49  --gc_record_bc_elim                     false
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing Options
% 7.49/1.49  
% 7.49/1.49  --preprocessing_flag                    true
% 7.49/1.49  --time_out_prep_mult                    0.1
% 7.49/1.49  --splitting_mode                        input
% 7.49/1.49  --splitting_grd                         true
% 7.49/1.49  --splitting_cvd                         false
% 7.49/1.49  --splitting_cvd_svl                     false
% 7.49/1.49  --splitting_nvd                         32
% 7.49/1.49  --sub_typing                            true
% 7.49/1.49  --prep_gs_sim                           true
% 7.49/1.49  --prep_unflatten                        true
% 7.49/1.49  --prep_res_sim                          true
% 7.49/1.49  --prep_upred                            true
% 7.49/1.49  --prep_sem_filter                       exhaustive
% 7.49/1.49  --prep_sem_filter_out                   false
% 7.49/1.49  --pred_elim                             true
% 7.49/1.49  --res_sim_input                         true
% 7.49/1.49  --eq_ax_congr_red                       true
% 7.49/1.49  --pure_diseq_elim                       true
% 7.49/1.49  --brand_transform                       false
% 7.49/1.49  --non_eq_to_eq                          false
% 7.49/1.49  --prep_def_merge                        true
% 7.49/1.49  --prep_def_merge_prop_impl              false
% 7.49/1.49  --prep_def_merge_mbd                    true
% 7.49/1.49  --prep_def_merge_tr_red                 false
% 7.49/1.49  --prep_def_merge_tr_cl                  false
% 7.49/1.49  --smt_preprocessing                     true
% 7.49/1.49  --smt_ac_axioms                         fast
% 7.49/1.49  --preprocessed_out                      false
% 7.49/1.49  --preprocessed_stats                    false
% 7.49/1.49  
% 7.49/1.49  ------ Abstraction refinement Options
% 7.49/1.49  
% 7.49/1.49  --abstr_ref                             []
% 7.49/1.49  --abstr_ref_prep                        false
% 7.49/1.49  --abstr_ref_until_sat                   false
% 7.49/1.49  --abstr_ref_sig_restrict                funpre
% 7.49/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.49/1.49  --abstr_ref_under                       []
% 7.49/1.49  
% 7.49/1.49  ------ SAT Options
% 7.49/1.49  
% 7.49/1.49  --sat_mode                              false
% 7.49/1.49  --sat_fm_restart_options                ""
% 7.49/1.49  --sat_gr_def                            false
% 7.49/1.49  --sat_epr_types                         true
% 7.49/1.49  --sat_non_cyclic_types                  false
% 7.49/1.49  --sat_finite_models                     false
% 7.49/1.49  --sat_fm_lemmas                         false
% 7.49/1.49  --sat_fm_prep                           false
% 7.49/1.49  --sat_fm_uc_incr                        true
% 7.49/1.49  --sat_out_model                         small
% 7.49/1.49  --sat_out_clauses                       false
% 7.49/1.49  
% 7.49/1.49  ------ QBF Options
% 7.49/1.49  
% 7.49/1.49  --qbf_mode                              false
% 7.49/1.49  --qbf_elim_univ                         false
% 7.49/1.49  --qbf_dom_inst                          none
% 7.49/1.49  --qbf_dom_pre_inst                      false
% 7.49/1.49  --qbf_sk_in                             false
% 7.49/1.49  --qbf_pred_elim                         true
% 7.49/1.49  --qbf_split                             512
% 7.49/1.49  
% 7.49/1.49  ------ BMC1 Options
% 7.49/1.49  
% 7.49/1.49  --bmc1_incremental                      false
% 7.49/1.49  --bmc1_axioms                           reachable_all
% 7.49/1.49  --bmc1_min_bound                        0
% 7.49/1.49  --bmc1_max_bound                        -1
% 7.49/1.49  --bmc1_max_bound_default                -1
% 7.49/1.49  --bmc1_symbol_reachability              true
% 7.49/1.49  --bmc1_property_lemmas                  false
% 7.49/1.49  --bmc1_k_induction                      false
% 7.49/1.49  --bmc1_non_equiv_states                 false
% 7.49/1.49  --bmc1_deadlock                         false
% 7.49/1.49  --bmc1_ucm                              false
% 7.49/1.49  --bmc1_add_unsat_core                   none
% 7.49/1.49  --bmc1_unsat_core_children              false
% 7.49/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.49/1.49  --bmc1_out_stat                         full
% 7.49/1.49  --bmc1_ground_init                      false
% 7.49/1.49  --bmc1_pre_inst_next_state              false
% 7.49/1.49  --bmc1_pre_inst_state                   false
% 7.49/1.49  --bmc1_pre_inst_reach_state             false
% 7.49/1.49  --bmc1_out_unsat_core                   false
% 7.49/1.49  --bmc1_aig_witness_out                  false
% 7.49/1.49  --bmc1_verbose                          false
% 7.49/1.49  --bmc1_dump_clauses_tptp                false
% 7.49/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.49/1.49  --bmc1_dump_file                        -
% 7.49/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.49/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.49/1.49  --bmc1_ucm_extend_mode                  1
% 7.49/1.49  --bmc1_ucm_init_mode                    2
% 7.49/1.49  --bmc1_ucm_cone_mode                    none
% 7.49/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.49/1.49  --bmc1_ucm_relax_model                  4
% 7.49/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.49/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.49/1.49  --bmc1_ucm_layered_model                none
% 7.49/1.49  --bmc1_ucm_max_lemma_size               10
% 7.49/1.49  
% 7.49/1.49  ------ AIG Options
% 7.49/1.49  
% 7.49/1.49  --aig_mode                              false
% 7.49/1.49  
% 7.49/1.49  ------ Instantiation Options
% 7.49/1.49  
% 7.49/1.49  --instantiation_flag                    true
% 7.49/1.49  --inst_sos_flag                         true
% 7.49/1.49  --inst_sos_phase                        true
% 7.49/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.49/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.49/1.49  --inst_lit_sel_side                     none
% 7.49/1.49  --inst_solver_per_active                1400
% 7.49/1.49  --inst_solver_calls_frac                1.
% 7.49/1.49  --inst_passive_queue_type               priority_queues
% 7.49/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.49/1.49  --inst_passive_queues_freq              [25;2]
% 7.49/1.49  --inst_dismatching                      true
% 7.49/1.49  --inst_eager_unprocessed_to_passive     true
% 7.49/1.49  --inst_prop_sim_given                   true
% 7.49/1.49  --inst_prop_sim_new                     false
% 7.49/1.49  --inst_subs_new                         false
% 7.49/1.49  --inst_eq_res_simp                      false
% 7.49/1.49  --inst_subs_given                       false
% 7.49/1.49  --inst_orphan_elimination               true
% 7.49/1.49  --inst_learning_loop_flag               true
% 7.49/1.49  --inst_learning_start                   3000
% 7.49/1.49  --inst_learning_factor                  2
% 7.49/1.49  --inst_start_prop_sim_after_learn       3
% 7.49/1.49  --inst_sel_renew                        solver
% 7.49/1.49  --inst_lit_activity_flag                true
% 7.49/1.49  --inst_restr_to_given                   false
% 7.49/1.49  --inst_activity_threshold               500
% 7.49/1.49  --inst_out_proof                        true
% 7.49/1.49  
% 7.49/1.49  ------ Resolution Options
% 7.49/1.49  
% 7.49/1.49  --resolution_flag                       false
% 7.49/1.49  --res_lit_sel                           adaptive
% 7.49/1.49  --res_lit_sel_side                      none
% 7.49/1.49  --res_ordering                          kbo
% 7.49/1.49  --res_to_prop_solver                    active
% 7.49/1.49  --res_prop_simpl_new                    false
% 7.49/1.49  --res_prop_simpl_given                  true
% 7.49/1.49  --res_passive_queue_type                priority_queues
% 7.49/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.49/1.49  --res_passive_queues_freq               [15;5]
% 7.49/1.49  --res_forward_subs                      full
% 7.49/1.49  --res_backward_subs                     full
% 7.49/1.49  --res_forward_subs_resolution           true
% 7.49/1.49  --res_backward_subs_resolution          true
% 7.49/1.49  --res_orphan_elimination                true
% 7.49/1.49  --res_time_limit                        2.
% 7.49/1.49  --res_out_proof                         true
% 7.49/1.49  
% 7.49/1.49  ------ Superposition Options
% 7.49/1.49  
% 7.49/1.49  --superposition_flag                    true
% 7.49/1.49  --sup_passive_queue_type                priority_queues
% 7.49/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.49/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.49/1.49  --demod_completeness_check              fast
% 7.49/1.49  --demod_use_ground                      true
% 7.49/1.49  --sup_to_prop_solver                    passive
% 7.49/1.49  --sup_prop_simpl_new                    true
% 7.49/1.49  --sup_prop_simpl_given                  true
% 7.49/1.49  --sup_fun_splitting                     true
% 7.49/1.49  --sup_smt_interval                      50000
% 7.49/1.49  
% 7.49/1.49  ------ Superposition Simplification Setup
% 7.49/1.49  
% 7.49/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.49/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.49/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.49/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.49/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.49/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.49/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.49/1.49  --sup_immed_triv                        [TrivRules]
% 7.49/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.49  --sup_immed_bw_main                     []
% 7.49/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.49/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.49/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.49/1.49  --sup_input_bw                          []
% 7.49/1.49  
% 7.49/1.49  ------ Combination Options
% 7.49/1.49  
% 7.49/1.49  --comb_res_mult                         3
% 7.49/1.49  --comb_sup_mult                         2
% 7.49/1.49  --comb_inst_mult                        10
% 7.49/1.49  
% 7.49/1.49  ------ Debug Options
% 7.49/1.49  
% 7.49/1.49  --dbg_backtrace                         false
% 7.49/1.49  --dbg_dump_prop_clauses                 false
% 7.49/1.49  --dbg_dump_prop_clauses_file            -
% 7.49/1.49  --dbg_out_stat                          false
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  ------ Proving...
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  % SZS status Theorem for theBenchmark.p
% 7.49/1.49  
% 7.49/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.49/1.49  
% 7.49/1.49  fof(f10,axiom,(
% 7.49/1.49    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f35,plain,(
% 7.49/1.49    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.49    inference(ennf_transformation,[],[f10])).
% 7.49/1.49  
% 7.49/1.49  fof(f36,plain,(
% 7.49/1.49    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.49    inference(flattening,[],[f35])).
% 7.49/1.49  
% 7.49/1.49  fof(f70,plain,(
% 7.49/1.49    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f36])).
% 7.49/1.49  
% 7.49/1.49  fof(f17,conjecture,(
% 7.49/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f18,negated_conjecture,(
% 7.49/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 7.49/1.49    inference(negated_conjecture,[],[f17])).
% 7.49/1.49  
% 7.49/1.49  fof(f47,plain,(
% 7.49/1.49    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.49/1.49    inference(ennf_transformation,[],[f18])).
% 7.49/1.49  
% 7.49/1.49  fof(f48,plain,(
% 7.49/1.49    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.49/1.49    inference(flattening,[],[f47])).
% 7.49/1.49  
% 7.49/1.49  fof(f54,plain,(
% 7.49/1.49    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 7.49/1.49    introduced(choice_axiom,[])).
% 7.49/1.49  
% 7.49/1.49  fof(f53,plain,(
% 7.49/1.49    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.49/1.49    introduced(choice_axiom,[])).
% 7.49/1.49  
% 7.49/1.49  fof(f52,plain,(
% 7.49/1.49    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 7.49/1.49    introduced(choice_axiom,[])).
% 7.49/1.49  
% 7.49/1.49  fof(f55,plain,(
% 7.49/1.49    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 7.49/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f48,f54,f53,f52])).
% 7.49/1.49  
% 7.49/1.49  fof(f83,plain,(
% 7.49/1.49    m1_pre_topc(sK2,sK1)),
% 7.49/1.49    inference(cnf_transformation,[],[f55])).
% 7.49/1.49  
% 7.49/1.49  fof(f86,plain,(
% 7.49/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 7.49/1.49    inference(cnf_transformation,[],[f55])).
% 7.49/1.49  
% 7.49/1.49  fof(f8,axiom,(
% 7.49/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f31,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.49    inference(ennf_transformation,[],[f8])).
% 7.49/1.49  
% 7.49/1.49  fof(f32,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.49    inference(flattening,[],[f31])).
% 7.49/1.49  
% 7.49/1.49  fof(f64,plain,(
% 7.49/1.49    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f32])).
% 7.49/1.49  
% 7.49/1.49  fof(f79,plain,(
% 7.49/1.49    ~v2_struct_0(sK1)),
% 7.49/1.49    inference(cnf_transformation,[],[f55])).
% 7.49/1.49  
% 7.49/1.49  fof(f80,plain,(
% 7.49/1.49    v2_pre_topc(sK1)),
% 7.49/1.49    inference(cnf_transformation,[],[f55])).
% 7.49/1.49  
% 7.49/1.49  fof(f81,plain,(
% 7.49/1.49    l1_pre_topc(sK1)),
% 7.49/1.49    inference(cnf_transformation,[],[f55])).
% 7.49/1.49  
% 7.49/1.49  fof(f84,plain,(
% 7.49/1.49    v1_funct_1(sK3)),
% 7.49/1.49    inference(cnf_transformation,[],[f55])).
% 7.49/1.49  
% 7.49/1.49  fof(f85,plain,(
% 7.49/1.49    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 7.49/1.49    inference(cnf_transformation,[],[f55])).
% 7.49/1.49  
% 7.49/1.49  fof(f12,axiom,(
% 7.49/1.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f38,plain,(
% 7.49/1.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.49/1.49    inference(ennf_transformation,[],[f12])).
% 7.49/1.49  
% 7.49/1.49  fof(f72,plain,(
% 7.49/1.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f38])).
% 7.49/1.49  
% 7.49/1.49  fof(f7,axiom,(
% 7.49/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f29,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.49    inference(ennf_transformation,[],[f7])).
% 7.49/1.49  
% 7.49/1.49  fof(f30,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.49    inference(flattening,[],[f29])).
% 7.49/1.49  
% 7.49/1.49  fof(f63,plain,(
% 7.49/1.49    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f30])).
% 7.49/1.49  
% 7.49/1.49  fof(f82,plain,(
% 7.49/1.49    ~v2_struct_0(sK2)),
% 7.49/1.49    inference(cnf_transformation,[],[f55])).
% 7.49/1.49  
% 7.49/1.49  fof(f5,axiom,(
% 7.49/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f26,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.49/1.49    inference(ennf_transformation,[],[f5])).
% 7.49/1.49  
% 7.49/1.49  fof(f61,plain,(
% 7.49/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f26])).
% 7.49/1.49  
% 7.49/1.49  fof(f4,axiom,(
% 7.49/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f24,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.49/1.49    inference(ennf_transformation,[],[f4])).
% 7.49/1.49  
% 7.49/1.49  fof(f25,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.49/1.49    inference(flattening,[],[f24])).
% 7.49/1.49  
% 7.49/1.49  fof(f60,plain,(
% 7.49/1.49    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f25])).
% 7.49/1.49  
% 7.49/1.49  fof(f9,axiom,(
% 7.49/1.49    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f33,plain,(
% 7.49/1.49    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.49    inference(ennf_transformation,[],[f9])).
% 7.49/1.49  
% 7.49/1.49  fof(f34,plain,(
% 7.49/1.49    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.49    inference(flattening,[],[f33])).
% 7.49/1.49  
% 7.49/1.49  fof(f66,plain,(
% 7.49/1.49    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f34])).
% 7.49/1.49  
% 7.49/1.49  fof(f14,axiom,(
% 7.49/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f41,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.49    inference(ennf_transformation,[],[f14])).
% 7.49/1.49  
% 7.49/1.49  fof(f42,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.49    inference(flattening,[],[f41])).
% 7.49/1.49  
% 7.49/1.49  fof(f76,plain,(
% 7.49/1.49    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f42])).
% 7.49/1.49  
% 7.49/1.49  fof(f67,plain,(
% 7.49/1.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f34])).
% 7.49/1.49  
% 7.49/1.49  fof(f3,axiom,(
% 7.49/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f22,plain,(
% 7.49/1.49    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.49/1.49    inference(ennf_transformation,[],[f3])).
% 7.49/1.49  
% 7.49/1.49  fof(f23,plain,(
% 7.49/1.49    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.49/1.49    inference(flattening,[],[f22])).
% 7.49/1.49  
% 7.49/1.49  fof(f49,plain,(
% 7.49/1.49    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.49/1.49    inference(nnf_transformation,[],[f23])).
% 7.49/1.49  
% 7.49/1.49  fof(f58,plain,(
% 7.49/1.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f49])).
% 7.49/1.49  
% 7.49/1.49  fof(f65,plain,(
% 7.49/1.49    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f34])).
% 7.49/1.49  
% 7.49/1.49  fof(f13,axiom,(
% 7.49/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f39,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.49    inference(ennf_transformation,[],[f13])).
% 7.49/1.49  
% 7.49/1.49  fof(f40,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.49    inference(flattening,[],[f39])).
% 7.49/1.49  
% 7.49/1.49  fof(f50,plain,(
% 7.49/1.49    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) => (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))))),
% 7.49/1.49    introduced(choice_axiom,[])).
% 7.49/1.49  
% 7.49/1.49  fof(f51,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f50])).
% 7.49/1.49  
% 7.49/1.49  fof(f74,plain,(
% 7.49/1.49    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f51])).
% 7.49/1.49  
% 7.49/1.49  fof(f87,plain,(
% 7.49/1.49    ( ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) )),
% 7.49/1.49    inference(cnf_transformation,[],[f55])).
% 7.49/1.49  
% 7.49/1.49  fof(f73,plain,(
% 7.49/1.49    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f51])).
% 7.49/1.49  
% 7.49/1.49  fof(f6,axiom,(
% 7.49/1.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f27,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.49    inference(ennf_transformation,[],[f6])).
% 7.49/1.49  
% 7.49/1.49  fof(f28,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.49    inference(flattening,[],[f27])).
% 7.49/1.49  
% 7.49/1.49  fof(f62,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f28])).
% 7.49/1.49  
% 7.49/1.49  fof(f88,plain,(
% 7.49/1.49    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)),
% 7.49/1.49    inference(cnf_transformation,[],[f55])).
% 7.49/1.49  
% 7.49/1.49  fof(f59,plain,(
% 7.49/1.49    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f49])).
% 7.49/1.49  
% 7.49/1.49  fof(f89,plain,(
% 7.49/1.49    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.49/1.49    inference(equality_resolution,[],[f59])).
% 7.49/1.49  
% 7.49/1.49  fof(f68,plain,(
% 7.49/1.49    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f36])).
% 7.49/1.49  
% 7.49/1.49  fof(f69,plain,(
% 7.49/1.49    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f36])).
% 7.49/1.49  
% 7.49/1.49  fof(f2,axiom,(
% 7.49/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f20,plain,(
% 7.49/1.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 7.49/1.49    inference(ennf_transformation,[],[f2])).
% 7.49/1.49  
% 7.49/1.49  fof(f21,plain,(
% 7.49/1.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 7.49/1.49    inference(flattening,[],[f20])).
% 7.49/1.49  
% 7.49/1.49  fof(f57,plain,(
% 7.49/1.49    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f21])).
% 7.49/1.49  
% 7.49/1.49  fof(f11,axiom,(
% 7.49/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f37,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.49/1.49    inference(ennf_transformation,[],[f11])).
% 7.49/1.49  
% 7.49/1.49  fof(f71,plain,(
% 7.49/1.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f37])).
% 7.49/1.49  
% 7.49/1.49  fof(f1,axiom,(
% 7.49/1.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f19,plain,(
% 7.49/1.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.49/1.49    inference(ennf_transformation,[],[f1])).
% 7.49/1.49  
% 7.49/1.49  fof(f56,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f19])).
% 7.49/1.49  
% 7.49/1.49  fof(f75,plain,(
% 7.49/1.49    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f51])).
% 7.49/1.49  
% 7.49/1.49  fof(f16,axiom,(
% 7.49/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 7.49/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.49/1.49  
% 7.49/1.49  fof(f45,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.49/1.49    inference(ennf_transformation,[],[f16])).
% 7.49/1.49  
% 7.49/1.49  fof(f46,plain,(
% 7.49/1.49    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.49/1.49    inference(flattening,[],[f45])).
% 7.49/1.49  
% 7.49/1.49  fof(f78,plain,(
% 7.49/1.49    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.49/1.49    inference(cnf_transformation,[],[f46])).
% 7.49/1.49  
% 7.49/1.49  cnf(c_12,plain,
% 7.49/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.49/1.49      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.49/1.49      | v2_struct_0(X1)
% 7.49/1.49      | ~ l1_pre_topc(X1)
% 7.49/1.49      | ~ v2_pre_topc(X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1079,plain,
% 7.49/1.49      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.49/1.49      | m1_subset_1(k4_tmap_1(X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.49/1.49      | v2_struct_0(X1_51)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | ~ v2_pre_topc(X1_51) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1658,plain,
% 7.49/1.49      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.49/1.49      | m1_subset_1(k4_tmap_1(X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) = iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X1_51) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1079]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_28,negated_conjecture,
% 7.49/1.49      ( m1_pre_topc(sK2,sK1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1063,negated_conjecture,
% 7.49/1.49      ( m1_pre_topc(sK2,sK1) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_28]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1674,plain,
% 7.49/1.49      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1063]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_25,negated_conjecture,
% 7.49/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 7.49/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1066,negated_conjecture,
% 7.49/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_25]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1671,plain,
% 7.49/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1066]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_8,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.49/1.49      | ~ m1_pre_topc(X3,X4)
% 7.49/1.49      | ~ m1_pre_topc(X3,X1)
% 7.49/1.49      | ~ m1_pre_topc(X1,X4)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.49/1.49      | v2_struct_0(X4)
% 7.49/1.49      | v2_struct_0(X2)
% 7.49/1.49      | ~ l1_pre_topc(X4)
% 7.49/1.49      | ~ l1_pre_topc(X2)
% 7.49/1.49      | ~ v2_pre_topc(X4)
% 7.49/1.49      | ~ v2_pre_topc(X2)
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1083,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.49/1.49      | ~ m1_pre_topc(X2_51,X0_51)
% 7.49/1.49      | ~ m1_pre_topc(X0_51,X3_51)
% 7.49/1.49      | ~ m1_pre_topc(X2_51,X3_51)
% 7.49/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.49/1.49      | v2_struct_0(X1_51)
% 7.49/1.49      | v2_struct_0(X3_51)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | ~ l1_pre_topc(X3_51)
% 7.49/1.49      | ~ v2_pre_topc(X1_51)
% 7.49/1.49      | ~ v2_pre_topc(X3_51)
% 7.49/1.49      | ~ v1_funct_1(X0_52)
% 7.49/1.49      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1654,plain,
% 7.49/1.49      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52)
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(X2_51,X3_51) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X3_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(X3_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X3_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1083]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4696,plain,
% 7.49/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
% 7.49/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,sK2) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X1_51) != iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1671,c_1654]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_32,negated_conjecture,
% 7.49/1.49      ( ~ v2_struct_0(sK1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_33,plain,
% 7.49/1.49      ( v2_struct_0(sK1) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_31,negated_conjecture,
% 7.49/1.49      ( v2_pre_topc(sK1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_34,plain,
% 7.49/1.49      ( v2_pre_topc(sK1) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_30,negated_conjecture,
% 7.49/1.49      ( l1_pre_topc(sK1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_35,plain,
% 7.49/1.49      ( l1_pre_topc(sK1) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_27,negated_conjecture,
% 7.49/1.49      ( v1_funct_1(sK3) ),
% 7.49/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_38,plain,
% 7.49/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_26,negated_conjecture,
% 7.49/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 7.49/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_39,plain,
% 7.49/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4922,plain,
% 7.49/1.49      ( l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
% 7.49/1.49      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,sK2) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X1_51) != iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | v2_pre_topc(X1_51) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_4696,c_33,c_34,c_35,c_38,c_39]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4923,plain,
% 7.49/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
% 7.49/1.49      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,sK2) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X1_51) != iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X1_51) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_4922]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4928,plain,
% 7.49/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
% 7.49/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1674,c_4923]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_16,plain,
% 7.49/1.49      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1075,plain,
% 7.49/1.49      ( m1_pre_topc(X0_51,X0_51) | ~ l1_pre_topc(X0_51) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1662,plain,
% 7.49/1.49      ( m1_pre_topc(X0_51,X0_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1075]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.49/1.49      | ~ m1_pre_topc(X3,X1)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.49/1.49      | v2_struct_0(X1)
% 7.49/1.49      | v2_struct_0(X2)
% 7.49/1.49      | ~ l1_pre_topc(X1)
% 7.49/1.49      | ~ l1_pre_topc(X2)
% 7.49/1.49      | ~ v2_pre_topc(X1)
% 7.49/1.49      | ~ v2_pre_topc(X2)
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.49/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1084,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.49/1.49      | ~ m1_pre_topc(X2_51,X0_51)
% 7.49/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.49/1.49      | v2_struct_0(X1_51)
% 7.49/1.49      | v2_struct_0(X0_51)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | ~ l1_pre_topc(X0_51)
% 7.49/1.49      | ~ v2_pre_topc(X1_51)
% 7.49/1.49      | ~ v2_pre_topc(X0_51)
% 7.49/1.49      | ~ v1_funct_1(X0_52)
% 7.49/1.49      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_52,X2_51) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1653,plain,
% 7.49/1.49      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_52,X2_51)
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1084]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3741,plain,
% 7.49/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51)
% 7.49/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,sK2) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | v2_struct_0(sK2) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1671,c_1653]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_29,negated_conjecture,
% 7.49/1.49      ( ~ v2_struct_0(sK2) ),
% 7.49/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_36,plain,
% 7.49/1.49      ( v2_struct_0(sK2) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_37,plain,
% 7.49/1.49      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5,plain,
% 7.49/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1086,plain,
% 7.49/1.49      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | l1_pre_topc(X0_51) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1854,plain,
% 7.49/1.49      ( ~ m1_pre_topc(sK2,X0_51)
% 7.49/1.49      | ~ l1_pre_topc(X0_51)
% 7.49/1.49      | l1_pre_topc(sK2) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1086]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1855,plain,
% 7.49/1.49      ( m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK2) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1854]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1857,plain,
% 7.49/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK2) = iProver_top ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1855]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4,plain,
% 7.49/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.49/1.49      | ~ l1_pre_topc(X1)
% 7.49/1.49      | ~ v2_pre_topc(X1)
% 7.49/1.49      | v2_pre_topc(X0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1087,plain,
% 7.49/1.49      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | ~ v2_pre_topc(X1_51)
% 7.49/1.49      | v2_pre_topc(X0_51) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2110,plain,
% 7.49/1.49      ( ~ m1_pre_topc(sK2,X0_51)
% 7.49/1.49      | ~ l1_pre_topc(X0_51)
% 7.49/1.49      | ~ v2_pre_topc(X0_51)
% 7.49/1.49      | v2_pre_topc(sK2) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1087]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2111,plain,
% 7.49/1.49      ( m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK2) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_2110]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2113,plain,
% 7.49/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK2) = iProver_top ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_2111]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4126,plain,
% 7.49/1.49      ( m1_pre_topc(X0_51,sK2) != iProver_top
% 7.49/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51) ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_3741,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_1857,c_2113]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4127,plain,
% 7.49/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51)
% 7.49/1.49      | m1_pre_topc(X0_51,sK2) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_4126]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4132,plain,
% 7.49/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2)
% 7.49/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1662,c_4127]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4188,plain,
% 7.49/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_4132,c_35,c_37,c_1857]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_10,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.49/1.49      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 7.49/1.49      | ~ m1_pre_topc(X4,X3)
% 7.49/1.49      | ~ m1_pre_topc(X1,X3)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.49/1.49      | v2_struct_0(X3)
% 7.49/1.49      | v2_struct_0(X2)
% 7.49/1.49      | ~ l1_pre_topc(X3)
% 7.49/1.49      | ~ l1_pre_topc(X2)
% 7.49/1.49      | ~ v2_pre_topc(X3)
% 7.49/1.49      | ~ v2_pre_topc(X2)
% 7.49/1.49      | ~ v1_funct_1(X0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1081,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.49/1.49      | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),u1_struct_0(X3_51),u1_struct_0(X1_51))
% 7.49/1.49      | ~ m1_pre_topc(X0_51,X2_51)
% 7.49/1.49      | ~ m1_pre_topc(X3_51,X2_51)
% 7.49/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.49/1.49      | v2_struct_0(X1_51)
% 7.49/1.49      | v2_struct_0(X2_51)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | ~ l1_pre_topc(X2_51)
% 7.49/1.49      | ~ v2_pre_topc(X1_51)
% 7.49/1.49      | ~ v2_pre_topc(X2_51)
% 7.49/1.49      | ~ v1_funct_1(X0_52) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1656,plain,
% 7.49/1.49      ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.49/1.49      | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),u1_struct_0(X3_51),u1_struct_0(X1_51)) = iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(X3_51,X2_51) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X2_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(X2_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X2_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1081]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_20,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
% 7.49/1.49      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.49/1.49      | ~ m1_pre_topc(X0,X3)
% 7.49/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.49/1.49      | v2_struct_0(X3)
% 7.49/1.49      | v2_struct_0(X1)
% 7.49/1.49      | v2_struct_0(X0)
% 7.49/1.49      | ~ l1_pre_topc(X3)
% 7.49/1.49      | ~ l1_pre_topc(X1)
% 7.49/1.49      | ~ v2_pre_topc(X3)
% 7.49/1.49      | ~ v2_pre_topc(X1)
% 7.49/1.49      | ~ v1_funct_1(X2) ),
% 7.49/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1071,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,k3_tmap_1(X2_51,X1_51,X0_51,X0_51,X0_52))
% 7.49/1.49      | ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.49/1.49      | ~ m1_pre_topc(X0_51,X2_51)
% 7.49/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.49/1.49      | v2_struct_0(X1_51)
% 7.49/1.49      | v2_struct_0(X0_51)
% 7.49/1.49      | v2_struct_0(X2_51)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | ~ l1_pre_topc(X2_51)
% 7.49/1.49      | ~ v2_pre_topc(X1_51)
% 7.49/1.49      | ~ v2_pre_topc(X2_51)
% 7.49/1.49      | ~ v1_funct_1(X0_52) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_20]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1666,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,k3_tmap_1(X2_51,X1_51,X0_51,X0_51,X0_52)) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X2_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(X2_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X2_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1071]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_9,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.49/1.49      | ~ m1_pre_topc(X3,X4)
% 7.49/1.49      | ~ m1_pre_topc(X1,X4)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.49/1.49      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.49/1.49      | v2_struct_0(X4)
% 7.49/1.49      | v2_struct_0(X2)
% 7.49/1.49      | ~ l1_pre_topc(X4)
% 7.49/1.49      | ~ l1_pre_topc(X2)
% 7.49/1.49      | ~ v2_pre_topc(X4)
% 7.49/1.49      | ~ v2_pre_topc(X2)
% 7.49/1.49      | ~ v1_funct_1(X0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1082,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.49/1.49      | ~ m1_pre_topc(X0_51,X2_51)
% 7.49/1.49      | ~ m1_pre_topc(X3_51,X2_51)
% 7.49/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.49/1.49      | m1_subset_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
% 7.49/1.49      | v2_struct_0(X1_51)
% 7.49/1.49      | v2_struct_0(X2_51)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | ~ l1_pre_topc(X2_51)
% 7.49/1.49      | ~ v2_pre_topc(X1_51)
% 7.49/1.49      | ~ v2_pre_topc(X2_51)
% 7.49/1.49      | ~ v1_funct_1(X0_52) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_9]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1655,plain,
% 7.49/1.49      ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(X3_51,X2_51) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.49/1.49      | m1_subset_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51)))) = iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X2_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(X2_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X2_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1082]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3,plain,
% 7.49/1.49      ( ~ r2_funct_2(X0,X1,X2,X3)
% 7.49/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.49/1.49      | ~ v1_funct_2(X3,X0,X1)
% 7.49/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.49      | ~ v1_funct_1(X2)
% 7.49/1.49      | ~ v1_funct_1(X3)
% 7.49/1.49      | X3 = X2 ),
% 7.49/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1088,plain,
% 7.49/1.49      ( ~ r2_funct_2(X0_52,X1_52,X2_52,X3_52)
% 7.49/1.49      | ~ v1_funct_2(X2_52,X0_52,X1_52)
% 7.49/1.49      | ~ v1_funct_2(X3_52,X0_52,X1_52)
% 7.49/1.49      | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 7.49/1.49      | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 7.49/1.49      | ~ v1_funct_1(X2_52)
% 7.49/1.49      | ~ v1_funct_1(X3_52)
% 7.49/1.49      | X3_52 = X2_52 ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1649,plain,
% 7.49/1.49      ( X0_52 = X1_52
% 7.49/1.49      | r2_funct_2(X2_52,X3_52,X1_52,X0_52) != iProver_top
% 7.49/1.49      | v1_funct_2(X1_52,X2_52,X3_52) != iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,X2_52,X3_52) != iProver_top
% 7.49/1.49      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
% 7.49/1.49      | v1_funct_1(X1_52) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1088]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3512,plain,
% 7.49/1.49      ( sK3 = X0_52
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) != iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1671,c_1649]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3584,plain,
% 7.49/1.49      ( v1_funct_1(X0_52) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | sK3 = X0_52
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) != iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_3512,c_38,c_39]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3585,plain,
% 7.49/1.49      ( sK3 = X0_52
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) != iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_3584]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4103,plain,
% 7.49/1.49      ( k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52) = sK3
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(X1_51),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | v1_funct_2(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_51),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.49/1.49      | v1_funct_1(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1655,c_3585]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4351,plain,
% 7.49/1.49      ( v2_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_51),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 7.49/1.49      | v1_funct_2(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(X1_51),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top
% 7.49/1.49      | k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52) = sK3
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.49/1.49      | v1_funct_1(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_4103,c_33,c_34,c_35]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4352,plain,
% 7.49/1.49      ( k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52) = sK3
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(X1_51),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | v1_funct_2(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_51),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.49/1.49      | v1_funct_1(k3_tmap_1(X0_51,sK1,X1_51,sK2,X0_52)) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_4351]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4355,plain,
% 7.49/1.49      ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
% 7.49/1.49      | v1_funct_2(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | v2_struct_0(sK2) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3)) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1666,c_4352]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_40,plain,
% 7.49/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_11,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.49/1.49      | ~ m1_pre_topc(X3,X4)
% 7.49/1.49      | ~ m1_pre_topc(X1,X4)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.49/1.49      | v2_struct_0(X4)
% 7.49/1.49      | v2_struct_0(X2)
% 7.49/1.49      | ~ l1_pre_topc(X4)
% 7.49/1.49      | ~ l1_pre_topc(X2)
% 7.49/1.49      | ~ v2_pre_topc(X4)
% 7.49/1.49      | ~ v2_pre_topc(X2)
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 7.49/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1080,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.49/1.49      | ~ m1_pre_topc(X0_51,X2_51)
% 7.49/1.49      | ~ m1_pre_topc(X3_51,X2_51)
% 7.49/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.49/1.49      | v2_struct_0(X1_51)
% 7.49/1.49      | v2_struct_0(X2_51)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | ~ l1_pre_topc(X2_51)
% 7.49/1.49      | ~ v2_pre_topc(X1_51)
% 7.49/1.49      | ~ v2_pre_topc(X2_51)
% 7.49/1.49      | ~ v1_funct_1(X0_52)
% 7.49/1.49      | v1_funct_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52)) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1730,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(sK1))
% 7.49/1.49      | ~ m1_pre_topc(X0_51,X1_51)
% 7.49/1.49      | ~ m1_pre_topc(X2_51,X1_51)
% 7.49/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
% 7.49/1.49      | v2_struct_0(X1_51)
% 7.49/1.49      | v2_struct_0(sK1)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | ~ l1_pre_topc(sK1)
% 7.49/1.49      | ~ v2_pre_topc(X1_51)
% 7.49/1.49      | ~ v2_pre_topc(sK1)
% 7.49/1.49      | ~ v1_funct_1(X0_52)
% 7.49/1.49      | v1_funct_1(k3_tmap_1(X1_51,sK1,X0_51,X2_51,X0_52)) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1080]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1876,plain,
% 7.49/1.49      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.49/1.49      | ~ m1_pre_topc(X0_51,X1_51)
% 7.49/1.49      | ~ m1_pre_topc(sK2,X1_51)
% 7.49/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.49/1.49      | v2_struct_0(X1_51)
% 7.49/1.49      | v2_struct_0(sK1)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | ~ l1_pre_topc(sK1)
% 7.49/1.49      | ~ v2_pre_topc(X1_51)
% 7.49/1.49      | ~ v2_pre_topc(sK1)
% 7.49/1.49      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3))
% 7.49/1.49      | ~ v1_funct_1(sK3) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1730]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3652,plain,
% 7.49/1.49      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.49/1.49      | ~ m1_pre_topc(sK2,X0_51)
% 7.49/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.49/1.49      | v2_struct_0(X0_51)
% 7.49/1.49      | v2_struct_0(sK1)
% 7.49/1.49      | ~ l1_pre_topc(X0_51)
% 7.49/1.49      | ~ l1_pre_topc(sK1)
% 7.49/1.49      | ~ v2_pre_topc(X0_51)
% 7.49/1.49      | ~ v2_pre_topc(sK1)
% 7.49/1.49      | v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3))
% 7.49/1.49      | ~ v1_funct_1(sK3) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1876]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3653,plain,
% 7.49/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3)) = iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_3652]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4360,plain,
% 7.49/1.49      ( v2_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
% 7.49/1.49      | v1_funct_2(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_4355,c_33,c_34,c_35,c_36,c_38,c_39,c_40,c_3653]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4361,plain,
% 7.49/1.49      ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
% 7.49/1.49      | v1_funct_2(k3_tmap_1(X0_51,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X0_51) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_4360]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4366,plain,
% 7.49/1.49      ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
% 7.49/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1656,c_4361]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4581,plain,
% 7.49/1.49      ( l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | v2_pre_topc(X0_51) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_4366,c_33,c_34,c_35,c_38,c_39,c_40]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4582,plain,
% 7.49/1.49      ( k3_tmap_1(X0_51,sK1,sK2,sK2,sK3) = sK3
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X0_51) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_4581]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4587,plain,
% 7.49/1.49      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1674,c_4582]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4368,plain,
% 7.49/1.49      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
% 7.49/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.49/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_4366]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4592,plain,
% 7.49/1.49      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_4587,c_33,c_34,c_35,c_37,c_38,c_39,c_40,c_4368]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4930,plain,
% 7.49/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.49/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.49/1.49      inference(light_normalisation,[status(thm)],[c_4928,c_4188,c_4592]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2584,plain,
% 7.49/1.49      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1075]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2585,plain,
% 7.49/1.49      ( m1_pre_topc(sK2,sK2) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_2584]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4936,plain,
% 7.49/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_4930,c_33,c_34,c_35,c_37,c_1857,c_2585]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_18,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 7.49/1.49      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 7.49/1.49      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 7.49/1.49      | ~ m1_pre_topc(X0,X2)
% 7.49/1.49      | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
% 7.49/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.49/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.49/1.49      | v2_struct_0(X1)
% 7.49/1.49      | v2_struct_0(X2)
% 7.49/1.49      | v2_struct_0(X0)
% 7.49/1.49      | ~ l1_pre_topc(X1)
% 7.49/1.49      | ~ l1_pre_topc(X2)
% 7.49/1.49      | ~ v2_pre_topc(X1)
% 7.49/1.49      | ~ v2_pre_topc(X2)
% 7.49/1.49      | ~ v1_funct_1(X3)
% 7.49/1.49      | ~ v1_funct_1(X4) ),
% 7.49/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1073,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52)
% 7.49/1.49      | ~ v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.49/1.49      | ~ v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51))
% 7.49/1.49      | ~ m1_pre_topc(X0_51,X2_51)
% 7.49/1.49      | r2_hidden(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X0_51))
% 7.49/1.49      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.49/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
% 7.49/1.49      | v2_struct_0(X1_51)
% 7.49/1.49      | v2_struct_0(X0_51)
% 7.49/1.49      | v2_struct_0(X2_51)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | ~ l1_pre_topc(X2_51)
% 7.49/1.49      | ~ v2_pre_topc(X1_51)
% 7.49/1.49      | ~ v2_pre_topc(X2_51)
% 7.49/1.49      | ~ v1_funct_1(X0_52)
% 7.49/1.49      | ~ v1_funct_1(X1_52) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1664,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 7.49/1.49      | r2_hidden(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X0_51)) = iProver_top
% 7.49/1.49      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X2_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(X2_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X2_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.49/1.49      | v1_funct_1(X1_52) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1073]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4940,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.49/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | v2_struct_0(sK2) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_4936,c_1664]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_6403,plain,
% 7.49/1.49      ( v1_funct_1(X0_52) != iProver_top
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_4940,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_1857,
% 7.49/1.49                 c_2113,c_2585]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_6404,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_6403]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_24,negated_conjecture,
% 7.49/1.49      ( ~ r2_hidden(X0,u1_struct_0(sK2))
% 7.49/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.49/1.49      | k1_funct_1(sK3,X0) = X0 ),
% 7.49/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1067,negated_conjecture,
% 7.49/1.49      ( ~ r2_hidden(X0_52,u1_struct_0(sK2))
% 7.49/1.49      | ~ m1_subset_1(X0_52,u1_struct_0(sK1))
% 7.49/1.49      | k1_funct_1(sK3,X0_52) = X0_52 ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_24]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1670,plain,
% 7.49/1.49      ( k1_funct_1(sK3,X0_52) = X0_52
% 7.49/1.49      | r2_hidden(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,u1_struct_0(sK1)) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1067]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_6407,plain,
% 7.49/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_6404,c_1670]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_19,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 7.49/1.49      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 7.49/1.49      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 7.49/1.49      | ~ m1_pre_topc(X0,X2)
% 7.49/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.49/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.49/1.49      | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2))
% 7.49/1.49      | v2_struct_0(X1)
% 7.49/1.49      | v2_struct_0(X2)
% 7.49/1.49      | v2_struct_0(X0)
% 7.49/1.49      | ~ l1_pre_topc(X1)
% 7.49/1.49      | ~ l1_pre_topc(X2)
% 7.49/1.49      | ~ v2_pre_topc(X1)
% 7.49/1.49      | ~ v2_pre_topc(X2)
% 7.49/1.49      | ~ v1_funct_1(X3)
% 7.49/1.49      | ~ v1_funct_1(X4) ),
% 7.49/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1072,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52)
% 7.49/1.49      | ~ v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.49/1.49      | ~ v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51))
% 7.49/1.49      | ~ m1_pre_topc(X0_51,X2_51)
% 7.49/1.49      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.49/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
% 7.49/1.49      | m1_subset_1(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X2_51))
% 7.49/1.49      | v2_struct_0(X1_51)
% 7.49/1.49      | v2_struct_0(X0_51)
% 7.49/1.49      | v2_struct_0(X2_51)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | ~ l1_pre_topc(X2_51)
% 7.49/1.49      | ~ v2_pre_topc(X1_51)
% 7.49/1.49      | ~ v2_pre_topc(X2_51)
% 7.49/1.49      | ~ v1_funct_1(X0_52)
% 7.49/1.49      | ~ v1_funct_1(X1_52) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_19]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1665,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 7.49/1.49      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X2_51)) = iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X2_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(X2_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X2_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.49/1.49      | v1_funct_1(X1_52) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1072]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_4939,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 7.49/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | v2_struct_0(sK2) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_4936,c_1665]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5060,plain,
% 7.49/1.49      ( v1_funct_1(X0_52) != iProver_top
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_4939,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_1857,
% 7.49/1.49                 c_2113,c_2585]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5061,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_5060]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_6,plain,
% 7.49/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.49/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.49/1.49      | m1_subset_1(X2,u1_struct_0(X1))
% 7.49/1.49      | v2_struct_0(X1)
% 7.49/1.49      | v2_struct_0(X0)
% 7.49/1.49      | ~ l1_pre_topc(X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1085,plain,
% 7.49/1.49      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.49/1.49      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 7.49/1.49      | m1_subset_1(X0_52,u1_struct_0(X1_51))
% 7.49/1.49      | v2_struct_0(X1_51)
% 7.49/1.49      | v2_struct_0(X0_51)
% 7.49/1.49      | ~ l1_pre_topc(X1_51) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1652,plain,
% 7.49/1.49      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,u1_struct_0(X1_51)) = iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1085]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5065,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) = iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | v2_struct_0(sK2) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_5061,c_1652]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5248,plain,
% 7.49/1.49      ( v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) = iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_5065,c_36]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5249,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) = iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_5248]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5254,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X1_51)) = iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_5249,c_1652]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1128,plain,
% 7.49/1.49      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1086]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5350,plain,
% 7.49/1.49      ( v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X1_51)) = iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_5254,c_1128]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5351,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X1_51)) = iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_5350]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5354,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | v2_struct_0(sK2) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1674,c_5351]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5358,plain,
% 7.49/1.49      ( m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_5354,c_33,c_35,c_36,c_37,c_1857,c_2585]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5359,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_5358]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_6462,plain,
% 7.49/1.49      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_6407,c_5359]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_6463,plain,
% 7.49/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_6462]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_6467,plain,
% 7.49/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.49/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1658,c_6463]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_23,negated_conjecture,
% 7.49/1.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
% 7.49/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1093,plain,( X0_52 = X0_52 ),theory(equality) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1116,plain,
% 7.49/1.49      ( sK3 = sK3 ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1093]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2,plain,
% 7.49/1.49      ( r2_funct_2(X0,X1,X2,X2)
% 7.49/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.49/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.49/1.49      | ~ v1_funct_1(X2) ),
% 7.49/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1089,plain,
% 7.49/1.49      ( r2_funct_2(X0_52,X1_52,X2_52,X2_52)
% 7.49/1.49      | ~ v1_funct_2(X2_52,X0_52,X1_52)
% 7.49/1.49      | ~ m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 7.49/1.49      | ~ v1_funct_1(X2_52) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2558,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 7.49/1.49      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.49/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.49/1.49      | ~ v1_funct_1(sK3) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1089]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2706,plain,
% 7.49/1.49      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1093]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1103,plain,
% 7.49/1.49      ( ~ r2_funct_2(X0_52,X1_52,X2_52,X3_52)
% 7.49/1.49      | r2_funct_2(X4_52,X5_52,X6_52,X7_52)
% 7.49/1.49      | X4_52 != X0_52
% 7.49/1.49      | X5_52 != X1_52
% 7.49/1.49      | X6_52 != X2_52
% 7.49/1.49      | X7_52 != X3_52 ),
% 7.49/1.49      theory(equality) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1837,plain,
% 7.49/1.49      ( ~ r2_funct_2(X0_52,X1_52,X2_52,X3_52)
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
% 7.49/1.49      | k4_tmap_1(sK1,sK2) != X2_52
% 7.49/1.49      | u1_struct_0(sK1) != X1_52
% 7.49/1.49      | u1_struct_0(sK2) != X0_52
% 7.49/1.49      | sK3 != X3_52 ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1103]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3478,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
% 7.49/1.49      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3)
% 7.49/1.49      | k4_tmap_1(sK1,sK2) != sK3
% 7.49/1.49      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 7.49/1.49      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 7.49/1.49      | sK3 != sK3 ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1837]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_14,plain,
% 7.49/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.49/1.49      | v2_struct_0(X1)
% 7.49/1.49      | ~ l1_pre_topc(X1)
% 7.49/1.49      | ~ v2_pre_topc(X1)
% 7.49/1.49      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 7.49/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1077,plain,
% 7.49/1.49      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.49/1.49      | v2_struct_0(X1_51)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | ~ v2_pre_topc(X1_51)
% 7.49/1.49      | v1_funct_1(k4_tmap_1(X1_51,X0_51)) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3580,plain,
% 7.49/1.49      ( ~ m1_pre_topc(sK2,sK1)
% 7.49/1.49      | v2_struct_0(sK1)
% 7.49/1.49      | ~ l1_pre_topc(sK1)
% 7.49/1.49      | ~ v2_pre_topc(sK1)
% 7.49/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1077]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3581,plain,
% 7.49/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_3580]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3589,plain,
% 7.49/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.49/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1658,c_3585]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3592,plain,
% 7.49/1.49      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.49/1.49      | k4_tmap_1(sK1,sK2) = sK3 ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_3589,c_33,c_34,c_35,c_37,c_3581]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3593,plain,
% 7.49/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.49/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_3592]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3650,plain,
% 7.49/1.49      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1093]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_13,plain,
% 7.49/1.49      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 7.49/1.49      | ~ m1_pre_topc(X1,X0)
% 7.49/1.49      | v2_struct_0(X0)
% 7.49/1.49      | ~ l1_pre_topc(X0)
% 7.49/1.49      | ~ v2_pre_topc(X0) ),
% 7.49/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1078,plain,
% 7.49/1.49      ( v1_funct_2(k4_tmap_1(X0_51,X1_51),u1_struct_0(X1_51),u1_struct_0(X0_51))
% 7.49/1.49      | ~ m1_pre_topc(X1_51,X0_51)
% 7.49/1.49      | v2_struct_0(X0_51)
% 7.49/1.49      | ~ l1_pre_topc(X0_51)
% 7.49/1.49      | ~ v2_pre_topc(X0_51) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5412,plain,
% 7.49/1.49      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.49/1.49      | ~ m1_pre_topc(sK2,sK1)
% 7.49/1.49      | v2_struct_0(sK1)
% 7.49/1.49      | ~ l1_pre_topc(sK1)
% 7.49/1.49      | ~ v2_pre_topc(sK1) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1078]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5413,plain,
% 7.49/1.49      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_5412]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_6474,plain,
% 7.49/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_6467,c_33,c_34,c_35,c_37,c_27,c_26,c_25,c_23,c_1116,
% 7.49/1.49                 c_2558,c_2706,c_3478,c_3581,c_3593,c_3650,c_5413]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1659,plain,
% 7.49/1.49      ( v1_funct_2(k4_tmap_1(X0_51,X1_51),u1_struct_0(X1_51),u1_struct_0(X0_51)) = iProver_top
% 7.49/1.49      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X0_51) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1078]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.49/1.49      | ~ m1_subset_1(X3,X1)
% 7.49/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.49/1.49      | ~ v1_funct_1(X0)
% 7.49/1.49      | v1_xboole_0(X1)
% 7.49/1.49      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.49/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1090,plain,
% 7.49/1.49      ( ~ v1_funct_2(X0_52,X1_52,X2_52)
% 7.49/1.49      | ~ m1_subset_1(X3_52,X1_52)
% 7.49/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 7.49/1.49      | ~ v1_funct_1(X0_52)
% 7.49/1.49      | v1_xboole_0(X1_52)
% 7.49/1.49      | k3_funct_2(X1_52,X2_52,X0_52,X3_52) = k1_funct_1(X0_52,X3_52) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1647,plain,
% 7.49/1.49      ( k3_funct_2(X0_52,X1_52,X2_52,X3_52) = k1_funct_1(X2_52,X3_52)
% 7.49/1.49      | v1_funct_2(X2_52,X0_52,X1_52) != iProver_top
% 7.49/1.49      | m1_subset_1(X3_52,X0_52) != iProver_top
% 7.49/1.49      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 7.49/1.49      | v1_funct_1(X2_52) != iProver_top
% 7.49/1.49      | v1_xboole_0(X0_52) = iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1090]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2738,plain,
% 7.49/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
% 7.49/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top
% 7.49/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1671,c_1647]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3187,plain,
% 7.49/1.49      ( m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.49/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
% 7.49/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_2738,c_38,c_39]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_3188,plain,
% 7.49/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
% 7.49/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.49/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_3187]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5066,plain,
% 7.49/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52))
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.49/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_5061,c_3188]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5131,plain,
% 7.49/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.49/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.49/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1658,c_5066]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5138,plain,
% 7.49/1.49      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 7.49/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_5131,c_33,c_34,c_35,c_37,c_27,c_26,c_25,c_23,c_1116,
% 7.49/1.49                 c_2558,c_2706,c_3478,c_3581,c_3593,c_3650]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5139,plain,
% 7.49/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 7.49/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_5138]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5142,plain,
% 7.49/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 7.49/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1659,c_5139]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5243,plain,
% 7.49/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 7.49/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_5142,c_33,c_34,c_35,c_37]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_6476,plain,
% 7.49/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.49/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.49/1.49      inference(demodulation,[status(thm)],[c_6474,c_5243]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_15,plain,
% 7.49/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.49/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.49/1.49      | ~ l1_pre_topc(X1) ),
% 7.49/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1076,plain,
% 7.49/1.49      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.49/1.49      | m1_subset_1(u1_struct_0(X0_51),k1_zfmisc_1(u1_struct_0(X1_51)))
% 7.49/1.49      | ~ l1_pre_topc(X1_51) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_15]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1661,plain,
% 7.49/1.49      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.49/1.49      | m1_subset_1(u1_struct_0(X0_51),k1_zfmisc_1(u1_struct_0(X1_51))) = iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1076]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_0,plain,
% 7.49/1.49      ( ~ r2_hidden(X0,X1)
% 7.49/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 7.49/1.49      | ~ v1_xboole_0(X2) ),
% 7.49/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1091,plain,
% 7.49/1.49      ( ~ r2_hidden(X0_52,X1_52)
% 7.49/1.49      | ~ m1_subset_1(X1_52,k1_zfmisc_1(X2_52))
% 7.49/1.49      | ~ v1_xboole_0(X2_52) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1646,plain,
% 7.49/1.49      ( r2_hidden(X0_52,X1_52) != iProver_top
% 7.49/1.49      | m1_subset_1(X1_52,k1_zfmisc_1(X2_52)) != iProver_top
% 7.49/1.49      | v1_xboole_0(X2_52) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1091]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_2260,plain,
% 7.49/1.49      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.49/1.49      | r2_hidden(X0_52,u1_struct_0(X0_51)) != iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v1_xboole_0(u1_struct_0(X1_51)) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1661,c_1646]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_6408,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.49/1.49      | v1_xboole_0(u1_struct_0(X0_51)) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_6404,c_2260]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7343,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.49/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.49/1.49      | v1_xboole_0(u1_struct_0(X0_51)) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1658,c_6408]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7458,plain,
% 7.49/1.49      ( l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | v1_xboole_0(u1_struct_0(X0_51)) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_7343,c_33,c_34,c_35,c_37,c_27,c_26,c_25,c_23,c_1116,
% 7.49/1.49                 c_2558,c_2706,c_3478,c_3581,c_3593,c_3650,c_5413]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7459,plain,
% 7.49/1.49      ( m1_pre_topc(sK2,X0_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v1_xboole_0(u1_struct_0(X0_51)) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_7458]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7465,plain,
% 7.49/1.49      ( l1_pre_topc(sK2) != iProver_top
% 7.49/1.49      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1662,c_7459]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7543,plain,
% 7.49/1.49      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_7465,c_35,c_37,c_1857]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7547,plain,
% 7.49/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_6476,c_7543]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_17,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 7.49/1.49      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 7.49/1.49      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 7.49/1.49      | ~ m1_pre_topc(X0,X2)
% 7.49/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.49/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.49/1.49      | v2_struct_0(X1)
% 7.49/1.49      | v2_struct_0(X2)
% 7.49/1.49      | v2_struct_0(X0)
% 7.49/1.49      | ~ l1_pre_topc(X1)
% 7.49/1.49      | ~ l1_pre_topc(X2)
% 7.49/1.49      | ~ v2_pre_topc(X1)
% 7.49/1.49      | ~ v2_pre_topc(X2)
% 7.49/1.49      | ~ v1_funct_1(X3)
% 7.49/1.49      | ~ v1_funct_1(X4)
% 7.49/1.49      | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK0(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK0(X1,X2,X0,X3,X4)) ),
% 7.49/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1074,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52)
% 7.49/1.49      | ~ v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.49/1.49      | ~ v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51))
% 7.49/1.49      | ~ m1_pre_topc(X0_51,X2_51)
% 7.49/1.49      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.49/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
% 7.49/1.49      | v2_struct_0(X1_51)
% 7.49/1.49      | v2_struct_0(X0_51)
% 7.49/1.49      | v2_struct_0(X2_51)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | ~ l1_pre_topc(X2_51)
% 7.49/1.49      | ~ v2_pre_topc(X1_51)
% 7.49/1.49      | ~ v2_pre_topc(X2_51)
% 7.49/1.49      | ~ v1_funct_1(X0_52)
% 7.49/1.49      | ~ v1_funct_1(X1_52)
% 7.49/1.49      | k3_funct_2(u1_struct_0(X2_51),u1_struct_0(X1_51),X0_52,sK0(X1_51,X2_51,X0_51,X0_52,X1_52)) != k1_funct_1(X1_52,sK0(X1_51,X2_51,X0_51,X0_52,X1_52)) ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_17]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1663,plain,
% 7.49/1.49      ( k3_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,sK0(X1_51,X0_51,X2_51,X0_52,X1_52)) != k1_funct_1(X1_52,sK0(X1_51,X0_51,X2_51,X0_52,X1_52))
% 7.49/1.49      | r2_funct_2(u1_struct_0(X2_51),u1_struct_0(X1_51),k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X1_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 7.49/1.49      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.49/1.49      | v2_struct_0(X2_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.49/1.49      | v1_funct_1(X1_52) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1074]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7659,plain,
% 7.49/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),k4_tmap_1(sK1,sK2)) = iProver_top
% 7.49/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.49/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | v2_struct_0(sK2) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_7547,c_1663]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_22,plain,
% 7.49/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.49/1.49      | ~ r2_hidden(X2,u1_struct_0(X0))
% 7.49/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.49/1.49      | v2_struct_0(X1)
% 7.49/1.49      | v2_struct_0(X0)
% 7.49/1.49      | ~ l1_pre_topc(X1)
% 7.49/1.49      | ~ v2_pre_topc(X1)
% 7.49/1.49      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 7.49/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1069,plain,
% 7.49/1.49      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.49/1.49      | ~ r2_hidden(X0_52,u1_struct_0(X0_51))
% 7.49/1.49      | ~ m1_subset_1(X0_52,u1_struct_0(X1_51))
% 7.49/1.49      | v2_struct_0(X1_51)
% 7.49/1.49      | v2_struct_0(X0_51)
% 7.49/1.49      | ~ l1_pre_topc(X1_51)
% 7.49/1.49      | ~ v2_pre_topc(X1_51)
% 7.49/1.49      | k1_funct_1(k4_tmap_1(X1_51,X0_51),X0_52) = X0_52 ),
% 7.49/1.49      inference(subtyping,[status(esa)],[c_22]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_1668,plain,
% 7.49/1.49      ( k1_funct_1(k4_tmap_1(X0_51,X1_51),X0_52) = X0_52
% 7.49/1.49      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 7.49/1.49      | r2_hidden(X0_52,u1_struct_0(X1_51)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
% 7.49/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.49/1.49      | v2_pre_topc(X0_51) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_1069]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5363,plain,
% 7.49/1.49      ( k1_funct_1(k4_tmap_1(sK1,X0_51),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,sK1) != iProver_top
% 7.49/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_5359,c_1668]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5612,plain,
% 7.49/1.49      ( v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,sK1) != iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | k1_funct_1(k4_tmap_1(sK1,X0_51),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_5363,c_33,c_34,c_35]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5613,plain,
% 7.49/1.49      ( k1_funct_1(k4_tmap_1(sK1,X0_51),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(X0_51,sK1) != iProver_top
% 7.49/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_5612]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_6409,plain,
% 7.49/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v2_struct_0(sK2) = iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_6404,c_5613]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7149,plain,
% 7.49/1.49      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_6409,c_36,c_37]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7150,plain,
% 7.49/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.49/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.49/1.49      inference(renaming,[status(thm)],[c_7149]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7154,plain,
% 7.49/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.49/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.49/1.49      inference(superposition,[status(thm)],[c_1658,c_7150]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7605,plain,
% 7.49/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 7.49/1.49      inference(global_propositional_subsumption,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_7154,c_33,c_34,c_35,c_37,c_27,c_26,c_25,c_23,c_1116,
% 7.49/1.49                 c_2558,c_2706,c_3478,c_3581,c_3593,c_3650,c_5413]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7660,plain,
% 7.49/1.49      ( sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.49/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.49/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.49/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | v2_struct_0(sK2) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.49      inference(light_normalisation,[status(thm)],[c_7659,c_4936,c_7605]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_7661,plain,
% 7.49/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.49/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.49/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.49/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | v2_struct_0(sK2) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.49/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.49/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.49/1.49      inference(equality_resolution_simp,[status(thm)],[c_7660]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5573,plain,
% 7.49/1.49      ( ~ m1_pre_topc(sK2,sK1)
% 7.49/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.49/1.49      | v2_struct_0(sK1)
% 7.49/1.49      | ~ l1_pre_topc(sK1)
% 7.49/1.49      | ~ v2_pre_topc(sK1) ),
% 7.49/1.49      inference(instantiation,[status(thm)],[c_1079]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(c_5574,plain,
% 7.49/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.49/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 7.49/1.49      | v2_struct_0(sK1) = iProver_top
% 7.49/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.49/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.49/1.49      inference(predicate_to_equality,[status(thm)],[c_5573]) ).
% 7.49/1.49  
% 7.49/1.49  cnf(contradiction,plain,
% 7.49/1.49      ( $false ),
% 7.49/1.49      inference(minisat,
% 7.49/1.49                [status(thm)],
% 7.49/1.49                [c_7661,c_5574,c_5413,c_3650,c_3593,c_3581,c_3478,c_2706,
% 7.49/1.49                 c_2585,c_2558,c_2113,c_1857,c_1116,c_23,c_40,c_25,c_39,
% 7.49/1.49                 c_26,c_38,c_27,c_37,c_36,c_35,c_34,c_33]) ).
% 7.49/1.49  
% 7.49/1.49  
% 7.49/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.49/1.49  
% 7.49/1.49  ------                               Statistics
% 7.49/1.49  
% 7.49/1.49  ------ General
% 7.49/1.49  
% 7.49/1.49  abstr_ref_over_cycles:                  0
% 7.49/1.49  abstr_ref_under_cycles:                 0
% 7.49/1.49  gc_basic_clause_elim:                   0
% 7.49/1.49  forced_gc_time:                         0
% 7.49/1.49  parsing_time:                           0.012
% 7.49/1.49  unif_index_cands_time:                  0.
% 7.49/1.49  unif_index_add_time:                    0.
% 7.49/1.49  orderings_time:                         0.
% 7.49/1.49  out_proof_time:                         0.023
% 7.49/1.49  total_time:                             0.542
% 7.49/1.49  num_of_symbols:                         56
% 7.49/1.49  num_of_terms:                           16071
% 7.49/1.49  
% 7.49/1.49  ------ Preprocessing
% 7.49/1.49  
% 7.49/1.49  num_of_splits:                          0
% 7.49/1.49  num_of_split_atoms:                     0
% 7.49/1.49  num_of_reused_defs:                     0
% 7.49/1.49  num_eq_ax_congr_red:                    42
% 7.49/1.49  num_of_sem_filtered_clauses:            1
% 7.49/1.49  num_of_subtypes:                        2
% 7.49/1.49  monotx_restored_types:                  0
% 7.49/1.49  sat_num_of_epr_types:                   0
% 7.49/1.49  sat_num_of_non_cyclic_types:            0
% 7.49/1.49  sat_guarded_non_collapsed_types:        1
% 7.49/1.49  num_pure_diseq_elim:                    0
% 7.49/1.49  simp_replaced_by:                       0
% 7.49/1.49  res_preprocessed:                       124
% 7.49/1.49  prep_upred:                             0
% 7.49/1.49  prep_unflattend:                        32
% 7.49/1.49  smt_new_axioms:                         0
% 7.49/1.49  pred_elim_cands:                        10
% 7.49/1.49  pred_elim:                              0
% 7.49/1.49  pred_elim_cl:                           0
% 7.49/1.49  pred_elim_cycles:                       3
% 7.49/1.49  merged_defs:                            0
% 7.49/1.49  merged_defs_ncl:                        0
% 7.49/1.49  bin_hyper_res:                          0
% 7.49/1.49  prep_cycles:                            3
% 7.49/1.49  pred_elim_time:                         0.026
% 7.49/1.49  splitting_time:                         0.
% 7.49/1.49  sem_filter_time:                        0.
% 7.49/1.49  monotx_time:                            0.
% 7.49/1.49  subtype_inf_time:                       0.001
% 7.49/1.49  
% 7.49/1.49  ------ Problem properties
% 7.49/1.49  
% 7.49/1.49  clauses:                                33
% 7.49/1.49  conjectures:                            10
% 7.49/1.49  epr:                                    10
% 7.49/1.49  horn:                                   18
% 7.49/1.49  ground:                                 9
% 7.49/1.49  unary:                                  9
% 7.49/1.49  binary:                                 1
% 7.49/1.49  lits:                                   199
% 7.49/1.49  lits_eq:                                7
% 7.49/1.49  fd_pure:                                0
% 7.49/1.49  fd_pseudo:                              0
% 7.49/1.49  fd_cond:                                0
% 7.49/1.49  fd_pseudo_cond:                         1
% 7.49/1.49  ac_symbols:                             0
% 7.49/1.49  
% 7.49/1.49  ------ Propositional Solver
% 7.49/1.49  
% 7.49/1.49  prop_solver_calls:                      24
% 7.49/1.49  prop_fast_solver_calls:                 2727
% 7.49/1.49  smt_solver_calls:                       0
% 7.49/1.49  smt_fast_solver_calls:                  0
% 7.49/1.49  prop_num_of_clauses:                    4095
% 7.49/1.49  prop_preprocess_simplified:             8344
% 7.49/1.49  prop_fo_subsumed:                       191
% 7.49/1.49  prop_solver_time:                       0.
% 7.49/1.49  smt_solver_time:                        0.
% 7.49/1.49  smt_fast_solver_time:                   0.
% 7.49/1.49  prop_fast_solver_time:                  0.
% 7.49/1.49  prop_unsat_core_time:                   0.
% 7.49/1.49  
% 7.49/1.49  ------ QBF
% 7.49/1.49  
% 7.49/1.49  qbf_q_res:                              0
% 7.49/1.49  qbf_num_tautologies:                    0
% 7.49/1.49  qbf_prep_cycles:                        0
% 7.49/1.49  
% 7.49/1.49  ------ BMC1
% 7.49/1.49  
% 7.49/1.49  bmc1_current_bound:                     -1
% 7.49/1.49  bmc1_last_solved_bound:                 -1
% 7.49/1.49  bmc1_unsat_core_size:                   -1
% 7.49/1.49  bmc1_unsat_core_parents_size:           -1
% 7.49/1.49  bmc1_merge_next_fun:                    0
% 7.49/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.49/1.49  
% 7.49/1.49  ------ Instantiation
% 7.49/1.49  
% 7.49/1.49  inst_num_of_clauses:                    938
% 7.49/1.49  inst_num_in_passive:                    101
% 7.49/1.49  inst_num_in_active:                     490
% 7.49/1.49  inst_num_in_unprocessed:                347
% 7.49/1.49  inst_num_of_loops:                      530
% 7.49/1.49  inst_num_of_learning_restarts:          0
% 7.49/1.49  inst_num_moves_active_passive:          38
% 7.49/1.49  inst_lit_activity:                      0
% 7.49/1.49  inst_lit_activity_moves:                0
% 7.49/1.49  inst_num_tautologies:                   0
% 7.49/1.49  inst_num_prop_implied:                  0
% 7.49/1.49  inst_num_existing_simplified:           0
% 7.49/1.49  inst_num_eq_res_simplified:             0
% 7.49/1.49  inst_num_child_elim:                    0
% 7.49/1.49  inst_num_of_dismatching_blockings:      178
% 7.49/1.49  inst_num_of_non_proper_insts:           977
% 7.49/1.49  inst_num_of_duplicates:                 0
% 7.49/1.49  inst_inst_num_from_inst_to_res:         0
% 7.49/1.49  inst_dismatching_checking_time:         0.
% 7.49/1.49  
% 7.49/1.49  ------ Resolution
% 7.49/1.49  
% 7.49/1.49  res_num_of_clauses:                     0
% 7.49/1.49  res_num_in_passive:                     0
% 7.49/1.49  res_num_in_active:                      0
% 7.49/1.49  res_num_of_loops:                       127
% 7.49/1.49  res_forward_subset_subsumed:            26
% 7.49/1.49  res_backward_subset_subsumed:           0
% 7.49/1.49  res_forward_subsumed:                   0
% 7.49/1.49  res_backward_subsumed:                  0
% 7.49/1.49  res_forward_subsumption_resolution:     0
% 7.49/1.49  res_backward_subsumption_resolution:    0
% 7.49/1.49  res_clause_to_clause_subsumption:       566
% 7.49/1.49  res_orphan_elimination:                 0
% 7.49/1.49  res_tautology_del:                      20
% 7.49/1.49  res_num_eq_res_simplified:              0
% 7.49/1.49  res_num_sel_changes:                    0
% 7.49/1.49  res_moves_from_active_to_pass:          0
% 7.49/1.49  
% 7.49/1.49  ------ Superposition
% 7.49/1.49  
% 7.49/1.49  sup_time_total:                         0.
% 7.49/1.49  sup_time_generating:                    0.
% 7.49/1.49  sup_time_sim_full:                      0.
% 7.49/1.49  sup_time_sim_immed:                     0.
% 7.49/1.49  
% 7.49/1.49  sup_num_of_clauses:                     121
% 7.49/1.49  sup_num_in_active:                      96
% 7.49/1.49  sup_num_in_passive:                     25
% 7.49/1.50  sup_num_of_loops:                       104
% 7.49/1.50  sup_fw_superposition:                   89
% 7.49/1.50  sup_bw_superposition:                   47
% 7.49/1.50  sup_immediate_simplified:               31
% 7.49/1.50  sup_given_eliminated:                   0
% 7.49/1.50  comparisons_done:                       0
% 7.49/1.50  comparisons_avoided:                    6
% 7.49/1.50  
% 7.49/1.50  ------ Simplifications
% 7.49/1.50  
% 7.49/1.50  
% 7.49/1.50  sim_fw_subset_subsumed:                 21
% 7.49/1.50  sim_bw_subset_subsumed:                 2
% 7.49/1.50  sim_fw_subsumed:                        7
% 7.49/1.50  sim_bw_subsumed:                        5
% 7.49/1.50  sim_fw_subsumption_res:                 0
% 7.49/1.50  sim_bw_subsumption_res:                 0
% 7.49/1.50  sim_tautology_del:                      7
% 7.49/1.50  sim_eq_tautology_del:                   3
% 7.49/1.50  sim_eq_res_simp:                        1
% 7.49/1.50  sim_fw_demodulated:                     0
% 7.49/1.50  sim_bw_demodulated:                     2
% 7.49/1.50  sim_light_normalised:                   3
% 7.49/1.50  sim_joinable_taut:                      0
% 7.49/1.50  sim_joinable_simp:                      0
% 7.49/1.50  sim_ac_normalised:                      0
% 7.49/1.50  sim_smt_subsumption:                    0
% 7.49/1.50  
%------------------------------------------------------------------------------
