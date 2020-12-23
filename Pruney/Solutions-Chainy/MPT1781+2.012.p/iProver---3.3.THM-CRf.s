%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:45 EST 2020

% Result     : Theorem 4.02s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :  274 (44234 expanded)
%              Number of clauses        :  195 (12018 expanded)
%              Number of leaves         :   20 (13624 expanded)
%              Depth                    :   39
%              Number of atoms          : 2035 (431018 expanded)
%              Number of equality atoms :  886 (53240 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal clause size      :   24 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f50,f49,f48])).

fof(f77,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
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

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f29])).

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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f46,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
        & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f46])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
      | ~ r2_hidden(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f53])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f47])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1037,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | m1_subset_1(k4_tmap_1(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X1_50) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1578,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(k4_tmap_1(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1037])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1021,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1594,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1021])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1024,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1591,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1024])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f58])).

cnf(c_1041,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X0_50)
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_pre_topc(X2_50,X3_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X3_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1574,plain,
    ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1041])).

cnf(c_3512,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_1574])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_31,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_33,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_37,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4365,plain,
    ( l1_pre_topc(X1_50) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3)
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3512,c_31,c_32,c_33,c_36,c_37])).

cnf(c_4366,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3)
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_4365])).

cnf(c_4371,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_4366])).

cnf(c_13,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1034,plain,
    ( m1_pre_topc(X0_50,X0_50)
    | ~ l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1581,plain,
    ( m1_pre_topc(X0_50,X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1034])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f57])).

cnf(c_1042,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X2_50,X0_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X0_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X0_50)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1573,plain,
    ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50)
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1042])).

cnf(c_3229,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k2_tmap_1(sK2,sK1,sK3,X0_50)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_1573])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_35,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1044,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | l1_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1835,plain,
    ( ~ m1_pre_topc(sK2,X0_50)
    | ~ l1_pre_topc(X0_50)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1044])).

cnf(c_1836,plain,
    ( m1_pre_topc(sK2,X0_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1835])).

cnf(c_1838,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1836])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1045,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X1_50)
    | v2_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2083,plain,
    ( ~ m1_pre_topc(sK2,X0_50)
    | ~ l1_pre_topc(X0_50)
    | ~ v2_pre_topc(X0_50)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_2084,plain,
    ( m1_pre_topc(sK2,X0_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2083])).

cnf(c_2086,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2084])).

cnf(c_3238,plain,
    ( m1_pre_topc(X0_50,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k2_tmap_1(sK2,sK1,sK3,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3229,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_1838,c_2086])).

cnf(c_3239,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k2_tmap_1(sK2,sK1,sK3,X0_50)
    | m1_pre_topc(X0_50,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3238])).

cnf(c_3244,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1581,c_3239])).

cnf(c_1837,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1835])).

cnf(c_2085,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2083])).

cnf(c_1660,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
    | ~ m1_pre_topc(X1_50,X0_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
    | v2_struct_0(X0_50)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_50)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_50)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(sK1),X0_51,u1_struct_0(X1_50)) = k2_tmap_1(X0_50,sK1,X0_51,X1_50) ),
    inference(instantiation,[status(thm)],[c_1042])).

cnf(c_1762,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_50,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k2_tmap_1(sK2,sK1,sK3,X0_50) ),
    inference(instantiation,[status(thm)],[c_1660])).

cnf(c_2181,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_2874,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_3401,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3244,c_30,c_29,c_28,c_27,c_26,c_25,c_24,c_23,c_1837,c_2085,c_2181,c_2874])).

cnf(c_4373,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2)
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4371,c_3401])).

cnf(c_2875,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2874])).

cnf(c_4413,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4373,c_31,c_32,c_33,c_35,c_1838,c_2875])).

cnf(c_7,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_1040,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | m1_subset_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1575,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1040])).

cnf(c_4416,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4413,c_1575])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5092,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4416,c_31,c_32,c_33,c_35,c_36,c_37,c_38])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1046,plain,
    ( ~ r2_funct_2(X0_52,X1_52,X0_51,X1_51)
    | ~ v1_funct_2(X1_51,X0_52,X1_52)
    | ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51)
    | X0_51 = X1_51 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1569,plain,
    ( X0_51 = X1_51
    | r2_funct_2(X0_52,X1_52,X0_51,X1_51) != iProver_top
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | v1_funct_2(X1_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1046])).

cnf(c_2548,plain,
    ( sK3 = X0_51
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_1569])).

cnf(c_2866,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | sK3 = X0_51
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2548,c_36,c_37])).

cnf(c_2867,plain,
    ( sK3 = X0_51
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_2866])).

cnf(c_5102,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5092,c_2867])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f70])).

cnf(c_1029,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,k3_tmap_1(X2_50,X1_50,X0_50,X0_50,X0_51))
    | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X2_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1586,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,k3_tmap_1(X2_50,X1_50,X0_50,X0_50,X0_51)) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1029])).

cnf(c_4415,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4413,c_1586])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f60])).

cnf(c_1039,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X2_50)
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1576,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1039])).

cnf(c_4417,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4413,c_1576])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f59])).

cnf(c_1038,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_pre_topc(X3_50,X2_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X1_50)
    | v2_struct_0(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v1_funct_1(X0_51)
    | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1577,plain,
    ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X3_50) != iProver_top
    | m1_pre_topc(X0_50,X3_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X3_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X3_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1038])).

cnf(c_3404,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK2,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_1577])).

cnf(c_1661,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_pre_topc(X2_50,X1_50)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
    | v2_struct_0(X1_50)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(X0_51)
    | v1_funct_1(k3_tmap_1(X1_50,sK1,X0_50,X2_50,X0_51)) ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_1775,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_pre_topc(sK2,X1_50)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(X1_50)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1661])).

cnf(c_1776,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK2,X1_50) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1775])).

cnf(c_3505,plain,
    ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3)) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK2,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_pre_topc(X1_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3404,c_31,c_32,c_33,c_36,c_37,c_38,c_1776])).

cnf(c_3506,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK2,X1_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3505])).

cnf(c_4418,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4413,c_3506])).

cnf(c_4033,plain,
    ( k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X1_50),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1575,c_2867])).

cnf(c_4504,plain,
    ( v2_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X1_50),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51)) != iProver_top
    | k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51) = sK3
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4033,c_31,c_32,c_33])).

cnf(c_4505,plain,
    ( k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X1_50),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4504])).

cnf(c_4509,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4413,c_4505])).

cnf(c_4510,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4509,c_4413])).

cnf(c_4511,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4510,c_4413])).

cnf(c_5208,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5102,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_4415,c_4417,c_4418,c_4511])).

cnf(c_15,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
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
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1032,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
    | ~ v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
    | r2_hidden(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X0_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
    | v2_struct_0(X2_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1583,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | r2_hidden(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X0_50)) = iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1032])).

cnf(c_5218,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK2)) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5208,c_1583])).

cnf(c_6063,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK2)) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5218,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_1838,c_2086,c_2875])).

cnf(c_6064,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_6063])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f66])).

cnf(c_1031,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
    | ~ v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
    | m1_subset_1(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X2_50))
    | v2_struct_0(X2_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1584,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X0_50,X2_50) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X2_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X2_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X2_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1031])).

cnf(c_5217,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5208,c_1584])).

cnf(c_5889,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5217,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_1838,c_2086,c_2875])).

cnf(c_5890,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_5889])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1043,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
    | m1_subset_1(X0_51,u1_struct_0(X1_50))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X1_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1572,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X1_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1043])).

cnf(c_5894,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X0_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_5890,c_1572])).

cnf(c_6042,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X0_50)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5894,c_34])).

cnf(c_6043,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X0_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_6042])).

cnf(c_6047,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X1_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_6043,c_1572])).

cnf(c_1072,plain,
    ( m1_pre_topc(X0_50,X1_50) != iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1044])).

cnf(c_6662,plain,
    ( v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X1_50)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6047,c_1072])).

cnf(c_6663,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_50,X1_50) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X1_50)) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_6662])).

cnf(c_6666,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK1)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_6663])).

cnf(c_6670,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6666,c_31,c_33,c_34,c_35,c_1838,c_2875])).

cnf(c_6671,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK1)) = iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_6670])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | k1_funct_1(k4_tmap_1(X2,X1),X0) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1027,plain,
    ( ~ r2_hidden(X0_51,u1_struct_0(X0_50))
    | ~ m1_pre_topc(X0_50,X1_50)
    | ~ m1_subset_1(X0_51,u1_struct_0(X1_50))
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X1_50)
    | k1_funct_1(k4_tmap_1(X1_50,X0_50),X0_51) = X0_51 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1588,plain,
    ( k1_funct_1(k4_tmap_1(X0_50,X1_50),X0_51) = X0_51
    | r2_hidden(X0_51,u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1027])).

cnf(c_6674,plain,
    ( k1_funct_1(k4_tmap_1(sK1,X0_50),sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_6671,c_1588])).

cnf(c_6688,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X0_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | k1_funct_1(k4_tmap_1(sK1,X0_50),sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
    | v1_funct_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6674,c_31,c_32,c_33])).

cnf(c_6689,plain,
    ( k1_funct_1(k4_tmap_1(sK1,X0_50),sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X0_50)) != iProver_top
    | m1_pre_topc(X0_50,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_6688])).

cnf(c_6692,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_6064,c_6689])).

cnf(c_6722,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6692,c_34,c_35])).

cnf(c_6723,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_6722])).

cnf(c_6727,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1578,c_6723])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ r2_hidden(X3,u1_struct_0(X4))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k1_funct_1(k3_tmap_1(X5,X2,X1,X4,X0),X3) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1030,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ r2_hidden(X1_51,u1_struct_0(X2_50))
    | ~ m1_pre_topc(X2_50,X0_50)
    | ~ m1_pre_topc(X0_50,X3_50)
    | ~ m1_pre_topc(X2_50,X3_50)
    | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | v2_struct_0(X2_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | v2_struct_0(X3_50)
    | ~ l1_pre_topc(X1_50)
    | ~ l1_pre_topc(X3_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v2_pre_topc(X3_50)
    | ~ v1_funct_1(X0_51)
    | k1_funct_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),X1_51) = k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,X1_51) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1585,plain,
    ( k1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51),X1_51) = k3_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),X0_51,X1_51)
    | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | r2_hidden(X1_51,u1_struct_0(X3_50)) != iProver_top
    | m1_pre_topc(X3_50,X2_50) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_pre_topc(X3_50,X0_50) != iProver_top
    | m1_subset_1(X1_51,u1_struct_0(X2_50)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X3_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1030])).

cnf(c_4053,plain,
    ( k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),X0_51) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_51,u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_1585])).

cnf(c_4379,plain,
    ( l1_pre_topc(X0_50) != iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | r2_hidden(X0_51,u1_struct_0(X1_50)) != iProver_top
    | k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),X0_51) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51)
    | v2_pre_topc(X0_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4053,c_31,c_32,c_33,c_34,c_36,c_37])).

cnf(c_4380,plain,
    ( k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),X0_51) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51)
    | r2_hidden(X0_51,u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X1_50,X0_50) != iProver_top
    | m1_pre_topc(X1_50,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_4379])).

cnf(c_6068,plain,
    ( k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,X0_51)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_51))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_6064,c_4380])).

cnf(c_6434,plain,
    ( v2_struct_0(X0_50) = iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,X0_51)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_51))
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6068,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_1838,c_2086,c_2875,c_5217])).

cnf(c_6435,plain,
    ( k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,X0_51)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_51))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_6434])).

cnf(c_6439,plain,
    ( k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1578,c_6435])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1035,plain,
    ( ~ m1_pre_topc(X0_50,X1_50)
    | v2_struct_0(X1_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X1_50)
    | v1_funct_1(k4_tmap_1(X1_50,X0_50)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2419,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_2420,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2419])).

cnf(c_2934,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1578,c_2867])).

cnf(c_21,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_42,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1049,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1066,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_1051,plain,
    ( ~ r2_funct_2(X0_52,X1_52,X0_51,X1_51)
    | r2_funct_2(X0_52,X1_52,X2_51,X3_51)
    | X2_51 != X0_51
    | X3_51 != X1_51 ),
    theory(equality)).

cnf(c_1748,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_51,X1_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
    | k4_tmap_1(sK1,sK2) != X0_51
    | sK3 != X1_51 ),
    inference(instantiation,[status(thm)],[c_1051])).

cnf(c_1749,plain,
    ( k4_tmap_1(sK1,sK2) != X0_51
    | sK3 != X1_51
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_51,X1_51) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1748])).

cnf(c_1751,plain,
    ( k4_tmap_1(sK1,sK2) != sK3
    | sK3 != sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1749])).

cnf(c_0,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1047,plain,
    ( r2_funct_2(X0_52,X1_52,X0_51,X0_51)
    | ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1568,plain,
    ( r2_funct_2(X0_52,X1_52,X0_51,X0_51) = iProver_top
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1047])).

cnf(c_2054,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_1568])).

cnf(c_3021,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2934,c_31,c_32,c_33,c_35,c_36,c_37,c_42,c_1066,c_1751,c_2054,c_2420])).

cnf(c_3022,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3021])).

cnf(c_11,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1036,plain,
    ( v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50))
    | ~ m1_pre_topc(X1_50,X0_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X0_50)
    | ~ v2_pre_topc(X0_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_4021,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_4022,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4021])).

cnf(c_6459,plain,
    ( l1_pre_topc(X0_50) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | v2_struct_0(X0_50) = iProver_top
    | v2_pre_topc(X0_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6439,c_31,c_32,c_33,c_35,c_36,c_37,c_42,c_1066,c_1751,c_2054,c_2420,c_2934,c_4022])).

cnf(c_6460,plain,
    ( k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_6459])).

cnf(c_6465,plain,
    ( k1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_6460])).

cnf(c_5215,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_5208,c_4413])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k1_funct_1(sK3,X0) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1025,negated_conjecture,
    ( ~ r2_hidden(X0_51,u1_struct_0(sK2))
    | ~ m1_subset_1(X0_51,u1_struct_0(sK1))
    | k1_funct_1(sK3,X0_51) = X0_51 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1590,plain,
    ( k1_funct_1(sK3,X0_51) = X0_51
    | r2_hidden(X0_51,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1025])).

cnf(c_6067,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_6064,c_1590])).

cnf(c_6309,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_6043,c_6067])).

cnf(c_6312,plain,
    ( v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6309,c_31,c_33,c_35])).

cnf(c_6313,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
    | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_6312])).

cnf(c_6317,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1578,c_6313])).

cnf(c_6448,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6317,c_31,c_32,c_33,c_35,c_36,c_37,c_42,c_1066,c_1751,c_2054,c_2420,c_2934,c_4022])).

cnf(c_6468,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6465,c_5215,c_6448])).

cnf(c_6466,plain,
    ( k1_funct_1(k3_tmap_1(sK2,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1581,c_6460])).

cnf(c_4372,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k3_tmap_1(X0_50,sK1,sK2,X0_50,sK3)
    | m1_pre_topc(X0_50,sK2) != iProver_top
    | m1_pre_topc(sK2,X0_50) != iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1581,c_4366])).

cnf(c_4500,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK2,sK2,sK3)
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1581,c_4372])).

cnf(c_4501,plain,
    ( k3_tmap_1(sK2,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2)
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4500,c_3401])).

cnf(c_4605,plain,
    ( k3_tmap_1(sK2,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4501,c_32,c_33,c_34,c_35,c_1838,c_2086,c_2875])).

cnf(c_5213,plain,
    ( k3_tmap_1(sK2,sK1,sK2,sK2,sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_5208,c_4605])).

cnf(c_6467,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6466,c_5213,c_6448])).

cnf(c_6472,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6468,c_32,c_33,c_34,c_35,c_1838,c_2086,c_6467])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f68])).

cnf(c_1033,plain,
    ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
    | ~ v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
    | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
    | ~ m1_pre_topc(X0_50,X2_50)
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
    | v2_struct_0(X2_50)
    | v2_struct_0(X1_50)
    | v2_struct_0(X0_50)
    | ~ l1_pre_topc(X2_50)
    | ~ l1_pre_topc(X1_50)
    | ~ v2_pre_topc(X2_50)
    | ~ v2_pre_topc(X1_50)
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51)
    | k3_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),X0_51,sK0(X1_50,X2_50,X0_50,X0_51,X1_51)) != k1_funct_1(X1_51,sK0(X1_50,X2_50,X0_50,X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1582,plain,
    ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) != k1_funct_1(X1_51,sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
    | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
    | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
    | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
    | m1_pre_topc(X2_50,X0_50) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
    | v2_struct_0(X2_50) = iProver_top
    | v2_struct_0(X1_50) = iProver_top
    | v2_struct_0(X0_50) = iProver_top
    | l1_pre_topc(X1_50) != iProver_top
    | l1_pre_topc(X0_50) != iProver_top
    | v2_pre_topc(X1_50) != iProver_top
    | v2_pre_topc(X0_50) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1033])).

cnf(c_6478,plain,
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
    inference(superposition,[status(thm)],[c_6472,c_1582])).

cnf(c_6479,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
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
    inference(light_normalisation,[status(thm)],[c_6478,c_5208])).

cnf(c_4920,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1037])).

cnf(c_4921,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4920])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6727,c_6479,c_4921,c_4022,c_3022,c_2875,c_2420,c_2086,c_1838,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.02/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.02/1.03  
% 4.02/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.02/1.03  
% 4.02/1.03  ------  iProver source info
% 4.02/1.03  
% 4.02/1.03  git: date: 2020-06-30 10:37:57 +0100
% 4.02/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.02/1.03  git: non_committed_changes: false
% 4.02/1.03  git: last_make_outside_of_git: false
% 4.02/1.03  
% 4.02/1.03  ------ 
% 4.02/1.03  
% 4.02/1.03  ------ Input Options
% 4.02/1.03  
% 4.02/1.03  --out_options                           all
% 4.02/1.03  --tptp_safe_out                         true
% 4.02/1.03  --problem_path                          ""
% 4.02/1.03  --include_path                          ""
% 4.02/1.03  --clausifier                            res/vclausify_rel
% 4.02/1.03  --clausifier_options                    ""
% 4.02/1.03  --stdin                                 false
% 4.02/1.03  --stats_out                             all
% 4.02/1.03  
% 4.02/1.03  ------ General Options
% 4.02/1.03  
% 4.02/1.03  --fof                                   false
% 4.02/1.03  --time_out_real                         305.
% 4.02/1.03  --time_out_virtual                      -1.
% 4.02/1.03  --symbol_type_check                     false
% 4.02/1.03  --clausify_out                          false
% 4.02/1.03  --sig_cnt_out                           false
% 4.02/1.03  --trig_cnt_out                          false
% 4.02/1.03  --trig_cnt_out_tolerance                1.
% 4.02/1.03  --trig_cnt_out_sk_spl                   false
% 4.02/1.03  --abstr_cl_out                          false
% 4.02/1.03  
% 4.02/1.03  ------ Global Options
% 4.02/1.03  
% 4.02/1.03  --schedule                              default
% 4.02/1.03  --add_important_lit                     false
% 4.02/1.03  --prop_solver_per_cl                    1000
% 4.02/1.03  --min_unsat_core                        false
% 4.02/1.03  --soft_assumptions                      false
% 4.02/1.03  --soft_lemma_size                       3
% 4.02/1.03  --prop_impl_unit_size                   0
% 4.02/1.03  --prop_impl_unit                        []
% 4.02/1.03  --share_sel_clauses                     true
% 4.02/1.03  --reset_solvers                         false
% 4.02/1.03  --bc_imp_inh                            [conj_cone]
% 4.02/1.03  --conj_cone_tolerance                   3.
% 4.02/1.03  --extra_neg_conj                        none
% 4.02/1.03  --large_theory_mode                     true
% 4.02/1.03  --prolific_symb_bound                   200
% 4.02/1.03  --lt_threshold                          2000
% 4.02/1.03  --clause_weak_htbl                      true
% 4.02/1.03  --gc_record_bc_elim                     false
% 4.02/1.03  
% 4.02/1.03  ------ Preprocessing Options
% 4.02/1.03  
% 4.02/1.03  --preprocessing_flag                    true
% 4.02/1.03  --time_out_prep_mult                    0.1
% 4.02/1.03  --splitting_mode                        input
% 4.02/1.03  --splitting_grd                         true
% 4.02/1.03  --splitting_cvd                         false
% 4.02/1.03  --splitting_cvd_svl                     false
% 4.02/1.03  --splitting_nvd                         32
% 4.02/1.03  --sub_typing                            true
% 4.02/1.03  --prep_gs_sim                           true
% 4.02/1.03  --prep_unflatten                        true
% 4.02/1.03  --prep_res_sim                          true
% 4.02/1.03  --prep_upred                            true
% 4.02/1.03  --prep_sem_filter                       exhaustive
% 4.02/1.03  --prep_sem_filter_out                   false
% 4.02/1.03  --pred_elim                             true
% 4.02/1.03  --res_sim_input                         true
% 4.02/1.03  --eq_ax_congr_red                       true
% 4.02/1.03  --pure_diseq_elim                       true
% 4.02/1.03  --brand_transform                       false
% 4.02/1.03  --non_eq_to_eq                          false
% 4.02/1.03  --prep_def_merge                        true
% 4.02/1.03  --prep_def_merge_prop_impl              false
% 4.02/1.03  --prep_def_merge_mbd                    true
% 4.02/1.03  --prep_def_merge_tr_red                 false
% 4.02/1.03  --prep_def_merge_tr_cl                  false
% 4.02/1.03  --smt_preprocessing                     true
% 4.02/1.03  --smt_ac_axioms                         fast
% 4.02/1.03  --preprocessed_out                      false
% 4.02/1.03  --preprocessed_stats                    false
% 4.02/1.03  
% 4.02/1.03  ------ Abstraction refinement Options
% 4.02/1.03  
% 4.02/1.03  --abstr_ref                             []
% 4.02/1.03  --abstr_ref_prep                        false
% 4.02/1.03  --abstr_ref_until_sat                   false
% 4.02/1.03  --abstr_ref_sig_restrict                funpre
% 4.02/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 4.02/1.03  --abstr_ref_under                       []
% 4.02/1.03  
% 4.02/1.03  ------ SAT Options
% 4.02/1.03  
% 4.02/1.03  --sat_mode                              false
% 4.02/1.03  --sat_fm_restart_options                ""
% 4.02/1.03  --sat_gr_def                            false
% 4.02/1.03  --sat_epr_types                         true
% 4.02/1.03  --sat_non_cyclic_types                  false
% 4.02/1.03  --sat_finite_models                     false
% 4.02/1.03  --sat_fm_lemmas                         false
% 4.02/1.03  --sat_fm_prep                           false
% 4.02/1.03  --sat_fm_uc_incr                        true
% 4.02/1.03  --sat_out_model                         small
% 4.02/1.03  --sat_out_clauses                       false
% 4.02/1.03  
% 4.02/1.03  ------ QBF Options
% 4.02/1.03  
% 4.02/1.03  --qbf_mode                              false
% 4.02/1.03  --qbf_elim_univ                         false
% 4.02/1.03  --qbf_dom_inst                          none
% 4.02/1.03  --qbf_dom_pre_inst                      false
% 4.02/1.03  --qbf_sk_in                             false
% 4.02/1.03  --qbf_pred_elim                         true
% 4.02/1.03  --qbf_split                             512
% 4.02/1.03  
% 4.02/1.03  ------ BMC1 Options
% 4.02/1.03  
% 4.02/1.03  --bmc1_incremental                      false
% 4.02/1.03  --bmc1_axioms                           reachable_all
% 4.02/1.03  --bmc1_min_bound                        0
% 4.02/1.03  --bmc1_max_bound                        -1
% 4.02/1.03  --bmc1_max_bound_default                -1
% 4.02/1.03  --bmc1_symbol_reachability              true
% 4.02/1.03  --bmc1_property_lemmas                  false
% 4.02/1.03  --bmc1_k_induction                      false
% 4.02/1.03  --bmc1_non_equiv_states                 false
% 4.02/1.03  --bmc1_deadlock                         false
% 4.02/1.03  --bmc1_ucm                              false
% 4.02/1.03  --bmc1_add_unsat_core                   none
% 4.02/1.03  --bmc1_unsat_core_children              false
% 4.02/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 4.02/1.03  --bmc1_out_stat                         full
% 4.02/1.03  --bmc1_ground_init                      false
% 4.02/1.03  --bmc1_pre_inst_next_state              false
% 4.02/1.03  --bmc1_pre_inst_state                   false
% 4.02/1.03  --bmc1_pre_inst_reach_state             false
% 4.02/1.03  --bmc1_out_unsat_core                   false
% 4.02/1.03  --bmc1_aig_witness_out                  false
% 4.02/1.03  --bmc1_verbose                          false
% 4.02/1.03  --bmc1_dump_clauses_tptp                false
% 4.02/1.03  --bmc1_dump_unsat_core_tptp             false
% 4.02/1.03  --bmc1_dump_file                        -
% 4.02/1.03  --bmc1_ucm_expand_uc_limit              128
% 4.02/1.03  --bmc1_ucm_n_expand_iterations          6
% 4.02/1.03  --bmc1_ucm_extend_mode                  1
% 4.02/1.03  --bmc1_ucm_init_mode                    2
% 4.02/1.03  --bmc1_ucm_cone_mode                    none
% 4.02/1.03  --bmc1_ucm_reduced_relation_type        0
% 4.02/1.03  --bmc1_ucm_relax_model                  4
% 4.02/1.03  --bmc1_ucm_full_tr_after_sat            true
% 4.02/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 4.02/1.03  --bmc1_ucm_layered_model                none
% 4.02/1.03  --bmc1_ucm_max_lemma_size               10
% 4.02/1.03  
% 4.02/1.03  ------ AIG Options
% 4.02/1.03  
% 4.02/1.03  --aig_mode                              false
% 4.02/1.03  
% 4.02/1.03  ------ Instantiation Options
% 4.02/1.03  
% 4.02/1.03  --instantiation_flag                    true
% 4.02/1.03  --inst_sos_flag                         true
% 4.02/1.03  --inst_sos_phase                        true
% 4.02/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.02/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.02/1.03  --inst_lit_sel_side                     num_symb
% 4.02/1.03  --inst_solver_per_active                1400
% 4.02/1.03  --inst_solver_calls_frac                1.
% 4.02/1.03  --inst_passive_queue_type               priority_queues
% 4.02/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.02/1.03  --inst_passive_queues_freq              [25;2]
% 4.02/1.03  --inst_dismatching                      true
% 4.02/1.03  --inst_eager_unprocessed_to_passive     true
% 4.02/1.03  --inst_prop_sim_given                   true
% 4.02/1.03  --inst_prop_sim_new                     false
% 4.02/1.03  --inst_subs_new                         false
% 4.02/1.03  --inst_eq_res_simp                      false
% 4.02/1.03  --inst_subs_given                       false
% 4.02/1.03  --inst_orphan_elimination               true
% 4.02/1.03  --inst_learning_loop_flag               true
% 4.02/1.03  --inst_learning_start                   3000
% 4.02/1.03  --inst_learning_factor                  2
% 4.02/1.03  --inst_start_prop_sim_after_learn       3
% 4.02/1.03  --inst_sel_renew                        solver
% 4.02/1.03  --inst_lit_activity_flag                true
% 4.02/1.03  --inst_restr_to_given                   false
% 4.02/1.03  --inst_activity_threshold               500
% 4.02/1.03  --inst_out_proof                        true
% 4.02/1.03  
% 4.02/1.03  ------ Resolution Options
% 4.02/1.03  
% 4.02/1.03  --resolution_flag                       true
% 4.02/1.03  --res_lit_sel                           adaptive
% 4.02/1.03  --res_lit_sel_side                      none
% 4.02/1.03  --res_ordering                          kbo
% 4.02/1.03  --res_to_prop_solver                    active
% 4.02/1.03  --res_prop_simpl_new                    false
% 4.02/1.03  --res_prop_simpl_given                  true
% 4.02/1.03  --res_passive_queue_type                priority_queues
% 4.02/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.02/1.03  --res_passive_queues_freq               [15;5]
% 4.02/1.03  --res_forward_subs                      full
% 4.02/1.03  --res_backward_subs                     full
% 4.02/1.03  --res_forward_subs_resolution           true
% 4.02/1.03  --res_backward_subs_resolution          true
% 4.02/1.03  --res_orphan_elimination                true
% 4.02/1.03  --res_time_limit                        2.
% 4.02/1.03  --res_out_proof                         true
% 4.02/1.03  
% 4.02/1.03  ------ Superposition Options
% 4.02/1.03  
% 4.02/1.03  --superposition_flag                    true
% 4.02/1.03  --sup_passive_queue_type                priority_queues
% 4.02/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.02/1.03  --sup_passive_queues_freq               [8;1;4]
% 4.02/1.03  --demod_completeness_check              fast
% 4.02/1.03  --demod_use_ground                      true
% 4.02/1.03  --sup_to_prop_solver                    passive
% 4.02/1.03  --sup_prop_simpl_new                    true
% 4.02/1.03  --sup_prop_simpl_given                  true
% 4.02/1.03  --sup_fun_splitting                     true
% 4.02/1.03  --sup_smt_interval                      50000
% 4.02/1.03  
% 4.02/1.03  ------ Superposition Simplification Setup
% 4.02/1.03  
% 4.02/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.02/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.02/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.02/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.02/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 4.02/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.02/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.02/1.03  --sup_immed_triv                        [TrivRules]
% 4.02/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/1.03  --sup_immed_bw_main                     []
% 4.02/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.02/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 4.02/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/1.03  --sup_input_bw                          []
% 4.02/1.03  
% 4.02/1.03  ------ Combination Options
% 4.02/1.03  
% 4.02/1.03  --comb_res_mult                         3
% 4.02/1.03  --comb_sup_mult                         2
% 4.02/1.03  --comb_inst_mult                        10
% 4.02/1.03  
% 4.02/1.03  ------ Debug Options
% 4.02/1.03  
% 4.02/1.03  --dbg_backtrace                         false
% 4.02/1.03  --dbg_dump_prop_clauses                 false
% 4.02/1.03  --dbg_dump_prop_clauses_file            -
% 4.02/1.03  --dbg_out_stat                          false
% 4.02/1.03  ------ Parsing...
% 4.02/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.02/1.03  
% 4.02/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.02/1.03  
% 4.02/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.02/1.03  
% 4.02/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.02/1.03  ------ Proving...
% 4.02/1.03  ------ Problem Properties 
% 4.02/1.03  
% 4.02/1.03  
% 4.02/1.03  clauses                                 31
% 4.02/1.03  conjectures                             10
% 4.02/1.03  EPR                                     10
% 4.02/1.03  Horn                                    16
% 4.02/1.03  unary                                   9
% 4.02/1.03  binary                                  1
% 4.02/1.03  lits                                    204
% 4.02/1.03  lits eq                                 7
% 4.02/1.03  fd_pure                                 0
% 4.02/1.03  fd_pseudo                               0
% 4.02/1.03  fd_cond                                 0
% 4.02/1.03  fd_pseudo_cond                          1
% 4.02/1.03  AC symbols                              0
% 4.02/1.03  
% 4.02/1.03  ------ Schedule dynamic 5 is on 
% 4.02/1.03  
% 4.02/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.02/1.03  
% 4.02/1.03  
% 4.02/1.03  ------ 
% 4.02/1.03  Current options:
% 4.02/1.03  ------ 
% 4.02/1.03  
% 4.02/1.03  ------ Input Options
% 4.02/1.03  
% 4.02/1.03  --out_options                           all
% 4.02/1.03  --tptp_safe_out                         true
% 4.02/1.03  --problem_path                          ""
% 4.02/1.03  --include_path                          ""
% 4.02/1.03  --clausifier                            res/vclausify_rel
% 4.02/1.03  --clausifier_options                    ""
% 4.02/1.03  --stdin                                 false
% 4.02/1.03  --stats_out                             all
% 4.02/1.03  
% 4.02/1.03  ------ General Options
% 4.02/1.03  
% 4.02/1.03  --fof                                   false
% 4.02/1.03  --time_out_real                         305.
% 4.02/1.03  --time_out_virtual                      -1.
% 4.02/1.03  --symbol_type_check                     false
% 4.02/1.03  --clausify_out                          false
% 4.02/1.03  --sig_cnt_out                           false
% 4.02/1.03  --trig_cnt_out                          false
% 4.02/1.03  --trig_cnt_out_tolerance                1.
% 4.02/1.03  --trig_cnt_out_sk_spl                   false
% 4.02/1.03  --abstr_cl_out                          false
% 4.02/1.03  
% 4.02/1.03  ------ Global Options
% 4.02/1.03  
% 4.02/1.03  --schedule                              default
% 4.02/1.03  --add_important_lit                     false
% 4.02/1.03  --prop_solver_per_cl                    1000
% 4.02/1.03  --min_unsat_core                        false
% 4.02/1.03  --soft_assumptions                      false
% 4.02/1.03  --soft_lemma_size                       3
% 4.02/1.03  --prop_impl_unit_size                   0
% 4.02/1.03  --prop_impl_unit                        []
% 4.02/1.03  --share_sel_clauses                     true
% 4.02/1.03  --reset_solvers                         false
% 4.02/1.03  --bc_imp_inh                            [conj_cone]
% 4.02/1.03  --conj_cone_tolerance                   3.
% 4.02/1.03  --extra_neg_conj                        none
% 4.02/1.03  --large_theory_mode                     true
% 4.02/1.03  --prolific_symb_bound                   200
% 4.02/1.03  --lt_threshold                          2000
% 4.02/1.03  --clause_weak_htbl                      true
% 4.02/1.03  --gc_record_bc_elim                     false
% 4.02/1.03  
% 4.02/1.03  ------ Preprocessing Options
% 4.02/1.03  
% 4.02/1.03  --preprocessing_flag                    true
% 4.02/1.03  --time_out_prep_mult                    0.1
% 4.02/1.03  --splitting_mode                        input
% 4.02/1.03  --splitting_grd                         true
% 4.02/1.03  --splitting_cvd                         false
% 4.02/1.03  --splitting_cvd_svl                     false
% 4.02/1.03  --splitting_nvd                         32
% 4.02/1.03  --sub_typing                            true
% 4.02/1.03  --prep_gs_sim                           true
% 4.02/1.03  --prep_unflatten                        true
% 4.02/1.03  --prep_res_sim                          true
% 4.02/1.03  --prep_upred                            true
% 4.02/1.03  --prep_sem_filter                       exhaustive
% 4.02/1.03  --prep_sem_filter_out                   false
% 4.02/1.03  --pred_elim                             true
% 4.02/1.03  --res_sim_input                         true
% 4.02/1.03  --eq_ax_congr_red                       true
% 4.02/1.03  --pure_diseq_elim                       true
% 4.02/1.03  --brand_transform                       false
% 4.02/1.03  --non_eq_to_eq                          false
% 4.02/1.03  --prep_def_merge                        true
% 4.02/1.03  --prep_def_merge_prop_impl              false
% 4.02/1.03  --prep_def_merge_mbd                    true
% 4.02/1.03  --prep_def_merge_tr_red                 false
% 4.02/1.03  --prep_def_merge_tr_cl                  false
% 4.02/1.03  --smt_preprocessing                     true
% 4.02/1.03  --smt_ac_axioms                         fast
% 4.02/1.03  --preprocessed_out                      false
% 4.02/1.03  --preprocessed_stats                    false
% 4.02/1.03  
% 4.02/1.03  ------ Abstraction refinement Options
% 4.02/1.03  
% 4.02/1.03  --abstr_ref                             []
% 4.02/1.03  --abstr_ref_prep                        false
% 4.02/1.03  --abstr_ref_until_sat                   false
% 4.02/1.03  --abstr_ref_sig_restrict                funpre
% 4.02/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 4.02/1.03  --abstr_ref_under                       []
% 4.02/1.03  
% 4.02/1.03  ------ SAT Options
% 4.02/1.03  
% 4.02/1.03  --sat_mode                              false
% 4.02/1.03  --sat_fm_restart_options                ""
% 4.02/1.03  --sat_gr_def                            false
% 4.02/1.03  --sat_epr_types                         true
% 4.02/1.03  --sat_non_cyclic_types                  false
% 4.02/1.03  --sat_finite_models                     false
% 4.02/1.03  --sat_fm_lemmas                         false
% 4.02/1.03  --sat_fm_prep                           false
% 4.02/1.03  --sat_fm_uc_incr                        true
% 4.02/1.03  --sat_out_model                         small
% 4.02/1.03  --sat_out_clauses                       false
% 4.02/1.03  
% 4.02/1.03  ------ QBF Options
% 4.02/1.03  
% 4.02/1.03  --qbf_mode                              false
% 4.02/1.03  --qbf_elim_univ                         false
% 4.02/1.03  --qbf_dom_inst                          none
% 4.02/1.03  --qbf_dom_pre_inst                      false
% 4.02/1.03  --qbf_sk_in                             false
% 4.02/1.03  --qbf_pred_elim                         true
% 4.02/1.03  --qbf_split                             512
% 4.02/1.03  
% 4.02/1.03  ------ BMC1 Options
% 4.02/1.03  
% 4.02/1.03  --bmc1_incremental                      false
% 4.02/1.03  --bmc1_axioms                           reachable_all
% 4.02/1.03  --bmc1_min_bound                        0
% 4.02/1.03  --bmc1_max_bound                        -1
% 4.02/1.03  --bmc1_max_bound_default                -1
% 4.02/1.03  --bmc1_symbol_reachability              true
% 4.02/1.03  --bmc1_property_lemmas                  false
% 4.02/1.03  --bmc1_k_induction                      false
% 4.02/1.03  --bmc1_non_equiv_states                 false
% 4.02/1.03  --bmc1_deadlock                         false
% 4.02/1.03  --bmc1_ucm                              false
% 4.02/1.03  --bmc1_add_unsat_core                   none
% 4.02/1.03  --bmc1_unsat_core_children              false
% 4.02/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 4.02/1.03  --bmc1_out_stat                         full
% 4.02/1.03  --bmc1_ground_init                      false
% 4.02/1.03  --bmc1_pre_inst_next_state              false
% 4.02/1.03  --bmc1_pre_inst_state                   false
% 4.02/1.03  --bmc1_pre_inst_reach_state             false
% 4.02/1.03  --bmc1_out_unsat_core                   false
% 4.02/1.03  --bmc1_aig_witness_out                  false
% 4.02/1.03  --bmc1_verbose                          false
% 4.02/1.03  --bmc1_dump_clauses_tptp                false
% 4.02/1.03  --bmc1_dump_unsat_core_tptp             false
% 4.02/1.03  --bmc1_dump_file                        -
% 4.02/1.03  --bmc1_ucm_expand_uc_limit              128
% 4.02/1.03  --bmc1_ucm_n_expand_iterations          6
% 4.02/1.03  --bmc1_ucm_extend_mode                  1
% 4.02/1.03  --bmc1_ucm_init_mode                    2
% 4.02/1.03  --bmc1_ucm_cone_mode                    none
% 4.02/1.03  --bmc1_ucm_reduced_relation_type        0
% 4.02/1.03  --bmc1_ucm_relax_model                  4
% 4.02/1.03  --bmc1_ucm_full_tr_after_sat            true
% 4.02/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 4.02/1.03  --bmc1_ucm_layered_model                none
% 4.02/1.03  --bmc1_ucm_max_lemma_size               10
% 4.02/1.03  
% 4.02/1.03  ------ AIG Options
% 4.02/1.03  
% 4.02/1.03  --aig_mode                              false
% 4.02/1.03  
% 4.02/1.03  ------ Instantiation Options
% 4.02/1.03  
% 4.02/1.03  --instantiation_flag                    true
% 4.02/1.03  --inst_sos_flag                         true
% 4.02/1.03  --inst_sos_phase                        true
% 4.02/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.02/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.02/1.03  --inst_lit_sel_side                     none
% 4.02/1.03  --inst_solver_per_active                1400
% 4.02/1.03  --inst_solver_calls_frac                1.
% 4.02/1.03  --inst_passive_queue_type               priority_queues
% 4.02/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.02/1.03  --inst_passive_queues_freq              [25;2]
% 4.02/1.03  --inst_dismatching                      true
% 4.02/1.03  --inst_eager_unprocessed_to_passive     true
% 4.02/1.03  --inst_prop_sim_given                   true
% 4.02/1.03  --inst_prop_sim_new                     false
% 4.02/1.03  --inst_subs_new                         false
% 4.02/1.03  --inst_eq_res_simp                      false
% 4.02/1.03  --inst_subs_given                       false
% 4.02/1.03  --inst_orphan_elimination               true
% 4.02/1.03  --inst_learning_loop_flag               true
% 4.02/1.03  --inst_learning_start                   3000
% 4.02/1.03  --inst_learning_factor                  2
% 4.02/1.03  --inst_start_prop_sim_after_learn       3
% 4.02/1.03  --inst_sel_renew                        solver
% 4.02/1.03  --inst_lit_activity_flag                true
% 4.02/1.03  --inst_restr_to_given                   false
% 4.02/1.03  --inst_activity_threshold               500
% 4.02/1.03  --inst_out_proof                        true
% 4.02/1.03  
% 4.02/1.03  ------ Resolution Options
% 4.02/1.03  
% 4.02/1.03  --resolution_flag                       false
% 4.02/1.03  --res_lit_sel                           adaptive
% 4.02/1.03  --res_lit_sel_side                      none
% 4.02/1.03  --res_ordering                          kbo
% 4.02/1.03  --res_to_prop_solver                    active
% 4.02/1.03  --res_prop_simpl_new                    false
% 4.02/1.03  --res_prop_simpl_given                  true
% 4.02/1.03  --res_passive_queue_type                priority_queues
% 4.02/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.02/1.03  --res_passive_queues_freq               [15;5]
% 4.02/1.03  --res_forward_subs                      full
% 4.02/1.03  --res_backward_subs                     full
% 4.02/1.03  --res_forward_subs_resolution           true
% 4.02/1.03  --res_backward_subs_resolution          true
% 4.02/1.03  --res_orphan_elimination                true
% 4.02/1.03  --res_time_limit                        2.
% 4.02/1.03  --res_out_proof                         true
% 4.02/1.03  
% 4.02/1.03  ------ Superposition Options
% 4.02/1.03  
% 4.02/1.03  --superposition_flag                    true
% 4.02/1.03  --sup_passive_queue_type                priority_queues
% 4.02/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.02/1.03  --sup_passive_queues_freq               [8;1;4]
% 4.02/1.03  --demod_completeness_check              fast
% 4.02/1.03  --demod_use_ground                      true
% 4.02/1.03  --sup_to_prop_solver                    passive
% 4.02/1.03  --sup_prop_simpl_new                    true
% 4.02/1.03  --sup_prop_simpl_given                  true
% 4.02/1.03  --sup_fun_splitting                     true
% 4.02/1.03  --sup_smt_interval                      50000
% 4.02/1.03  
% 4.02/1.03  ------ Superposition Simplification Setup
% 4.02/1.03  
% 4.02/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.02/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.02/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.02/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.02/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 4.02/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.02/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.02/1.03  --sup_immed_triv                        [TrivRules]
% 4.02/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/1.03  --sup_immed_bw_main                     []
% 4.02/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.02/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 4.02/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.02/1.03  --sup_input_bw                          []
% 4.02/1.03  
% 4.02/1.03  ------ Combination Options
% 4.02/1.03  
% 4.02/1.03  --comb_res_mult                         3
% 4.02/1.03  --comb_sup_mult                         2
% 4.02/1.03  --comb_inst_mult                        10
% 4.02/1.03  
% 4.02/1.03  ------ Debug Options
% 4.02/1.03  
% 4.02/1.03  --dbg_backtrace                         false
% 4.02/1.03  --dbg_dump_prop_clauses                 false
% 4.02/1.03  --dbg_dump_prop_clauses_file            -
% 4.02/1.03  --dbg_out_stat                          false
% 4.02/1.03  
% 4.02/1.03  
% 4.02/1.03  
% 4.02/1.03  
% 4.02/1.03  ------ Proving...
% 4.02/1.03  
% 4.02/1.03  
% 4.02/1.03  % SZS status Theorem for theBenchmark.p
% 4.02/1.03  
% 4.02/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 4.02/1.03  
% 4.02/1.03  fof(f8,axiom,(
% 4.02/1.03    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 4.02/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.03  
% 4.02/1.03  fof(f30,plain,(
% 4.02/1.03    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.02/1.03    inference(ennf_transformation,[],[f8])).
% 4.02/1.03  
% 4.02/1.03  fof(f31,plain,(
% 4.02/1.03    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/1.03    inference(flattening,[],[f30])).
% 4.02/1.03  
% 4.02/1.03  fof(f64,plain,(
% 4.02/1.03    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f31])).
% 4.02/1.03  
% 4.02/1.03  fof(f15,conjecture,(
% 4.02/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 4.02/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.03  
% 4.02/1.03  fof(f16,negated_conjecture,(
% 4.02/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 4.02/1.03    inference(negated_conjecture,[],[f15])).
% 4.02/1.03  
% 4.02/1.03  fof(f43,plain,(
% 4.02/1.03    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.02/1.03    inference(ennf_transformation,[],[f16])).
% 4.02/1.03  
% 4.02/1.03  fof(f44,plain,(
% 4.02/1.03    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.02/1.03    inference(flattening,[],[f43])).
% 4.02/1.03  
% 4.02/1.03  fof(f50,plain,(
% 4.02/1.03    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 4.02/1.03    introduced(choice_axiom,[])).
% 4.02/1.03  
% 4.02/1.03  fof(f49,plain,(
% 4.02/1.03    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 4.02/1.03    introduced(choice_axiom,[])).
% 4.02/1.03  
% 4.02/1.03  fof(f48,plain,(
% 4.02/1.03    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 4.02/1.03    introduced(choice_axiom,[])).
% 4.02/1.03  
% 4.02/1.03  fof(f51,plain,(
% 4.02/1.03    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 4.02/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f50,f49,f48])).
% 4.02/1.03  
% 4.02/1.03  fof(f77,plain,(
% 4.02/1.03    m1_pre_topc(sK2,sK1)),
% 4.02/1.03    inference(cnf_transformation,[],[f51])).
% 4.02/1.03  
% 4.02/1.03  fof(f80,plain,(
% 4.02/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 4.02/1.03    inference(cnf_transformation,[],[f51])).
% 4.02/1.03  
% 4.02/1.03  fof(f6,axiom,(
% 4.02/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 4.02/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.03  
% 4.02/1.03  fof(f26,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.02/1.03    inference(ennf_transformation,[],[f6])).
% 4.02/1.03  
% 4.02/1.03  fof(f27,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/1.03    inference(flattening,[],[f26])).
% 4.02/1.03  
% 4.02/1.03  fof(f58,plain,(
% 4.02/1.03    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f27])).
% 4.02/1.03  
% 4.02/1.03  fof(f73,plain,(
% 4.02/1.03    ~v2_struct_0(sK1)),
% 4.02/1.03    inference(cnf_transformation,[],[f51])).
% 4.02/1.03  
% 4.02/1.03  fof(f74,plain,(
% 4.02/1.03    v2_pre_topc(sK1)),
% 4.02/1.03    inference(cnf_transformation,[],[f51])).
% 4.02/1.03  
% 4.02/1.03  fof(f75,plain,(
% 4.02/1.03    l1_pre_topc(sK1)),
% 4.02/1.03    inference(cnf_transformation,[],[f51])).
% 4.02/1.03  
% 4.02/1.03  fof(f78,plain,(
% 4.02/1.03    v1_funct_1(sK3)),
% 4.02/1.03    inference(cnf_transformation,[],[f51])).
% 4.02/1.03  
% 4.02/1.03  fof(f79,plain,(
% 4.02/1.03    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 4.02/1.03    inference(cnf_transformation,[],[f51])).
% 4.02/1.03  
% 4.02/1.03  fof(f9,axiom,(
% 4.02/1.03    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 4.02/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.03  
% 4.02/1.03  fof(f32,plain,(
% 4.02/1.03    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 4.02/1.03    inference(ennf_transformation,[],[f9])).
% 4.02/1.03  
% 4.02/1.03  fof(f65,plain,(
% 4.02/1.03    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f32])).
% 4.02/1.03  
% 4.02/1.03  fof(f5,axiom,(
% 4.02/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 4.02/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.03  
% 4.02/1.03  fof(f24,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.02/1.03    inference(ennf_transformation,[],[f5])).
% 4.02/1.03  
% 4.02/1.03  fof(f25,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/1.03    inference(flattening,[],[f24])).
% 4.02/1.03  
% 4.02/1.03  fof(f57,plain,(
% 4.02/1.03    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f25])).
% 4.02/1.03  
% 4.02/1.03  fof(f76,plain,(
% 4.02/1.03    ~v2_struct_0(sK2)),
% 4.02/1.03    inference(cnf_transformation,[],[f51])).
% 4.02/1.03  
% 4.02/1.03  fof(f3,axiom,(
% 4.02/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 4.02/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.03  
% 4.02/1.03  fof(f21,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 4.02/1.03    inference(ennf_transformation,[],[f3])).
% 4.02/1.03  
% 4.02/1.03  fof(f55,plain,(
% 4.02/1.03    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f21])).
% 4.02/1.03  
% 4.02/1.03  fof(f2,axiom,(
% 4.02/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 4.02/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.03  
% 4.02/1.03  fof(f19,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.02/1.03    inference(ennf_transformation,[],[f2])).
% 4.02/1.03  
% 4.02/1.03  fof(f20,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.02/1.03    inference(flattening,[],[f19])).
% 4.02/1.03  
% 4.02/1.03  fof(f54,plain,(
% 4.02/1.03    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f20])).
% 4.02/1.03  
% 4.02/1.03  fof(f7,axiom,(
% 4.02/1.03    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 4.02/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.03  
% 4.02/1.03  fof(f28,plain,(
% 4.02/1.03    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.02/1.03    inference(ennf_transformation,[],[f7])).
% 4.02/1.03  
% 4.02/1.03  fof(f29,plain,(
% 4.02/1.03    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/1.03    inference(flattening,[],[f28])).
% 4.02/1.03  
% 4.02/1.03  fof(f61,plain,(
% 4.02/1.03    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f29])).
% 4.02/1.03  
% 4.02/1.03  fof(f1,axiom,(
% 4.02/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 4.02/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.03  
% 4.02/1.03  fof(f17,plain,(
% 4.02/1.03    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.02/1.03    inference(ennf_transformation,[],[f1])).
% 4.02/1.03  
% 4.02/1.03  fof(f18,plain,(
% 4.02/1.03    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.02/1.03    inference(flattening,[],[f17])).
% 4.02/1.03  
% 4.02/1.03  fof(f45,plain,(
% 4.02/1.03    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.02/1.03    inference(nnf_transformation,[],[f18])).
% 4.02/1.03  
% 4.02/1.03  fof(f52,plain,(
% 4.02/1.03    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f45])).
% 4.02/1.03  
% 4.02/1.03  fof(f12,axiom,(
% 4.02/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 4.02/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.03  
% 4.02/1.03  fof(f37,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.02/1.03    inference(ennf_transformation,[],[f12])).
% 4.02/1.03  
% 4.02/1.03  fof(f38,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/1.03    inference(flattening,[],[f37])).
% 4.02/1.03  
% 4.02/1.03  fof(f70,plain,(
% 4.02/1.03    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f38])).
% 4.02/1.03  
% 4.02/1.03  fof(f60,plain,(
% 4.02/1.03    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f29])).
% 4.02/1.03  
% 4.02/1.03  fof(f59,plain,(
% 4.02/1.03    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f29])).
% 4.02/1.03  
% 4.02/1.03  fof(f10,axiom,(
% 4.02/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 4.02/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.03  
% 4.02/1.03  fof(f33,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.02/1.03    inference(ennf_transformation,[],[f10])).
% 4.02/1.03  
% 4.02/1.03  fof(f34,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/1.03    inference(flattening,[],[f33])).
% 4.02/1.03  
% 4.02/1.03  fof(f46,plain,(
% 4.02/1.03    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) => (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))))),
% 4.02/1.03    introduced(choice_axiom,[])).
% 4.02/1.03  
% 4.02/1.03  fof(f47,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f46])).
% 4.02/1.03  
% 4.02/1.03  fof(f67,plain,(
% 4.02/1.03    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f47])).
% 4.02/1.03  
% 4.02/1.03  fof(f66,plain,(
% 4.02/1.03    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f47])).
% 4.02/1.03  
% 4.02/1.03  fof(f4,axiom,(
% 4.02/1.03    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 4.02/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.03  
% 4.02/1.03  fof(f22,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 4.02/1.03    inference(ennf_transformation,[],[f4])).
% 4.02/1.03  
% 4.02/1.03  fof(f23,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/1.03    inference(flattening,[],[f22])).
% 4.02/1.03  
% 4.02/1.03  fof(f56,plain,(
% 4.02/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f23])).
% 4.02/1.03  
% 4.02/1.03  fof(f14,axiom,(
% 4.02/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 4.02/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.03  
% 4.02/1.03  fof(f41,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.02/1.03    inference(ennf_transformation,[],[f14])).
% 4.02/1.03  
% 4.02/1.03  fof(f42,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/1.03    inference(flattening,[],[f41])).
% 4.02/1.03  
% 4.02/1.03  fof(f72,plain,(
% 4.02/1.03    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f42])).
% 4.02/1.03  
% 4.02/1.03  fof(f11,axiom,(
% 4.02/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)))))))))),
% 4.02/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.02/1.03  
% 4.02/1.03  fof(f35,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : ((k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) | ~r2_hidden(X5,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.02/1.03    inference(ennf_transformation,[],[f11])).
% 4.02/1.03  
% 4.02/1.03  fof(f36,plain,(
% 4.02/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.02/1.03    inference(flattening,[],[f35])).
% 4.02/1.03  
% 4.02/1.03  fof(f69,plain,(
% 4.02/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) | ~r2_hidden(X5,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f36])).
% 4.02/1.03  
% 4.02/1.03  fof(f62,plain,(
% 4.02/1.03    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f31])).
% 4.02/1.03  
% 4.02/1.03  fof(f82,plain,(
% 4.02/1.03    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)),
% 4.02/1.03    inference(cnf_transformation,[],[f51])).
% 4.02/1.03  
% 4.02/1.03  fof(f53,plain,(
% 4.02/1.03    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f45])).
% 4.02/1.03  
% 4.02/1.03  fof(f83,plain,(
% 4.02/1.03    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 4.02/1.03    inference(equality_resolution,[],[f53])).
% 4.02/1.03  
% 4.02/1.03  fof(f63,plain,(
% 4.02/1.03    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f31])).
% 4.02/1.03  
% 4.02/1.03  fof(f81,plain,(
% 4.02/1.03    ( ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) )),
% 4.02/1.03    inference(cnf_transformation,[],[f51])).
% 4.02/1.03  
% 4.02/1.03  fof(f68,plain,(
% 4.02/1.03    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.02/1.03    inference(cnf_transformation,[],[f47])).
% 4.02/1.03  
% 4.02/1.03  cnf(c_10,plain,
% 4.02/1.03      ( ~ m1_pre_topc(X0,X1)
% 4.02/1.03      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 4.02/1.03      | v2_struct_0(X1)
% 4.02/1.03      | ~ l1_pre_topc(X1)
% 4.02/1.03      | ~ v2_pre_topc(X1) ),
% 4.02/1.03      inference(cnf_transformation,[],[f64]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1037,plain,
% 4.02/1.03      ( ~ m1_pre_topc(X0_50,X1_50)
% 4.02/1.03      | m1_subset_1(k4_tmap_1(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(X1_50) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_10]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1578,plain,
% 4.02/1.03      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 4.02/1.03      | m1_subset_1(k4_tmap_1(X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) = iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1037]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_26,negated_conjecture,
% 4.02/1.03      ( m1_pre_topc(sK2,sK1) ),
% 4.02/1.03      inference(cnf_transformation,[],[f77]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1021,negated_conjecture,
% 4.02/1.03      ( m1_pre_topc(sK2,sK1) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_26]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1594,plain,
% 4.02/1.03      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1021]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_23,negated_conjecture,
% 4.02/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 4.02/1.03      inference(cnf_transformation,[],[f80]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1024,negated_conjecture,
% 4.02/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_23]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1591,plain,
% 4.02/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1024]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6,plain,
% 4.02/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.02/1.03      | ~ m1_pre_topc(X3,X4)
% 4.02/1.03      | ~ m1_pre_topc(X3,X1)
% 4.02/1.03      | ~ m1_pre_topc(X1,X4)
% 4.02/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.02/1.03      | v2_struct_0(X4)
% 4.02/1.03      | v2_struct_0(X2)
% 4.02/1.03      | ~ l1_pre_topc(X4)
% 4.02/1.03      | ~ l1_pre_topc(X2)
% 4.02/1.03      | ~ v2_pre_topc(X4)
% 4.02/1.03      | ~ v2_pre_topc(X2)
% 4.02/1.03      | ~ v1_funct_1(X0)
% 4.02/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 4.02/1.03      inference(cnf_transformation,[],[f58]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1041,plain,
% 4.02/1.03      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 4.02/1.03      | ~ m1_pre_topc(X2_50,X0_50)
% 4.02/1.03      | ~ m1_pre_topc(X0_50,X3_50)
% 4.02/1.03      | ~ m1_pre_topc(X2_50,X3_50)
% 4.02/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | v2_struct_0(X3_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ l1_pre_topc(X3_50)
% 4.02/1.03      | ~ v2_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(X3_50)
% 4.02/1.03      | ~ v1_funct_1(X0_51)
% 4.02/1.03      | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_6]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1574,plain,
% 4.02/1.03      ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X3_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(X3_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X3_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1041]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_3512,plain,
% 4.02/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3)
% 4.02/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,sK2) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X1_50) != iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1591,c_1574]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_30,negated_conjecture,
% 4.02/1.03      ( ~ v2_struct_0(sK1) ),
% 4.02/1.03      inference(cnf_transformation,[],[f73]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_31,plain,
% 4.02/1.03      ( v2_struct_0(sK1) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_29,negated_conjecture,
% 4.02/1.03      ( v2_pre_topc(sK1) ),
% 4.02/1.03      inference(cnf_transformation,[],[f74]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_32,plain,
% 4.02/1.03      ( v2_pre_topc(sK1) = iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_28,negated_conjecture,
% 4.02/1.03      ( l1_pre_topc(sK1) ),
% 4.02/1.03      inference(cnf_transformation,[],[f75]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_33,plain,
% 4.02/1.03      ( l1_pre_topc(sK1) = iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_25,negated_conjecture,
% 4.02/1.03      ( v1_funct_1(sK3) ),
% 4.02/1.03      inference(cnf_transformation,[],[f78]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_36,plain,
% 4.02/1.03      ( v1_funct_1(sK3) = iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_24,negated_conjecture,
% 4.02/1.03      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 4.02/1.03      inference(cnf_transformation,[],[f79]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_37,plain,
% 4.02/1.03      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4365,plain,
% 4.02/1.03      ( l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3)
% 4.02/1.03      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,sK2) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X1_50) != iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_3512,c_31,c_32,c_33,c_36,c_37]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4366,plain,
% 4.02/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3)
% 4.02/1.03      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,sK2) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X1_50) != iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_4365]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4371,plain,
% 4.02/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
% 4.02/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1594,c_4366]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_13,plain,
% 4.02/1.03      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 4.02/1.03      inference(cnf_transformation,[],[f65]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1034,plain,
% 4.02/1.03      ( m1_pre_topc(X0_50,X0_50) | ~ l1_pre_topc(X0_50) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_13]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1581,plain,
% 4.02/1.03      ( m1_pre_topc(X0_50,X0_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1034]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_5,plain,
% 4.02/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.02/1.03      | ~ m1_pre_topc(X3,X1)
% 4.02/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.02/1.03      | v2_struct_0(X1)
% 4.02/1.03      | v2_struct_0(X2)
% 4.02/1.03      | ~ l1_pre_topc(X1)
% 4.02/1.03      | ~ l1_pre_topc(X2)
% 4.02/1.03      | ~ v2_pre_topc(X1)
% 4.02/1.03      | ~ v2_pre_topc(X2)
% 4.02/1.03      | ~ v1_funct_1(X0)
% 4.02/1.03      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 4.02/1.03      inference(cnf_transformation,[],[f57]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1042,plain,
% 4.02/1.03      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 4.02/1.03      | ~ m1_pre_topc(X2_50,X0_50)
% 4.02/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | v2_struct_0(X0_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ l1_pre_topc(X0_50)
% 4.02/1.03      | ~ v2_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(X0_50)
% 4.02/1.03      | ~ v1_funct_1(X0_51)
% 4.02/1.03      | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_5]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1573,plain,
% 4.02/1.03      ( k2_partfun1(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,u1_struct_0(X2_50)) = k2_tmap_1(X0_50,X1_50,X0_51,X2_50)
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1042]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_3229,plain,
% 4.02/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k2_tmap_1(sK2,sK1,sK3,X0_50)
% 4.02/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,sK2) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | v2_struct_0(sK2) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | l1_pre_topc(sK2) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK2) != iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1591,c_1573]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_27,negated_conjecture,
% 4.02/1.03      ( ~ v2_struct_0(sK2) ),
% 4.02/1.03      inference(cnf_transformation,[],[f76]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_34,plain,
% 4.02/1.03      ( v2_struct_0(sK2) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_35,plain,
% 4.02/1.03      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_3,plain,
% 4.02/1.03      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 4.02/1.03      inference(cnf_transformation,[],[f55]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1044,plain,
% 4.02/1.03      ( ~ m1_pre_topc(X0_50,X1_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | l1_pre_topc(X0_50) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1835,plain,
% 4.02/1.03      ( ~ m1_pre_topc(sK2,X0_50)
% 4.02/1.03      | ~ l1_pre_topc(X0_50)
% 4.02/1.03      | l1_pre_topc(sK2) ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1044]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1836,plain,
% 4.02/1.03      ( m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(sK2) = iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1835]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1838,plain,
% 4.02/1.03      ( m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | l1_pre_topc(sK2) = iProver_top ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1836]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_2,plain,
% 4.02/1.03      ( ~ m1_pre_topc(X0,X1)
% 4.02/1.03      | ~ l1_pre_topc(X1)
% 4.02/1.03      | ~ v2_pre_topc(X1)
% 4.02/1.03      | v2_pre_topc(X0) ),
% 4.02/1.03      inference(cnf_transformation,[],[f54]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1045,plain,
% 4.02/1.03      ( ~ m1_pre_topc(X0_50,X1_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(X1_50)
% 4.02/1.03      | v2_pre_topc(X0_50) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_2083,plain,
% 4.02/1.03      ( ~ m1_pre_topc(sK2,X0_50)
% 4.02/1.03      | ~ l1_pre_topc(X0_50)
% 4.02/1.03      | ~ v2_pre_topc(X0_50)
% 4.02/1.03      | v2_pre_topc(sK2) ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1045]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_2084,plain,
% 4.02/1.03      ( m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK2) = iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_2083]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_2086,plain,
% 4.02/1.03      ( m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK2) = iProver_top ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_2084]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_3238,plain,
% 4.02/1.03      ( m1_pre_topc(X0_50,sK2) != iProver_top
% 4.02/1.03      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k2_tmap_1(sK2,sK1,sK3,X0_50) ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_3229,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_1838,c_2086]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_3239,plain,
% 4.02/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k2_tmap_1(sK2,sK1,sK3,X0_50)
% 4.02/1.03      | m1_pre_topc(X0_50,sK2) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_3238]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_3244,plain,
% 4.02/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2)
% 4.02/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1581,c_3239]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1837,plain,
% 4.02/1.03      ( ~ m1_pre_topc(sK2,sK1) | ~ l1_pre_topc(sK1) | l1_pre_topc(sK2) ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1835]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_2085,plain,
% 4.02/1.03      ( ~ m1_pre_topc(sK2,sK1)
% 4.02/1.03      | ~ l1_pre_topc(sK1)
% 4.02/1.03      | ~ v2_pre_topc(sK1)
% 4.02/1.03      | v2_pre_topc(sK2) ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_2083]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1660,plain,
% 4.02/1.03      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
% 4.02/1.03      | ~ m1_pre_topc(X1_50,X0_50)
% 4.02/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
% 4.02/1.03      | v2_struct_0(X0_50)
% 4.02/1.03      | v2_struct_0(sK1)
% 4.02/1.03      | ~ l1_pre_topc(X0_50)
% 4.02/1.03      | ~ l1_pre_topc(sK1)
% 4.02/1.03      | ~ v2_pre_topc(X0_50)
% 4.02/1.03      | ~ v2_pre_topc(sK1)
% 4.02/1.03      | ~ v1_funct_1(X0_51)
% 4.02/1.03      | k2_partfun1(u1_struct_0(X0_50),u1_struct_0(sK1),X0_51,u1_struct_0(X1_50)) = k2_tmap_1(X0_50,sK1,X0_51,X1_50) ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1042]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1762,plain,
% 4.02/1.03      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 4.02/1.03      | ~ m1_pre_topc(X0_50,sK2)
% 4.02/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 4.02/1.03      | v2_struct_0(sK1)
% 4.02/1.03      | v2_struct_0(sK2)
% 4.02/1.03      | ~ l1_pre_topc(sK1)
% 4.02/1.03      | ~ l1_pre_topc(sK2)
% 4.02/1.03      | ~ v2_pre_topc(sK1)
% 4.02/1.03      | ~ v2_pre_topc(sK2)
% 4.02/1.03      | ~ v1_funct_1(sK3)
% 4.02/1.03      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k2_tmap_1(sK2,sK1,sK3,X0_50) ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1660]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_2181,plain,
% 4.02/1.03      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 4.02/1.03      | ~ m1_pre_topc(sK2,sK2)
% 4.02/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 4.02/1.03      | v2_struct_0(sK1)
% 4.02/1.03      | v2_struct_0(sK2)
% 4.02/1.03      | ~ l1_pre_topc(sK1)
% 4.02/1.03      | ~ l1_pre_topc(sK2)
% 4.02/1.03      | ~ v2_pre_topc(sK1)
% 4.02/1.03      | ~ v2_pre_topc(sK2)
% 4.02/1.03      | ~ v1_funct_1(sK3)
% 4.02/1.03      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1762]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_2874,plain,
% 4.02/1.03      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1034]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_3401,plain,
% 4.02/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_3244,c_30,c_29,c_28,c_27,c_26,c_25,c_24,c_23,c_1837,
% 4.02/1.03                 c_2085,c_2181,c_2874]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4373,plain,
% 4.02/1.03      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2)
% 4.02/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 4.02/1.03      inference(light_normalisation,[status(thm)],[c_4371,c_3401]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_2875,plain,
% 4.02/1.03      ( m1_pre_topc(sK2,sK2) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK2) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_2874]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4413,plain,
% 4.02/1.03      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_4373,c_31,c_32,c_33,c_35,c_1838,c_2875]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_7,plain,
% 4.02/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.02/1.03      | ~ m1_pre_topc(X3,X4)
% 4.02/1.03      | ~ m1_pre_topc(X1,X4)
% 4.02/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.02/1.03      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 4.02/1.03      | v2_struct_0(X4)
% 4.02/1.03      | v2_struct_0(X2)
% 4.02/1.03      | ~ l1_pre_topc(X4)
% 4.02/1.03      | ~ l1_pre_topc(X2)
% 4.02/1.03      | ~ v2_pre_topc(X4)
% 4.02/1.03      | ~ v2_pre_topc(X2)
% 4.02/1.03      | ~ v1_funct_1(X0) ),
% 4.02/1.03      inference(cnf_transformation,[],[f61]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1040,plain,
% 4.02/1.03      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 4.02/1.03      | ~ m1_pre_topc(X0_50,X2_50)
% 4.02/1.03      | ~ m1_pre_topc(X3_50,X2_50)
% 4.02/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 4.02/1.03      | m1_subset_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_50),u1_struct_0(X1_50))))
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | v2_struct_0(X2_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ l1_pre_topc(X2_50)
% 4.02/1.03      | ~ v2_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(X2_50)
% 4.02/1.03      | ~ v1_funct_1(X0_51) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_7]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1575,plain,
% 4.02/1.03      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 4.02/1.03      | m1_subset_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) = iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X3_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(X3_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X3_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1040]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4416,plain,
% 4.02/1.03      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | m1_subset_1(k2_tmap_1(sK2,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 4.02/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_4413,c_1575]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_38,plain,
% 4.02/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_5092,plain,
% 4.02/1.03      ( m1_subset_1(k2_tmap_1(sK2,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_4416,c_31,c_32,c_33,c_35,c_36,c_37,c_38]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1,plain,
% 4.02/1.03      ( ~ r2_funct_2(X0,X1,X2,X3)
% 4.02/1.03      | ~ v1_funct_2(X3,X0,X1)
% 4.02/1.03      | ~ v1_funct_2(X2,X0,X1)
% 4.02/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.02/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.02/1.03      | ~ v1_funct_1(X3)
% 4.02/1.03      | ~ v1_funct_1(X2)
% 4.02/1.03      | X2 = X3 ),
% 4.02/1.03      inference(cnf_transformation,[],[f52]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1046,plain,
% 4.02/1.03      ( ~ r2_funct_2(X0_52,X1_52,X0_51,X1_51)
% 4.02/1.03      | ~ v1_funct_2(X1_51,X0_52,X1_52)
% 4.02/1.03      | ~ v1_funct_2(X0_51,X0_52,X1_52)
% 4.02/1.03      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 4.02/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 4.02/1.03      | ~ v1_funct_1(X0_51)
% 4.02/1.03      | ~ v1_funct_1(X1_51)
% 4.02/1.03      | X0_51 = X1_51 ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1569,plain,
% 4.02/1.03      ( X0_51 = X1_51
% 4.02/1.03      | r2_funct_2(X0_52,X1_52,X0_51,X1_51) != iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 4.02/1.03      | v1_funct_2(X1_51,X0_52,X1_52) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 4.02/1.03      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top
% 4.02/1.03      | v1_funct_1(X1_51) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1046]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_2548,plain,
% 4.02/1.03      ( sK3 = X0_51
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) != iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1591,c_1569]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_2866,plain,
% 4.02/1.03      ( v1_funct_1(X0_51) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | sK3 = X0_51
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) != iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_2548,c_36,c_37]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_2867,plain,
% 4.02/1.03      ( sK3 = X0_51
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) != iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_2866]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_5102,plain,
% 4.02/1.03      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 4.02/1.03      | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_5092,c_2867]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_18,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
% 4.02/1.03      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 4.02/1.03      | ~ m1_pre_topc(X0,X3)
% 4.02/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 4.02/1.03      | v2_struct_0(X3)
% 4.02/1.03      | v2_struct_0(X1)
% 4.02/1.03      | v2_struct_0(X0)
% 4.02/1.03      | ~ l1_pre_topc(X3)
% 4.02/1.03      | ~ l1_pre_topc(X1)
% 4.02/1.03      | ~ v2_pre_topc(X3)
% 4.02/1.03      | ~ v2_pre_topc(X1)
% 4.02/1.03      | ~ v1_funct_1(X2) ),
% 4.02/1.03      inference(cnf_transformation,[],[f70]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1029,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,k3_tmap_1(X2_50,X1_50,X0_50,X0_50,X0_51))
% 4.02/1.03      | ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 4.02/1.03      | ~ m1_pre_topc(X0_50,X2_50)
% 4.02/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 4.02/1.03      | v2_struct_0(X2_50)
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | v2_struct_0(X0_50)
% 4.02/1.03      | ~ l1_pre_topc(X2_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(X2_50)
% 4.02/1.03      | ~ v2_pre_topc(X1_50)
% 4.02/1.03      | ~ v1_funct_1(X0_51) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_18]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1586,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,k3_tmap_1(X2_50,X1_50,X0_50,X0_50,X0_51)) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X2_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(X2_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X2_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1029]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4415,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top
% 4.02/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | v2_struct_0(sK2) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_4413,c_1586]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_8,plain,
% 4.02/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.02/1.03      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 4.02/1.03      | ~ m1_pre_topc(X4,X3)
% 4.02/1.03      | ~ m1_pre_topc(X1,X3)
% 4.02/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.02/1.03      | v2_struct_0(X3)
% 4.02/1.03      | v2_struct_0(X2)
% 4.02/1.03      | ~ l1_pre_topc(X3)
% 4.02/1.03      | ~ l1_pre_topc(X2)
% 4.02/1.03      | ~ v2_pre_topc(X3)
% 4.02/1.03      | ~ v2_pre_topc(X2)
% 4.02/1.03      | ~ v1_funct_1(X0) ),
% 4.02/1.03      inference(cnf_transformation,[],[f60]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1039,plain,
% 4.02/1.03      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 4.02/1.03      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50))
% 4.02/1.03      | ~ m1_pre_topc(X0_50,X2_50)
% 4.02/1.03      | ~ m1_pre_topc(X3_50,X2_50)
% 4.02/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 4.02/1.03      | v2_struct_0(X2_50)
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | ~ l1_pre_topc(X2_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(X2_50)
% 4.02/1.03      | ~ v2_pre_topc(X1_50)
% 4.02/1.03      | ~ v1_funct_1(X0_51) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1576,plain,
% 4.02/1.03      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | v1_funct_2(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51),u1_struct_0(X3_50),u1_struct_0(X1_50)) = iProver_top
% 4.02/1.03      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X2_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(X2_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X2_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1039]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4417,plain,
% 4.02/1.03      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 4.02/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_4413,c_1576]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_9,plain,
% 4.02/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.02/1.03      | ~ m1_pre_topc(X3,X4)
% 4.02/1.03      | ~ m1_pre_topc(X1,X4)
% 4.02/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.02/1.03      | v2_struct_0(X4)
% 4.02/1.03      | v2_struct_0(X2)
% 4.02/1.03      | ~ l1_pre_topc(X4)
% 4.02/1.03      | ~ l1_pre_topc(X2)
% 4.02/1.03      | ~ v2_pre_topc(X4)
% 4.02/1.03      | ~ v2_pre_topc(X2)
% 4.02/1.03      | ~ v1_funct_1(X0)
% 4.02/1.03      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 4.02/1.03      inference(cnf_transformation,[],[f59]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1038,plain,
% 4.02/1.03      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 4.02/1.03      | ~ m1_pre_topc(X0_50,X2_50)
% 4.02/1.03      | ~ m1_pre_topc(X3_50,X2_50)
% 4.02/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | v2_struct_0(X2_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ l1_pre_topc(X2_50)
% 4.02/1.03      | ~ v2_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(X2_50)
% 4.02/1.03      | ~ v1_funct_1(X0_51)
% 4.02/1.03      | v1_funct_1(k3_tmap_1(X2_50,X1_50,X0_50,X3_50,X0_51)) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_9]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1577,plain,
% 4.02/1.03      ( v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X2_50,X3_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,X3_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X3_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(X3_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X3_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top
% 4.02/1.03      | v1_funct_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51)) = iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1038]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_3404,plain,
% 4.02/1.03      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X1_50) != iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3)) = iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1591,c_1577]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1661,plain,
% 4.02/1.03      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(sK1))
% 4.02/1.03      | ~ m1_pre_topc(X0_50,X1_50)
% 4.02/1.03      | ~ m1_pre_topc(X2_50,X1_50)
% 4.02/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(sK1))))
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | v2_struct_0(sK1)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ l1_pre_topc(sK1)
% 4.02/1.03      | ~ v2_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(sK1)
% 4.02/1.03      | ~ v1_funct_1(X0_51)
% 4.02/1.03      | v1_funct_1(k3_tmap_1(X1_50,sK1,X0_50,X2_50,X0_51)) ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1038]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1775,plain,
% 4.02/1.03      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 4.02/1.03      | ~ m1_pre_topc(X0_50,X1_50)
% 4.02/1.03      | ~ m1_pre_topc(sK2,X1_50)
% 4.02/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | v2_struct_0(sK1)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ l1_pre_topc(sK1)
% 4.02/1.03      | ~ v2_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(sK1)
% 4.02/1.03      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3))
% 4.02/1.03      | ~ v1_funct_1(sK3) ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1661]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1776,plain,
% 4.02/1.03      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X1_50) != iProver_top
% 4.02/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3)) = iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1775]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_3505,plain,
% 4.02/1.03      ( v1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3)) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X1_50) != iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_3404,c_31,c_32,c_33,c_36,c_37,c_38,c_1776]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_3506,plain,
% 4.02/1.03      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X1_50) != iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v1_funct_1(k3_tmap_1(X1_50,sK1,sK2,X0_50,sK3)) = iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_3505]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4418,plain,
% 4.02/1.03      ( m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_4413,c_3506]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4033,plain,
% 4.02/1.03      ( k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51) = sK3
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51)) != iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(X1_50),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_2(k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top
% 4.02/1.03      | v1_funct_1(k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51)) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1575,c_2867]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4504,plain,
% 4.02/1.03      ( v2_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 4.02/1.03      | v1_funct_2(k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(X1_50),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51)) != iProver_top
% 4.02/1.03      | k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51) = sK3
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top
% 4.02/1.03      | v1_funct_1(k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51)) != iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_4033,c_31,c_32,c_33]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4505,plain,
% 4.02/1.03      ( k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51) = sK3
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51)) != iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(X1_50),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_2(k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_50),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top
% 4.02/1.03      | v1_funct_1(k3_tmap_1(X0_50,sK1,X1_50,sK2,X0_51)) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_4504]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4509,plain,
% 4.02/1.03      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 4.02/1.03      | v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) != iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_4413,c_4505]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4510,plain,
% 4.02/1.03      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 4.02/1.03      | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(light_normalisation,[status(thm)],[c_4509,c_4413]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4511,plain,
% 4.02/1.03      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 4.02/1.03      | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(demodulation,[status(thm)],[c_4510,c_4413]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_5208,plain,
% 4.02/1.03      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_5102,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_4415,
% 4.02/1.03                 c_4417,c_4418,c_4511]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_15,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 4.02/1.03      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 4.02/1.03      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 4.02/1.03      | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
% 4.02/1.03      | ~ m1_pre_topc(X0,X2)
% 4.02/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 4.02/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 4.02/1.03      | v2_struct_0(X1)
% 4.02/1.03      | v2_struct_0(X2)
% 4.02/1.03      | v2_struct_0(X0)
% 4.02/1.03      | ~ l1_pre_topc(X1)
% 4.02/1.03      | ~ l1_pre_topc(X2)
% 4.02/1.03      | ~ v2_pre_topc(X1)
% 4.02/1.03      | ~ v2_pre_topc(X2)
% 4.02/1.03      | ~ v1_funct_1(X3)
% 4.02/1.03      | ~ v1_funct_1(X4) ),
% 4.02/1.03      inference(cnf_transformation,[],[f67]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1032,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
% 4.02/1.03      | ~ v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 4.02/1.03      | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
% 4.02/1.03      | r2_hidden(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X0_50))
% 4.02/1.03      | ~ m1_pre_topc(X0_50,X2_50)
% 4.02/1.03      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 4.02/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
% 4.02/1.03      | v2_struct_0(X2_50)
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | v2_struct_0(X0_50)
% 4.02/1.03      | ~ l1_pre_topc(X2_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(X2_50)
% 4.02/1.03      | ~ v2_pre_topc(X1_50)
% 4.02/1.03      | ~ v1_funct_1(X0_51)
% 4.02/1.03      | ~ v1_funct_1(X1_51) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_15]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1583,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | r2_hidden(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X0_50)) = iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X2_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(X2_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X2_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top
% 4.02/1.03      | v1_funct_1(X1_51) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1032]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_5218,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK2)) = iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | v2_struct_0(sK2) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | l1_pre_topc(sK2) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK2) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_5208,c_1583]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6063,plain,
% 4.02/1.03      ( v1_funct_1(X0_51) != iProver_top
% 4.02/1.03      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK2)) = iProver_top
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_5218,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_1838,
% 4.02/1.03                 c_2086,c_2875]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6064,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK2)) = iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_6063]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_16,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 4.02/1.03      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 4.02/1.03      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 4.02/1.03      | ~ m1_pre_topc(X0,X2)
% 4.02/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 4.02/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 4.02/1.03      | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2))
% 4.02/1.03      | v2_struct_0(X1)
% 4.02/1.03      | v2_struct_0(X2)
% 4.02/1.03      | v2_struct_0(X0)
% 4.02/1.03      | ~ l1_pre_topc(X1)
% 4.02/1.03      | ~ l1_pre_topc(X2)
% 4.02/1.03      | ~ v2_pre_topc(X1)
% 4.02/1.03      | ~ v2_pre_topc(X2)
% 4.02/1.03      | ~ v1_funct_1(X3)
% 4.02/1.03      | ~ v1_funct_1(X4) ),
% 4.02/1.03      inference(cnf_transformation,[],[f66]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1031,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
% 4.02/1.03      | ~ v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 4.02/1.03      | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
% 4.02/1.03      | ~ m1_pre_topc(X0_50,X2_50)
% 4.02/1.03      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 4.02/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
% 4.02/1.03      | m1_subset_1(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X2_50))
% 4.02/1.03      | v2_struct_0(X2_50)
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | v2_struct_0(X0_50)
% 4.02/1.03      | ~ l1_pre_topc(X2_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(X2_50)
% 4.02/1.03      | ~ v2_pre_topc(X1_50)
% 4.02/1.03      | ~ v1_funct_1(X0_51)
% 4.02/1.03      | ~ v1_funct_1(X1_51) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_16]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1584,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,X2_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 4.02/1.03      | m1_subset_1(sK0(X1_50,X2_50,X0_50,X0_51,X1_51),u1_struct_0(X2_50)) = iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X2_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(X2_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X2_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top
% 4.02/1.03      | v1_funct_1(X1_51) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1031]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_5217,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK2)) = iProver_top
% 4.02/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | v2_struct_0(sK2) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | l1_pre_topc(sK2) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK2) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_5208,c_1584]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_5889,plain,
% 4.02/1.03      ( v1_funct_1(X0_51) != iProver_top
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK2)) = iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_5217,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_1838,
% 4.02/1.03                 c_2086,c_2875]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_5890,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK2)) = iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_5889]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4,plain,
% 4.02/1.03      ( ~ m1_pre_topc(X0,X1)
% 4.02/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.02/1.03      | m1_subset_1(X2,u1_struct_0(X1))
% 4.02/1.03      | v2_struct_0(X1)
% 4.02/1.03      | v2_struct_0(X0)
% 4.02/1.03      | ~ l1_pre_topc(X1) ),
% 4.02/1.03      inference(cnf_transformation,[],[f56]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1043,plain,
% 4.02/1.03      ( ~ m1_pre_topc(X0_50,X1_50)
% 4.02/1.03      | ~ m1_subset_1(X0_51,u1_struct_0(X0_50))
% 4.02/1.03      | m1_subset_1(X0_51,u1_struct_0(X1_50))
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | v2_struct_0(X0_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_4]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1572,plain,
% 4.02/1.03      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,u1_struct_0(X1_50)) = iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1043]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_5894,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X0_50)) = iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_struct_0(sK2) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_5890,c_1572]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6042,plain,
% 4.02/1.03      ( v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X0_50)) = iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_5894,c_34]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6043,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X0_50)) = iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_6042]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6047,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X1_50)) = iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_6043,c_1572]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1072,plain,
% 4.02/1.03      ( m1_pre_topc(X0_50,X1_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) = iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1044]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6662,plain,
% 4.02/1.03      ( v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X1_50)) = iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_6047,c_1072]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6663,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,X1_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X1_50)) = iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_6662]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6666,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK1)) = iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | v2_struct_0(sK2) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1594,c_6663]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6670,plain,
% 4.02/1.03      ( m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK1)) = iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_6666,c_31,c_33,c_34,c_35,c_1838,c_2875]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6671,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK1)) = iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_6670]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_20,plain,
% 4.02/1.03      ( ~ r2_hidden(X0,u1_struct_0(X1))
% 4.02/1.03      | ~ m1_pre_topc(X1,X2)
% 4.02/1.03      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 4.02/1.03      | v2_struct_0(X2)
% 4.02/1.03      | v2_struct_0(X1)
% 4.02/1.03      | ~ l1_pre_topc(X2)
% 4.02/1.03      | ~ v2_pre_topc(X2)
% 4.02/1.03      | k1_funct_1(k4_tmap_1(X2,X1),X0) = X0 ),
% 4.02/1.03      inference(cnf_transformation,[],[f72]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1027,plain,
% 4.02/1.03      ( ~ r2_hidden(X0_51,u1_struct_0(X0_50))
% 4.02/1.03      | ~ m1_pre_topc(X0_50,X1_50)
% 4.02/1.03      | ~ m1_subset_1(X0_51,u1_struct_0(X1_50))
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | v2_struct_0(X0_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(X1_50)
% 4.02/1.03      | k1_funct_1(k4_tmap_1(X1_50,X0_50),X0_51) = X0_51 ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_20]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1588,plain,
% 4.02/1.03      ( k1_funct_1(k4_tmap_1(X0_50,X1_50),X0_51) = X0_51
% 4.02/1.03      | r2_hidden(X0_51,u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,u1_struct_0(X0_50)) != iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1027]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6674,plain,
% 4.02/1.03      ( k1_funct_1(k4_tmap_1(sK1,X0_50),sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X0_50)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,sK1) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_6671,c_1588]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6688,plain,
% 4.02/1.03      ( v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,sK1) != iProver_top
% 4.02/1.03      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X0_50)) != iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | k1_funct_1(k4_tmap_1(sK1,X0_50),sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_6674,c_31,c_32,c_33]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6689,plain,
% 4.02/1.03      ( k1_funct_1(k4_tmap_1(sK1,X0_50),sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(X0_50)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X0_50,sK1) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_6688]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6692,plain,
% 4.02/1.03      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(sK2) = iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_6064,c_6689]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6722,plain,
% 4.02/1.03      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_6692,c_34,c_35]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6723,plain,
% 4.02/1.03      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_6722]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6727,plain,
% 4.02/1.03      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 4.02/1.03      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1578,c_6723]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_17,plain,
% 4.02/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.02/1.03      | ~ r2_hidden(X3,u1_struct_0(X4))
% 4.02/1.03      | ~ m1_pre_topc(X1,X5)
% 4.02/1.03      | ~ m1_pre_topc(X4,X5)
% 4.02/1.03      | ~ m1_pre_topc(X4,X1)
% 4.02/1.03      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 4.02/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.02/1.03      | v2_struct_0(X5)
% 4.02/1.03      | v2_struct_0(X2)
% 4.02/1.03      | v2_struct_0(X1)
% 4.02/1.03      | v2_struct_0(X4)
% 4.02/1.03      | ~ l1_pre_topc(X5)
% 4.02/1.03      | ~ l1_pre_topc(X2)
% 4.02/1.03      | ~ v2_pre_topc(X5)
% 4.02/1.03      | ~ v2_pre_topc(X2)
% 4.02/1.03      | ~ v1_funct_1(X0)
% 4.02/1.03      | k1_funct_1(k3_tmap_1(X5,X2,X1,X4,X0),X3) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,X3) ),
% 4.02/1.03      inference(cnf_transformation,[],[f69]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1030,plain,
% 4.02/1.03      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 4.02/1.03      | ~ r2_hidden(X1_51,u1_struct_0(X2_50))
% 4.02/1.03      | ~ m1_pre_topc(X2_50,X0_50)
% 4.02/1.03      | ~ m1_pre_topc(X0_50,X3_50)
% 4.02/1.03      | ~ m1_pre_topc(X2_50,X3_50)
% 4.02/1.03      | ~ m1_subset_1(X1_51,u1_struct_0(X0_50))
% 4.02/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 4.02/1.03      | v2_struct_0(X2_50)
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | v2_struct_0(X0_50)
% 4.02/1.03      | v2_struct_0(X3_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ l1_pre_topc(X3_50)
% 4.02/1.03      | ~ v2_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(X3_50)
% 4.02/1.03      | ~ v1_funct_1(X0_51)
% 4.02/1.03      | k1_funct_1(k3_tmap_1(X3_50,X1_50,X0_50,X2_50,X0_51),X1_51) = k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,X1_51) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_17]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1585,plain,
% 4.02/1.03      ( k1_funct_1(k3_tmap_1(X0_50,X1_50,X2_50,X3_50,X0_51),X1_51) = k3_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),X0_51,X1_51)
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | r2_hidden(X1_51,u1_struct_0(X3_50)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X3_50,X2_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X3_50,X0_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X1_51,u1_struct_0(X2_50)) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 4.02/1.03      | v2_struct_0(X2_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X3_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1030]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4053,plain,
% 4.02/1.03      ( k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),X0_51) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51)
% 4.02/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | r2_hidden(X0_51,u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X1_50,sK2) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | v2_struct_0(sK2) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1591,c_1585]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4379,plain,
% 4.02/1.03      ( l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X1_50,sK2) != iProver_top
% 4.02/1.03      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 4.02/1.03      | r2_hidden(X0_51,u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),X0_51) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51)
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_4053,c_31,c_32,c_33,c_34,c_36,c_37]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4380,plain,
% 4.02/1.03      ( k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,X1_50,sK3),X0_51) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51)
% 4.02/1.03      | r2_hidden(X0_51,u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X1_50,X0_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(X1_50,sK2) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,u1_struct_0(sK2)) != iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_4379]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6068,plain,
% 4.02/1.03      ( k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,X0_51)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_51))
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK2)) != iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_struct_0(sK2) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_6064,c_4380]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6434,plain,
% 4.02/1.03      ( v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,X0_51)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_51))
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_6068,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_1838,
% 4.02/1.03                 c_2086,c_2875,c_5217]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6435,plain,
% 4.02/1.03      ( k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,X0_51)) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_51))
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_6434]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6439,plain,
% 4.02/1.03      ( k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 4.02/1.03      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1578,c_6435]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_12,plain,
% 4.02/1.03      ( ~ m1_pre_topc(X0,X1)
% 4.02/1.03      | v2_struct_0(X1)
% 4.02/1.03      | ~ l1_pre_topc(X1)
% 4.02/1.03      | ~ v2_pre_topc(X1)
% 4.02/1.03      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 4.02/1.03      inference(cnf_transformation,[],[f62]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1035,plain,
% 4.02/1.03      ( ~ m1_pre_topc(X0_50,X1_50)
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(X1_50)
% 4.02/1.03      | v1_funct_1(k4_tmap_1(X1_50,X0_50)) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_12]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_2419,plain,
% 4.02/1.03      ( ~ m1_pre_topc(sK2,sK1)
% 4.02/1.03      | v2_struct_0(sK1)
% 4.02/1.03      | ~ l1_pre_topc(sK1)
% 4.02/1.03      | ~ v2_pre_topc(sK1)
% 4.02/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1035]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_2420,plain,
% 4.02/1.03      ( m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_2419]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_2934,plain,
% 4.02/1.03      ( k4_tmap_1(sK1,sK2) = sK3
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
% 4.02/1.03      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1578,c_2867]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_21,negated_conjecture,
% 4.02/1.03      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
% 4.02/1.03      inference(cnf_transformation,[],[f82]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_42,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1049,plain,( X0_51 = X0_51 ),theory(equality) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1066,plain,
% 4.02/1.03      ( sK3 = sK3 ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1049]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1051,plain,
% 4.02/1.03      ( ~ r2_funct_2(X0_52,X1_52,X0_51,X1_51)
% 4.02/1.03      | r2_funct_2(X0_52,X1_52,X2_51,X3_51)
% 4.02/1.03      | X2_51 != X0_51
% 4.02/1.03      | X3_51 != X1_51 ),
% 4.02/1.03      theory(equality) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1748,plain,
% 4.02/1.03      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_51,X1_51)
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
% 4.02/1.03      | k4_tmap_1(sK1,sK2) != X0_51
% 4.02/1.03      | sK3 != X1_51 ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1051]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1749,plain,
% 4.02/1.03      ( k4_tmap_1(sK1,sK2) != X0_51
% 4.02/1.03      | sK3 != X1_51
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_51,X1_51) != iProver_top
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1748]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1751,plain,
% 4.02/1.03      ( k4_tmap_1(sK1,sK2) != sK3
% 4.02/1.03      | sK3 != sK3
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) != iProver_top ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1749]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_0,plain,
% 4.02/1.03      ( r2_funct_2(X0,X1,X2,X2)
% 4.02/1.03      | ~ v1_funct_2(X2,X0,X1)
% 4.02/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.02/1.03      | ~ v1_funct_1(X2) ),
% 4.02/1.03      inference(cnf_transformation,[],[f83]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1047,plain,
% 4.02/1.03      ( r2_funct_2(X0_52,X1_52,X0_51,X0_51)
% 4.02/1.03      | ~ v1_funct_2(X0_51,X0_52,X1_52)
% 4.02/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 4.02/1.03      | ~ v1_funct_1(X0_51) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1568,plain,
% 4.02/1.03      ( r2_funct_2(X0_52,X1_52,X0_51,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1047]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_2054,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) = iProver_top
% 4.02/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1591,c_1568]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_3021,plain,
% 4.02/1.03      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_2934,c_31,c_32,c_33,c_35,c_36,c_37,c_42,c_1066,c_1751,
% 4.02/1.03                 c_2054,c_2420]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_3022,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
% 4.02/1.03      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_3021]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_11,plain,
% 4.02/1.03      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 4.02/1.03      | ~ m1_pre_topc(X1,X0)
% 4.02/1.03      | v2_struct_0(X0)
% 4.02/1.03      | ~ l1_pre_topc(X0)
% 4.02/1.03      | ~ v2_pre_topc(X0) ),
% 4.02/1.03      inference(cnf_transformation,[],[f63]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1036,plain,
% 4.02/1.03      ( v1_funct_2(k4_tmap_1(X0_50,X1_50),u1_struct_0(X1_50),u1_struct_0(X0_50))
% 4.02/1.03      | ~ m1_pre_topc(X1_50,X0_50)
% 4.02/1.03      | v2_struct_0(X0_50)
% 4.02/1.03      | ~ l1_pre_topc(X0_50)
% 4.02/1.03      | ~ v2_pre_topc(X0_50) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_11]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4021,plain,
% 4.02/1.03      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 4.02/1.03      | ~ m1_pre_topc(sK2,sK1)
% 4.02/1.03      | v2_struct_0(sK1)
% 4.02/1.03      | ~ l1_pre_topc(sK1)
% 4.02/1.03      | ~ v2_pre_topc(sK1) ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1036]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4022,plain,
% 4.02/1.03      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4021]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6459,plain,
% 4.02/1.03      ( l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_6439,c_31,c_32,c_33,c_35,c_36,c_37,c_42,c_1066,c_1751,
% 4.02/1.03                 c_2054,c_2420,c_2934,c_4022]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6460,plain,
% 4.02/1.03      ( k1_funct_1(k3_tmap_1(X0_50,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_6459]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6465,plain,
% 4.02/1.03      ( k1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1594,c_6460]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_5215,plain,
% 4.02/1.03      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3 ),
% 4.02/1.03      inference(demodulation,[status(thm)],[c_5208,c_4413]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_22,negated_conjecture,
% 4.02/1.03      ( ~ r2_hidden(X0,u1_struct_0(sK2))
% 4.02/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 4.02/1.03      | k1_funct_1(sK3,X0) = X0 ),
% 4.02/1.03      inference(cnf_transformation,[],[f81]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1025,negated_conjecture,
% 4.02/1.03      ( ~ r2_hidden(X0_51,u1_struct_0(sK2))
% 4.02/1.03      | ~ m1_subset_1(X0_51,u1_struct_0(sK1))
% 4.02/1.03      | k1_funct_1(sK3,X0_51) = X0_51 ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_22]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1590,plain,
% 4.02/1.03      ( k1_funct_1(sK3,X0_51) = X0_51
% 4.02/1.03      | r2_hidden(X0_51,u1_struct_0(sK2)) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,u1_struct_0(sK1)) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1025]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6067,plain,
% 4.02/1.03      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_51),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_6064,c_1590]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6309,plain,
% 4.02/1.03      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_6043,c_6067]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6312,plain,
% 4.02/1.03      ( v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_6309,c_31,c_33,c_35]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6313,plain,
% 4.02/1.03      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_51)) = sK0(sK1,sK2,sK2,sK3,X0_51)
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top ),
% 4.02/1.03      inference(renaming,[status(thm)],[c_6312]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6317,plain,
% 4.02/1.03      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 4.02/1.03      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1578,c_6313]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6448,plain,
% 4.02/1.03      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_6317,c_31,c_32,c_33,c_35,c_36,c_37,c_42,c_1066,c_1751,
% 4.02/1.03                 c_2054,c_2420,c_2934,c_4022]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6468,plain,
% 4.02/1.03      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 4.02/1.03      inference(light_normalisation,[status(thm)],[c_6465,c_5215,c_6448]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6466,plain,
% 4.02/1.03      ( k1_funct_1(k3_tmap_1(sK2,sK1,sK2,sK2,sK3),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 4.02/1.03      | v2_struct_0(sK2) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK2) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK2) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1581,c_6460]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4372,plain,
% 4.02/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_50)) = k3_tmap_1(X0_50,sK1,sK2,X0_50,sK3)
% 4.02/1.03      | m1_pre_topc(X0_50,sK2) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,X0_50) != iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1581,c_4366]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4500,plain,
% 4.02/1.03      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK2,sK2,sK3)
% 4.02/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 4.02/1.03      | v2_struct_0(sK2) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK2) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK2) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_1581,c_4372]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4501,plain,
% 4.02/1.03      ( k3_tmap_1(sK2,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2)
% 4.02/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 4.02/1.03      | v2_struct_0(sK2) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK2) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK2) != iProver_top ),
% 4.02/1.03      inference(light_normalisation,[status(thm)],[c_4500,c_3401]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4605,plain,
% 4.02/1.03      ( k3_tmap_1(sK2,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_4501,c_32,c_33,c_34,c_35,c_1838,c_2086,c_2875]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_5213,plain,
% 4.02/1.03      ( k3_tmap_1(sK2,sK1,sK2,sK2,sK3) = sK3 ),
% 4.02/1.03      inference(demodulation,[status(thm)],[c_5208,c_4605]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6467,plain,
% 4.02/1.03      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 4.02/1.03      | v2_struct_0(sK2) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK2) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK2) != iProver_top ),
% 4.02/1.03      inference(light_normalisation,[status(thm)],[c_6466,c_5213,c_6448]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6472,plain,
% 4.02/1.03      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 4.02/1.03      inference(global_propositional_subsumption,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_6468,c_32,c_33,c_34,c_35,c_1838,c_2086,c_6467]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_14,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 4.02/1.03      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 4.02/1.03      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 4.02/1.03      | ~ m1_pre_topc(X0,X2)
% 4.02/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 4.02/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 4.02/1.03      | v2_struct_0(X1)
% 4.02/1.03      | v2_struct_0(X2)
% 4.02/1.03      | v2_struct_0(X0)
% 4.02/1.03      | ~ l1_pre_topc(X1)
% 4.02/1.03      | ~ l1_pre_topc(X2)
% 4.02/1.03      | ~ v2_pre_topc(X1)
% 4.02/1.03      | ~ v2_pre_topc(X2)
% 4.02/1.03      | ~ v1_funct_1(X3)
% 4.02/1.03      | ~ v1_funct_1(X4)
% 4.02/1.03      | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK0(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK0(X1,X2,X0,X3,X4)) ),
% 4.02/1.03      inference(cnf_transformation,[],[f68]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1033,plain,
% 4.02/1.03      ( r2_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),k2_tmap_1(X2_50,X1_50,X0_51,X0_50),X1_51)
% 4.02/1.03      | ~ v1_funct_2(X1_51,u1_struct_0(X0_50),u1_struct_0(X1_50))
% 4.02/1.03      | ~ v1_funct_2(X0_51,u1_struct_0(X2_50),u1_struct_0(X1_50))
% 4.02/1.03      | ~ m1_pre_topc(X0_50,X2_50)
% 4.02/1.03      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50))))
% 4.02/1.03      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50))))
% 4.02/1.03      | v2_struct_0(X2_50)
% 4.02/1.03      | v2_struct_0(X1_50)
% 4.02/1.03      | v2_struct_0(X0_50)
% 4.02/1.03      | ~ l1_pre_topc(X2_50)
% 4.02/1.03      | ~ l1_pre_topc(X1_50)
% 4.02/1.03      | ~ v2_pre_topc(X2_50)
% 4.02/1.03      | ~ v2_pre_topc(X1_50)
% 4.02/1.03      | ~ v1_funct_1(X0_51)
% 4.02/1.03      | ~ v1_funct_1(X1_51)
% 4.02/1.03      | k3_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),X0_51,sK0(X1_50,X2_50,X0_50,X0_51,X1_51)) != k1_funct_1(X1_51,sK0(X1_50,X2_50,X0_50,X0_51,X1_51)) ),
% 4.02/1.03      inference(subtyping,[status(esa)],[c_14]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_1582,plain,
% 4.02/1.03      ( k3_funct_2(u1_struct_0(X0_50),u1_struct_0(X1_50),X0_51,sK0(X1_50,X0_50,X2_50,X0_51,X1_51)) != k1_funct_1(X1_51,sK0(X1_50,X0_50,X2_50,X0_51,X1_51))
% 4.02/1.03      | r2_funct_2(u1_struct_0(X2_50),u1_struct_0(X1_50),k2_tmap_1(X0_50,X1_50,X0_51,X2_50),X1_51) = iProver_top
% 4.02/1.03      | v1_funct_2(X1_51,u1_struct_0(X2_50),u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | v1_funct_2(X0_51,u1_struct_0(X0_50),u1_struct_0(X1_50)) != iProver_top
% 4.02/1.03      | m1_pre_topc(X2_50,X0_50) != iProver_top
% 4.02/1.03      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_50),u1_struct_0(X1_50)))) != iProver_top
% 4.02/1.03      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_50),u1_struct_0(X1_50)))) != iProver_top
% 4.02/1.03      | v2_struct_0(X2_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X1_50) = iProver_top
% 4.02/1.03      | v2_struct_0(X0_50) = iProver_top
% 4.02/1.03      | l1_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | l1_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X1_50) != iProver_top
% 4.02/1.03      | v2_pre_topc(X0_50) != iProver_top
% 4.02/1.03      | v1_funct_1(X0_51) != iProver_top
% 4.02/1.03      | v1_funct_1(X1_51) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_1033]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6478,plain,
% 4.02/1.03      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),k4_tmap_1(sK1,sK2)) = iProver_top
% 4.02/1.03      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 4.02/1.03      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | v2_struct_0(sK2) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | l1_pre_topc(sK2) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK2) != iProver_top
% 4.02/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(superposition,[status(thm)],[c_6472,c_1582]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_6479,plain,
% 4.02/1.03      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 4.02/1.03      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 4.02/1.03      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 4.02/1.03      | m1_pre_topc(sK2,sK2) != iProver_top
% 4.02/1.03      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | v2_struct_0(sK2) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | l1_pre_topc(sK2) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK2) != iProver_top
% 4.02/1.03      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 4.02/1.03      | v1_funct_1(sK3) != iProver_top ),
% 4.02/1.03      inference(light_normalisation,[status(thm)],[c_6478,c_5208]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4920,plain,
% 4.02/1.03      ( ~ m1_pre_topc(sK2,sK1)
% 4.02/1.03      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 4.02/1.03      | v2_struct_0(sK1)
% 4.02/1.03      | ~ l1_pre_topc(sK1)
% 4.02/1.03      | ~ v2_pre_topc(sK1) ),
% 4.02/1.03      inference(instantiation,[status(thm)],[c_1037]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(c_4921,plain,
% 4.02/1.03      ( m1_pre_topc(sK2,sK1) != iProver_top
% 4.02/1.03      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 4.02/1.03      | v2_struct_0(sK1) = iProver_top
% 4.02/1.03      | l1_pre_topc(sK1) != iProver_top
% 4.02/1.03      | v2_pre_topc(sK1) != iProver_top ),
% 4.02/1.03      inference(predicate_to_equality,[status(thm)],[c_4920]) ).
% 4.02/1.03  
% 4.02/1.03  cnf(contradiction,plain,
% 4.02/1.03      ( $false ),
% 4.02/1.03      inference(minisat,
% 4.02/1.03                [status(thm)],
% 4.02/1.03                [c_6727,c_6479,c_4921,c_4022,c_3022,c_2875,c_2420,c_2086,
% 4.02/1.03                 c_1838,c_38,c_37,c_36,c_35,c_34,c_33,c_32,c_31]) ).
% 4.02/1.03  
% 4.02/1.03  
% 4.02/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 4.02/1.03  
% 4.02/1.03  ------                               Statistics
% 4.02/1.03  
% 4.02/1.03  ------ General
% 4.02/1.03  
% 4.02/1.03  abstr_ref_over_cycles:                  0
% 4.02/1.03  abstr_ref_under_cycles:                 0
% 4.02/1.03  gc_basic_clause_elim:                   0
% 4.02/1.03  forced_gc_time:                         0
% 4.02/1.03  parsing_time:                           0.015
% 4.02/1.03  unif_index_cands_time:                  0.
% 4.02/1.03  unif_index_add_time:                    0.
% 4.02/1.03  orderings_time:                         0.
% 4.02/1.03  out_proof_time:                         0.024
% 4.02/1.03  total_time:                             0.472
% 4.02/1.03  num_of_symbols:                         57
% 4.02/1.03  num_of_terms:                           14694
% 4.02/1.03  
% 4.02/1.03  ------ Preprocessing
% 4.02/1.03  
% 4.02/1.03  num_of_splits:                          0
% 4.02/1.03  num_of_split_atoms:                     0
% 4.02/1.03  num_of_reused_defs:                     0
% 4.02/1.03  num_eq_ax_congr_red:                    54
% 4.02/1.03  num_of_sem_filtered_clauses:            1
% 4.02/1.03  num_of_subtypes:                        4
% 4.02/1.03  monotx_restored_types:                  0
% 4.02/1.03  sat_num_of_epr_types:                   0
% 4.02/1.03  sat_num_of_non_cyclic_types:            0
% 4.02/1.03  sat_guarded_non_collapsed_types:        1
% 4.02/1.03  num_pure_diseq_elim:                    0
% 4.02/1.03  simp_replaced_by:                       0
% 4.02/1.03  res_preprocessed:                       112
% 4.02/1.03  prep_upred:                             0
% 4.02/1.03  prep_unflattend:                        30
% 4.02/1.03  smt_new_axioms:                         0
% 4.02/1.03  pred_elim_cands:                        9
% 4.02/1.03  pred_elim:                              0
% 4.02/1.03  pred_elim_cl:                           0
% 4.02/1.03  pred_elim_cycles:                       2
% 4.02/1.03  merged_defs:                            0
% 4.02/1.03  merged_defs_ncl:                        0
% 4.02/1.03  bin_hyper_res:                          0
% 4.02/1.03  prep_cycles:                            3
% 4.02/1.03  pred_elim_time:                         0.03
% 4.02/1.03  splitting_time:                         0.
% 4.02/1.03  sem_filter_time:                        0.
% 4.02/1.03  monotx_time:                            0.
% 4.02/1.03  subtype_inf_time:                       0.001
% 4.02/1.03  
% 4.02/1.03  ------ Problem properties
% 4.02/1.03  
% 4.02/1.03  clauses:                                31
% 4.02/1.03  conjectures:                            10
% 4.02/1.03  epr:                                    10
% 4.02/1.03  horn:                                   16
% 4.02/1.03  ground:                                 9
% 4.02/1.03  unary:                                  9
% 4.02/1.03  binary:                                 1
% 4.02/1.03  lits:                                   204
% 4.02/1.03  lits_eq:                                7
% 4.02/1.03  fd_pure:                                0
% 4.02/1.03  fd_pseudo:                              0
% 4.02/1.03  fd_cond:                                0
% 4.02/1.03  fd_pseudo_cond:                         1
% 4.02/1.03  ac_symbols:                             0
% 4.02/1.03  
% 4.02/1.03  ------ Propositional Solver
% 4.02/1.03  
% 4.02/1.03  prop_solver_calls:                      24
% 4.02/1.03  prop_fast_solver_calls:                 2539
% 4.02/1.03  smt_solver_calls:                       0
% 4.02/1.03  smt_fast_solver_calls:                  0
% 4.02/1.03  prop_num_of_clauses:                    3017
% 4.02/1.03  prop_preprocess_simplified:             8298
% 4.02/1.03  prop_fo_subsumed:                       217
% 4.02/1.03  prop_solver_time:                       0.
% 4.02/1.03  smt_solver_time:                        0.
% 4.02/1.03  smt_fast_solver_time:                   0.
% 4.02/1.03  prop_fast_solver_time:                  0.
% 4.02/1.03  prop_unsat_core_time:                   0.
% 4.02/1.03  
% 4.02/1.03  ------ QBF
% 4.02/1.03  
% 4.02/1.03  qbf_q_res:                              0
% 4.02/1.03  qbf_num_tautologies:                    0
% 4.02/1.03  qbf_prep_cycles:                        0
% 4.02/1.03  
% 4.02/1.03  ------ BMC1
% 4.02/1.03  
% 4.02/1.03  bmc1_current_bound:                     -1
% 4.02/1.03  bmc1_last_solved_bound:                 -1
% 4.02/1.03  bmc1_unsat_core_size:                   -1
% 4.02/1.03  bmc1_unsat_core_parents_size:           -1
% 4.02/1.03  bmc1_merge_next_fun:                    0
% 4.02/1.03  bmc1_unsat_core_clauses_time:           0.
% 4.02/1.03  
% 4.02/1.03  ------ Instantiation
% 4.02/1.03  
% 4.02/1.03  inst_num_of_clauses:                    791
% 4.02/1.03  inst_num_in_passive:                    26
% 4.02/1.03  inst_num_in_active:                     412
% 4.02/1.03  inst_num_in_unprocessed:                353
% 4.02/1.03  inst_num_of_loops:                      440
% 4.02/1.03  inst_num_of_learning_restarts:          0
% 4.02/1.03  inst_num_moves_active_passive:          27
% 4.02/1.03  inst_lit_activity:                      0
% 4.02/1.03  inst_lit_activity_moves:                0
% 4.02/1.03  inst_num_tautologies:                   0
% 4.02/1.03  inst_num_prop_implied:                  0
% 4.02/1.03  inst_num_existing_simplified:           0
% 4.02/1.03  inst_num_eq_res_simplified:             0
% 4.02/1.03  inst_num_child_elim:                    0
% 4.02/1.03  inst_num_of_dismatching_blockings:      469
% 4.02/1.03  inst_num_of_non_proper_insts:           599
% 4.02/1.03  inst_num_of_duplicates:                 0
% 4.02/1.03  inst_inst_num_from_inst_to_res:         0
% 4.02/1.03  inst_dismatching_checking_time:         0.
% 4.02/1.03  
% 4.02/1.03  ------ Resolution
% 4.02/1.03  
% 4.02/1.03  res_num_of_clauses:                     0
% 4.02/1.03  res_num_in_passive:                     0
% 4.02/1.03  res_num_in_active:                      0
% 4.02/1.03  res_num_of_loops:                       115
% 4.02/1.03  res_forward_subset_subsumed:            12
% 4.02/1.03  res_backward_subset_subsumed:           0
% 4.02/1.03  res_forward_subsumed:                   0
% 4.02/1.03  res_backward_subsumed:                  0
% 4.02/1.03  res_forward_subsumption_resolution:     1
% 4.02/1.03  res_backward_subsumption_resolution:    0
% 4.02/1.03  res_clause_to_clause_subsumption:       499
% 4.02/1.03  res_orphan_elimination:                 0
% 4.02/1.03  res_tautology_del:                      33
% 4.02/1.03  res_num_eq_res_simplified:              0
% 4.02/1.03  res_num_sel_changes:                    0
% 4.02/1.03  res_moves_from_active_to_pass:          0
% 4.02/1.03  
% 4.02/1.03  ------ Superposition
% 4.02/1.03  
% 4.02/1.03  sup_time_total:                         0.
% 4.02/1.03  sup_time_generating:                    0.
% 4.02/1.03  sup_time_sim_full:                      0.
% 4.02/1.03  sup_time_sim_immed:                     0.
% 4.02/1.03  
% 4.02/1.03  sup_num_of_clauses:                     101
% 4.02/1.03  sup_num_in_active:                      77
% 4.02/1.03  sup_num_in_passive:                     24
% 4.02/1.03  sup_num_of_loops:                       86
% 4.02/1.03  sup_fw_superposition:                   64
% 4.02/1.03  sup_bw_superposition:                   52
% 4.02/1.03  sup_immediate_simplified:               30
% 4.02/1.03  sup_given_eliminated:                   0
% 4.02/1.03  comparisons_done:                       0
% 4.02/1.03  comparisons_avoided:                    3
% 4.02/1.03  
% 4.02/1.03  ------ Simplifications
% 4.02/1.03  
% 4.02/1.03  
% 4.02/1.03  sim_fw_subset_subsumed:                 19
% 4.02/1.03  sim_bw_subset_subsumed:                 4
% 4.02/1.03  sim_fw_subsumed:                        0
% 4.02/1.03  sim_bw_subsumed:                        2
% 4.02/1.03  sim_fw_subsumption_res:                 0
% 4.02/1.03  sim_bw_subsumption_res:                 0
% 4.02/1.03  sim_tautology_del:                      7
% 4.02/1.03  sim_eq_tautology_del:                   4
% 4.02/1.03  sim_eq_res_simp:                        0
% 4.02/1.03  sim_fw_demodulated:                     3
% 4.02/1.03  sim_bw_demodulated:                     8
% 4.02/1.03  sim_light_normalised:                   14
% 4.02/1.03  sim_joinable_taut:                      0
% 4.02/1.03  sim_joinable_simp:                      0
% 4.02/1.03  sim_ac_normalised:                      0
% 4.02/1.03  sim_smt_subsumption:                    0
% 4.02/1.03  
%------------------------------------------------------------------------------
