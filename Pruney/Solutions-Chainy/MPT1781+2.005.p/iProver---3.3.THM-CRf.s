%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:44 EST 2020

% Result     : Theorem 7.33s
% Output     : CNFRefutation 7.33s
% Verified   : 
% Statistics : Number of formulae       :  277 (26231 expanded)
%              Number of clauses        :  190 (7168 expanded)
%              Number of leaves         :   22 (8049 expanded)
%              Depth                    :   40
%              Number of atoms          : 1887 (255848 expanded)
%              Number of equality atoms :  750 (31346 expanded)
%              Maximal formula depth    :   22 (   8 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f57,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f50,f56,f55,f54])).

fof(f85,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f82,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f83,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f86,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(flattening,[],[f32])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f64,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f37])).

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

fof(f51,plain,(
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

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f37])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f52,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
        & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f52])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
      | ~ r2_hidden(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f62])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f89,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f53])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1151,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | m1_subset_1(k4_tmap_1(X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
    | v2_struct_0(X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1730,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_subset_1(k4_tmap_1(X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1151])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1136,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1745,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1136])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1139,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1742,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

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
    inference(cnf_transformation,[],[f67])).

cnf(c_1155,plain,
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
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1726,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1155])).

cnf(c_4312,plain,
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
    inference(superposition,[status(thm)],[c_1742,c_1726])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_33,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_34,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_35,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4706,plain,
    ( l1_pre_topc(X1_51) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4312,c_33,c_34,c_35,c_38,c_39])).

cnf(c_4707,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(X0_51,sK2) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_4706])).

cnf(c_4712,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_4707])).

cnf(c_16,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1148,plain,
    ( m1_pre_topc(X0_51,X0_51)
    | ~ l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1733,plain,
    ( m1_pre_topc(X0_51,X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1148])).

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
    inference(cnf_transformation,[],[f66])).

cnf(c_1156,plain,
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
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1725,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1156])).

cnf(c_3553,plain,
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
    inference(superposition,[status(thm)],[c_1742,c_1725])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_36,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_37,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1158,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | l1_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1916,plain,
    ( ~ m1_pre_topc(sK2,X0_51)
    | ~ l1_pre_topc(X0_51)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1158])).

cnf(c_1917,plain,
    ( m1_pre_topc(sK2,X0_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1916])).

cnf(c_1919,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1917])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1159,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | v2_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2157,plain,
    ( ~ m1_pre_topc(sK2,X0_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v2_pre_topc(X0_51)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1159])).

cnf(c_2158,plain,
    ( m1_pre_topc(sK2,X0_51) != iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2157])).

cnf(c_2160,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2158])).

cnf(c_3797,plain,
    ( m1_pre_topc(X0_51,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3553,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_1919,c_2160])).

cnf(c_3798,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51)
    | m1_pre_topc(X0_51,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3797])).

cnf(c_3803,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1733,c_3798])).

cnf(c_1918,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1916])).

cnf(c_2159,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2157])).

cnf(c_2541,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_1799,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(sK1))
    | ~ m1_pre_topc(X1_51,X0_51)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
    | v2_struct_0(X0_51)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_51)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0_51)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(X0_52)
    | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),X0_52,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,X0_52,X1_51) ),
    inference(instantiation,[status(thm)],[c_1156])).

cnf(c_2600,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_51,sK2)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0_52)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,X0_52,X0_51) ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_3580,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(X0_52)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,X0_52,sK2) ),
    inference(instantiation,[status(thm)],[c_2600])).

cnf(c_3582,plain,
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
    inference(instantiation,[status(thm)],[c_3580])).

cnf(c_3875,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3803,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25,c_1918,c_2159,c_2541,c_3582])).

cnf(c_4714,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2)
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4712,c_3875])).

cnf(c_2542,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2541])).

cnf(c_4736,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4714,c_33,c_34,c_35,c_37,c_1919,c_2542])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f70])).

cnf(c_1154,plain,
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
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1727,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1154])).

cnf(c_4739,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4736,c_1727])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5189,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4739,c_33,c_34,c_35,c_37,c_38,c_39,c_40])).

cnf(c_4,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1160,plain,
    ( ~ r2_funct_2(X0_53,X1_53,X0_52,X1_52)
    | ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ v1_funct_2(X1_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52)
    | X1_52 = X0_52 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1721,plain,
    ( X0_52 = X1_52
    | r2_funct_2(X0_53,X1_53,X1_52,X0_52) != iProver_top
    | v1_funct_2(X1_52,X0_53,X1_53) != iProver_top
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1160])).

cnf(c_3099,plain,
    ( sK3 = X0_52
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,sK3) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_1721])).

cnf(c_3437,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | sK3 = X0_52
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,sK3) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3099,c_38,c_39])).

cnf(c_3438,plain,
    ( sK3 = X0_52
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,sK3) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_3437])).

cnf(c_5200,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),sK3) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5189,c_3438])).

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
    inference(cnf_transformation,[],[f78])).

cnf(c_1144,plain,
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

cnf(c_1737,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1144])).

cnf(c_4738,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4736,c_1737])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f69])).

cnf(c_1153,plain,
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
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1728,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1153])).

cnf(c_4740,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4736,c_1728])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f68])).

cnf(c_1152,plain,
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
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1729,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1152])).

cnf(c_3562,plain,
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
    inference(superposition,[status(thm)],[c_1742,c_1729])).

cnf(c_1801,plain,
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
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_1936,plain,
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
    inference(instantiation,[status(thm)],[c_1801])).

cnf(c_1937,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1936])).

cnf(c_3868,plain,
    ( v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_pre_topc(X1_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3562,c_33,c_34,c_35,c_38,c_39,c_40,c_1937])).

cnf(c_3869,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_pre_topc(sK2,X1_51) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | v2_pre_topc(X1_51) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3868])).

cnf(c_4741,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4736,c_3869])).

cnf(c_5196,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = X0_52
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5189,c_1721])).

cnf(c_5211,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5196])).

cnf(c_5263,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5200,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_4738,c_4740,c_4741,c_5211])).

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
    inference(cnf_transformation,[],[f76])).

cnf(c_1146,plain,
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

cnf(c_1735,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1146])).

cnf(c_5272,plain,
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
    inference(superposition,[status(thm)],[c_5263,c_1735])).

cnf(c_6157,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5272,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_1919,c_2160,c_2542])).

cnf(c_6158,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_6157])).

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
    inference(cnf_transformation,[],[f75])).

cnf(c_1145,plain,
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

cnf(c_1736,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1145])).

cnf(c_5271,plain,
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
    inference(superposition,[status(thm)],[c_5263,c_1736])).

cnf(c_5611,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5271,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_1919,c_2160,c_2542])).

cnf(c_5612,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_5611])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1157,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
    | m1_subset_1(X0_52,u1_struct_0(X1_51))
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X1_51) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1724,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X1_51)) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | l1_pre_topc(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1157])).

cnf(c_5617,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_5612,c_1724])).

cnf(c_6473,plain,
    ( v2_struct_0(X0_51) = iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5617,c_36])).

cnf(c_6474,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0_51) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_6473])).

cnf(c_6480,plain,
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
    inference(superposition,[status(thm)],[c_6474,c_1724])).

cnf(c_1198,plain,
    ( m1_pre_topc(X0_51,X1_51) != iProver_top
    | l1_pre_topc(X1_51) != iProver_top
    | l1_pre_topc(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1158])).

cnf(c_7654,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_6480,c_1198])).

cnf(c_7655,plain,
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
    inference(renaming,[status(thm)],[c_7654])).

cnf(c_7658,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_7655])).

cnf(c_7662,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7658,c_33,c_35,c_36,c_37,c_1919,c_2542])).

cnf(c_7663,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_7662])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1142,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | ~ m1_subset_1(X0_52,u1_struct_0(X1_51))
    | ~ r2_hidden(X0_52,u1_struct_0(X0_51))
    | v2_struct_0(X1_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | k1_funct_1(k4_tmap_1(X1_51,X0_51),X0_52) = X0_52 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1739,plain,
    ( k1_funct_1(k4_tmap_1(X0_51,X1_51),X0_52) = X0_52
    | m1_pre_topc(X1_51,X0_51) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
    | r2_hidden(X0_52,u1_struct_0(X1_51)) != iProver_top
    | v2_struct_0(X1_51) = iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | l1_pre_topc(X0_51) != iProver_top
    | v2_pre_topc(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1142])).

cnf(c_7668,plain,
    ( k1_funct_1(k4_tmap_1(sK1,X0_51),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_7663,c_1739])).

cnf(c_7814,plain,
    ( v2_struct_0(X0_51) = iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(X0_51,sK1) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | k1_funct_1(k4_tmap_1(sK1,X0_51),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7668,c_33,c_34,c_35])).

cnf(c_7815,plain,
    ( k1_funct_1(k4_tmap_1(sK1,X0_51),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_51,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) != iProver_top
    | v2_struct_0(X0_51) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_7814])).

cnf(c_7818,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_6158,c_7815])).

cnf(c_7870,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7818,c_36,c_37])).

cnf(c_7871,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_7870])).

cnf(c_7875,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_7871])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1162,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X1_52,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | v1_xboole_0(X0_53)
    | k3_funct_2(X0_53,X1_53,X0_52,X1_52) = k1_funct_1(X0_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1719,plain,
    ( k3_funct_2(X0_53,X1_53,X0_52,X1_52) = k1_funct_1(X0_52,X1_52)
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X1_52,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1162])).

cnf(c_2762,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_1719])).

cnf(c_3092,plain,
    ( m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2762,c_38,c_39])).

cnf(c_3093,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3092])).

cnf(c_5619,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5612,c_3093])).

cnf(c_5772,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_5619])).

cnf(c_23,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_44,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1166,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_1183,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_1174,plain,
    ( ~ r2_funct_2(X0_53,X1_53,X0_52,X1_52)
    | r2_funct_2(X0_53,X1_53,X2_52,X3_52)
    | X2_52 != X0_52
    | X3_52 != X1_52 ),
    theory(equality)).

cnf(c_1903,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,X1_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
    | k4_tmap_1(sK1,sK2) != X0_52
    | sK3 != X1_52 ),
    inference(instantiation,[status(thm)],[c_1174])).

cnf(c_1904,plain,
    ( k4_tmap_1(sK1,sK2) != X0_52
    | sK3 != X1_52
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,X1_52) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1903])).

cnf(c_1906,plain,
    ( k4_tmap_1(sK1,sK2) != sK3
    | sK3 != sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1904])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1149,plain,
    ( ~ m1_pre_topc(X0_51,X1_51)
    | v2_struct_0(X1_51)
    | ~ l1_pre_topc(X1_51)
    | ~ v2_pre_topc(X1_51)
    | v1_funct_1(k4_tmap_1(X1_51,X0_51)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2204,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_2205,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2204])).

cnf(c_3,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1161,plain,
    ( r2_funct_2(X0_53,X1_53,X0_52,X0_52)
    | ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1720,plain,
    ( r2_funct_2(X0_53,X1_53,X0_52,X0_52) = iProver_top
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1161])).

cnf(c_2727,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_1720])).

cnf(c_2037,plain,
    ( ~ r2_funct_2(X0_53,X1_53,X0_52,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ v1_funct_2(k4_tmap_1(sK1,sK2),X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | k4_tmap_1(sK1,sK2) = X0_52 ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_3261,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,k4_tmap_1(sK1,sK2))
    | ~ v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | k4_tmap_1(sK1,sK2) = X0_52 ),
    inference(instantiation,[status(thm)],[c_2037])).

cnf(c_3263,plain,
    ( k4_tmap_1(sK1,sK2) = X0_52
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3261])).

cnf(c_3265,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3263])).

cnf(c_14,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1150,plain,
    ( v1_funct_2(k4_tmap_1(X0_51,X1_51),u1_struct_0(X1_51),u1_struct_0(X0_51))
    | ~ m1_pre_topc(X1_51,X0_51)
    | v2_struct_0(X0_51)
    | ~ l1_pre_topc(X0_51)
    | ~ v2_pre_topc(X0_51) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3479,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_3480,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3479])).

cnf(c_5302,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1151])).

cnf(c_5303,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5302])).

cnf(c_5779,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5772,c_33,c_34,c_35,c_37,c_38,c_39,c_40,c_44,c_1183,c_1906,c_2205,c_2727,c_3265,c_3480,c_5303])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1164,plain,
    ( ~ r2_hidden(X0_52,X0_53)
    | ~ v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1717,plain,
    ( r2_hidden(X0_52,X0_53) != iProver_top
    | v1_xboole_0(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1164])).

cnf(c_6161,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6158,c_1717])).

cnf(c_6191,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_6161])).

cnf(c_6467,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6191,c_33,c_34,c_35,c_37,c_38,c_39,c_40,c_44,c_1183,c_1906,c_2205,c_2727,c_3265,c_3480,c_5303])).

cnf(c_6471,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_5779,c_6467])).

cnf(c_24,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,u1_struct_0(sK2))
    | k1_funct_1(sK3,X0) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1140,negated_conjecture,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK1))
    | ~ r2_hidden(X0_52,u1_struct_0(sK2))
    | k1_funct_1(sK3,X0_52) = X0_52 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1741,plain,
    ( k1_funct_1(sK3,X0_52) = X0_52
    | m1_subset_1(X0_52,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_52,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1140])).

cnf(c_6477,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_6474,c_1741])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1163,plain,
    ( ~ m1_subset_1(X0_52,X0_53)
    | r2_hidden(X0_52,X0_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1718,plain,
    ( m1_subset_1(X0_52,X0_53) != iProver_top
    | r2_hidden(X0_52,X0_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1163])).

cnf(c_5618,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5612,c_1718])).

cnf(c_6700,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6477,c_33,c_34,c_35,c_37,c_38,c_39,c_40,c_44,c_1183,c_1906,c_2205,c_2727,c_3265,c_3480,c_5303,c_5618,c_6191])).

cnf(c_6701,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_6700])).

cnf(c_6705,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_6701])).

cnf(c_6712,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6705,c_33,c_34,c_35,c_37,c_38,c_39,c_40,c_44,c_1183,c_1906,c_2205,c_2727,c_3265,c_3480,c_5303])).

cnf(c_7078,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_6471,c_6471,c_6712])).

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
    inference(cnf_transformation,[],[f77])).

cnf(c_1147,plain,
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

cnf(c_1734,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1147])).

cnf(c_7079,plain,
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
    inference(superposition,[status(thm)],[c_7078,c_1734])).

cnf(c_7080,plain,
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
    inference(light_normalisation,[status(thm)],[c_7079,c_5263])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7875,c_7080,c_5303,c_3480,c_3265,c_2727,c_2542,c_2205,c_2160,c_1919,c_1906,c_1183,c_44,c_40,c_39,c_38,c_37,c_36,c_35,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n016.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 12:52:34 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 7.33/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.33/1.48  
% 7.33/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.33/1.48  
% 7.33/1.48  ------  iProver source info
% 7.33/1.48  
% 7.33/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.33/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.33/1.48  git: non_committed_changes: false
% 7.33/1.48  git: last_make_outside_of_git: false
% 7.33/1.48  
% 7.33/1.48  ------ 
% 7.33/1.48  
% 7.33/1.48  ------ Input Options
% 7.33/1.48  
% 7.33/1.48  --out_options                           all
% 7.33/1.48  --tptp_safe_out                         true
% 7.33/1.48  --problem_path                          ""
% 7.33/1.48  --include_path                          ""
% 7.33/1.48  --clausifier                            res/vclausify_rel
% 7.33/1.48  --clausifier_options                    ""
% 7.33/1.48  --stdin                                 false
% 7.33/1.48  --stats_out                             all
% 7.33/1.48  
% 7.33/1.48  ------ General Options
% 7.33/1.48  
% 7.33/1.48  --fof                                   false
% 7.33/1.48  --time_out_real                         305.
% 7.33/1.48  --time_out_virtual                      -1.
% 7.33/1.48  --symbol_type_check                     false
% 7.33/1.48  --clausify_out                          false
% 7.33/1.48  --sig_cnt_out                           false
% 7.33/1.48  --trig_cnt_out                          false
% 7.33/1.48  --trig_cnt_out_tolerance                1.
% 7.33/1.48  --trig_cnt_out_sk_spl                   false
% 7.33/1.48  --abstr_cl_out                          false
% 7.33/1.48  
% 7.33/1.48  ------ Global Options
% 7.33/1.48  
% 7.33/1.48  --schedule                              default
% 7.33/1.48  --add_important_lit                     false
% 7.33/1.48  --prop_solver_per_cl                    1000
% 7.33/1.48  --min_unsat_core                        false
% 7.33/1.48  --soft_assumptions                      false
% 7.33/1.48  --soft_lemma_size                       3
% 7.33/1.48  --prop_impl_unit_size                   0
% 7.33/1.48  --prop_impl_unit                        []
% 7.33/1.48  --share_sel_clauses                     true
% 7.33/1.48  --reset_solvers                         false
% 7.33/1.48  --bc_imp_inh                            [conj_cone]
% 7.33/1.48  --conj_cone_tolerance                   3.
% 7.33/1.48  --extra_neg_conj                        none
% 7.33/1.48  --large_theory_mode                     true
% 7.33/1.48  --prolific_symb_bound                   200
% 7.33/1.48  --lt_threshold                          2000
% 7.33/1.48  --clause_weak_htbl                      true
% 7.33/1.48  --gc_record_bc_elim                     false
% 7.33/1.48  
% 7.33/1.48  ------ Preprocessing Options
% 7.33/1.48  
% 7.33/1.48  --preprocessing_flag                    true
% 7.33/1.48  --time_out_prep_mult                    0.1
% 7.33/1.48  --splitting_mode                        input
% 7.33/1.48  --splitting_grd                         true
% 7.33/1.48  --splitting_cvd                         false
% 7.33/1.48  --splitting_cvd_svl                     false
% 7.33/1.48  --splitting_nvd                         32
% 7.33/1.48  --sub_typing                            true
% 7.33/1.48  --prep_gs_sim                           true
% 7.33/1.48  --prep_unflatten                        true
% 7.33/1.48  --prep_res_sim                          true
% 7.33/1.48  --prep_upred                            true
% 7.33/1.48  --prep_sem_filter                       exhaustive
% 7.33/1.48  --prep_sem_filter_out                   false
% 7.33/1.48  --pred_elim                             true
% 7.33/1.48  --res_sim_input                         true
% 7.33/1.48  --eq_ax_congr_red                       true
% 7.33/1.48  --pure_diseq_elim                       true
% 7.33/1.48  --brand_transform                       false
% 7.33/1.48  --non_eq_to_eq                          false
% 7.33/1.48  --prep_def_merge                        true
% 7.33/1.48  --prep_def_merge_prop_impl              false
% 7.33/1.48  --prep_def_merge_mbd                    true
% 7.33/1.48  --prep_def_merge_tr_red                 false
% 7.33/1.48  --prep_def_merge_tr_cl                  false
% 7.33/1.48  --smt_preprocessing                     true
% 7.33/1.48  --smt_ac_axioms                         fast
% 7.33/1.48  --preprocessed_out                      false
% 7.33/1.48  --preprocessed_stats                    false
% 7.33/1.48  
% 7.33/1.48  ------ Abstraction refinement Options
% 7.33/1.48  
% 7.33/1.48  --abstr_ref                             []
% 7.33/1.48  --abstr_ref_prep                        false
% 7.33/1.48  --abstr_ref_until_sat                   false
% 7.33/1.48  --abstr_ref_sig_restrict                funpre
% 7.33/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.33/1.48  --abstr_ref_under                       []
% 7.33/1.48  
% 7.33/1.48  ------ SAT Options
% 7.33/1.48  
% 7.33/1.48  --sat_mode                              false
% 7.33/1.48  --sat_fm_restart_options                ""
% 7.33/1.48  --sat_gr_def                            false
% 7.33/1.48  --sat_epr_types                         true
% 7.33/1.48  --sat_non_cyclic_types                  false
% 7.33/1.48  --sat_finite_models                     false
% 7.33/1.48  --sat_fm_lemmas                         false
% 7.33/1.48  --sat_fm_prep                           false
% 7.33/1.48  --sat_fm_uc_incr                        true
% 7.33/1.48  --sat_out_model                         small
% 7.33/1.48  --sat_out_clauses                       false
% 7.33/1.48  
% 7.33/1.48  ------ QBF Options
% 7.33/1.48  
% 7.33/1.48  --qbf_mode                              false
% 7.33/1.48  --qbf_elim_univ                         false
% 7.33/1.48  --qbf_dom_inst                          none
% 7.33/1.48  --qbf_dom_pre_inst                      false
% 7.33/1.48  --qbf_sk_in                             false
% 7.33/1.48  --qbf_pred_elim                         true
% 7.33/1.48  --qbf_split                             512
% 7.33/1.48  
% 7.33/1.48  ------ BMC1 Options
% 7.33/1.48  
% 7.33/1.48  --bmc1_incremental                      false
% 7.33/1.48  --bmc1_axioms                           reachable_all
% 7.33/1.48  --bmc1_min_bound                        0
% 7.33/1.48  --bmc1_max_bound                        -1
% 7.33/1.48  --bmc1_max_bound_default                -1
% 7.33/1.48  --bmc1_symbol_reachability              true
% 7.33/1.48  --bmc1_property_lemmas                  false
% 7.33/1.48  --bmc1_k_induction                      false
% 7.33/1.48  --bmc1_non_equiv_states                 false
% 7.33/1.48  --bmc1_deadlock                         false
% 7.33/1.48  --bmc1_ucm                              false
% 7.33/1.48  --bmc1_add_unsat_core                   none
% 7.33/1.48  --bmc1_unsat_core_children              false
% 7.33/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.33/1.48  --bmc1_out_stat                         full
% 7.33/1.48  --bmc1_ground_init                      false
% 7.33/1.48  --bmc1_pre_inst_next_state              false
% 7.33/1.48  --bmc1_pre_inst_state                   false
% 7.33/1.48  --bmc1_pre_inst_reach_state             false
% 7.33/1.48  --bmc1_out_unsat_core                   false
% 7.33/1.48  --bmc1_aig_witness_out                  false
% 7.33/1.48  --bmc1_verbose                          false
% 7.33/1.48  --bmc1_dump_clauses_tptp                false
% 7.33/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.33/1.48  --bmc1_dump_file                        -
% 7.33/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.33/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.33/1.48  --bmc1_ucm_extend_mode                  1
% 7.33/1.48  --bmc1_ucm_init_mode                    2
% 7.33/1.48  --bmc1_ucm_cone_mode                    none
% 7.33/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.33/1.48  --bmc1_ucm_relax_model                  4
% 7.33/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.33/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.33/1.48  --bmc1_ucm_layered_model                none
% 7.33/1.48  --bmc1_ucm_max_lemma_size               10
% 7.33/1.48  
% 7.33/1.48  ------ AIG Options
% 7.33/1.48  
% 7.33/1.48  --aig_mode                              false
% 7.33/1.48  
% 7.33/1.48  ------ Instantiation Options
% 7.33/1.48  
% 7.33/1.48  --instantiation_flag                    true
% 7.33/1.48  --inst_sos_flag                         true
% 7.33/1.48  --inst_sos_phase                        true
% 7.33/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.33/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.33/1.48  --inst_lit_sel_side                     num_symb
% 7.33/1.48  --inst_solver_per_active                1400
% 7.33/1.48  --inst_solver_calls_frac                1.
% 7.33/1.48  --inst_passive_queue_type               priority_queues
% 7.33/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.33/1.48  --inst_passive_queues_freq              [25;2]
% 7.33/1.48  --inst_dismatching                      true
% 7.33/1.48  --inst_eager_unprocessed_to_passive     true
% 7.33/1.48  --inst_prop_sim_given                   true
% 7.33/1.48  --inst_prop_sim_new                     false
% 7.33/1.48  --inst_subs_new                         false
% 7.33/1.48  --inst_eq_res_simp                      false
% 7.33/1.48  --inst_subs_given                       false
% 7.33/1.48  --inst_orphan_elimination               true
% 7.33/1.48  --inst_learning_loop_flag               true
% 7.33/1.48  --inst_learning_start                   3000
% 7.33/1.48  --inst_learning_factor                  2
% 7.33/1.48  --inst_start_prop_sim_after_learn       3
% 7.33/1.48  --inst_sel_renew                        solver
% 7.33/1.48  --inst_lit_activity_flag                true
% 7.33/1.48  --inst_restr_to_given                   false
% 7.33/1.48  --inst_activity_threshold               500
% 7.33/1.48  --inst_out_proof                        true
% 7.33/1.48  
% 7.33/1.48  ------ Resolution Options
% 7.33/1.48  
% 7.33/1.48  --resolution_flag                       true
% 7.33/1.48  --res_lit_sel                           adaptive
% 7.33/1.48  --res_lit_sel_side                      none
% 7.33/1.48  --res_ordering                          kbo
% 7.33/1.48  --res_to_prop_solver                    active
% 7.33/1.48  --res_prop_simpl_new                    false
% 7.33/1.48  --res_prop_simpl_given                  true
% 7.33/1.48  --res_passive_queue_type                priority_queues
% 7.33/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.33/1.48  --res_passive_queues_freq               [15;5]
% 7.33/1.48  --res_forward_subs                      full
% 7.33/1.48  --res_backward_subs                     full
% 7.33/1.48  --res_forward_subs_resolution           true
% 7.33/1.48  --res_backward_subs_resolution          true
% 7.33/1.48  --res_orphan_elimination                true
% 7.33/1.48  --res_time_limit                        2.
% 7.33/1.48  --res_out_proof                         true
% 7.33/1.48  
% 7.33/1.48  ------ Superposition Options
% 7.33/1.48  
% 7.33/1.48  --superposition_flag                    true
% 7.33/1.48  --sup_passive_queue_type                priority_queues
% 7.33/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.33/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.33/1.48  --demod_completeness_check              fast
% 7.33/1.48  --demod_use_ground                      true
% 7.33/1.48  --sup_to_prop_solver                    passive
% 7.33/1.48  --sup_prop_simpl_new                    true
% 7.33/1.48  --sup_prop_simpl_given                  true
% 7.33/1.48  --sup_fun_splitting                     true
% 7.33/1.48  --sup_smt_interval                      50000
% 7.33/1.48  
% 7.33/1.48  ------ Superposition Simplification Setup
% 7.33/1.48  
% 7.33/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.33/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.33/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.33/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.33/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.33/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.33/1.48  --sup_immed_triv                        [TrivRules]
% 7.33/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.48  --sup_immed_bw_main                     []
% 7.33/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.33/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.33/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.48  --sup_input_bw                          []
% 7.33/1.48  
% 7.33/1.48  ------ Combination Options
% 7.33/1.48  
% 7.33/1.48  --comb_res_mult                         3
% 7.33/1.48  --comb_sup_mult                         2
% 7.33/1.48  --comb_inst_mult                        10
% 7.33/1.48  
% 7.33/1.48  ------ Debug Options
% 7.33/1.48  
% 7.33/1.48  --dbg_backtrace                         false
% 7.33/1.48  --dbg_dump_prop_clauses                 false
% 7.33/1.48  --dbg_dump_prop_clauses_file            -
% 7.33/1.48  --dbg_out_stat                          false
% 7.33/1.48  ------ Parsing...
% 7.33/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.33/1.48  
% 7.33/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.33/1.48  
% 7.33/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.33/1.48  
% 7.33/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.33/1.48  ------ Proving...
% 7.33/1.48  ------ Problem Properties 
% 7.33/1.48  
% 7.33/1.48  
% 7.33/1.48  clauses                                 33
% 7.33/1.48  conjectures                             10
% 7.33/1.48  EPR                                     12
% 7.33/1.48  Horn                                    17
% 7.33/1.48  unary                                   9
% 7.33/1.48  binary                                  2
% 7.33/1.48  lits                                    198
% 7.33/1.48  lits eq                                 7
% 7.33/1.48  fd_pure                                 0
% 7.33/1.48  fd_pseudo                               0
% 7.33/1.48  fd_cond                                 0
% 7.33/1.48  fd_pseudo_cond                          1
% 7.33/1.48  AC symbols                              0
% 7.33/1.48  
% 7.33/1.48  ------ Schedule dynamic 5 is on 
% 7.33/1.48  
% 7.33/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.33/1.48  
% 7.33/1.48  
% 7.33/1.48  ------ 
% 7.33/1.48  Current options:
% 7.33/1.48  ------ 
% 7.33/1.48  
% 7.33/1.48  ------ Input Options
% 7.33/1.48  
% 7.33/1.48  --out_options                           all
% 7.33/1.48  --tptp_safe_out                         true
% 7.33/1.48  --problem_path                          ""
% 7.33/1.48  --include_path                          ""
% 7.33/1.48  --clausifier                            res/vclausify_rel
% 7.33/1.48  --clausifier_options                    ""
% 7.33/1.48  --stdin                                 false
% 7.33/1.48  --stats_out                             all
% 7.33/1.48  
% 7.33/1.48  ------ General Options
% 7.33/1.48  
% 7.33/1.48  --fof                                   false
% 7.33/1.48  --time_out_real                         305.
% 7.33/1.48  --time_out_virtual                      -1.
% 7.33/1.48  --symbol_type_check                     false
% 7.33/1.48  --clausify_out                          false
% 7.33/1.48  --sig_cnt_out                           false
% 7.33/1.48  --trig_cnt_out                          false
% 7.33/1.48  --trig_cnt_out_tolerance                1.
% 7.33/1.48  --trig_cnt_out_sk_spl                   false
% 7.33/1.48  --abstr_cl_out                          false
% 7.33/1.48  
% 7.33/1.48  ------ Global Options
% 7.33/1.48  
% 7.33/1.48  --schedule                              default
% 7.33/1.48  --add_important_lit                     false
% 7.33/1.48  --prop_solver_per_cl                    1000
% 7.33/1.48  --min_unsat_core                        false
% 7.33/1.48  --soft_assumptions                      false
% 7.33/1.48  --soft_lemma_size                       3
% 7.33/1.48  --prop_impl_unit_size                   0
% 7.33/1.48  --prop_impl_unit                        []
% 7.33/1.48  --share_sel_clauses                     true
% 7.33/1.48  --reset_solvers                         false
% 7.33/1.48  --bc_imp_inh                            [conj_cone]
% 7.33/1.48  --conj_cone_tolerance                   3.
% 7.33/1.48  --extra_neg_conj                        none
% 7.33/1.48  --large_theory_mode                     true
% 7.33/1.48  --prolific_symb_bound                   200
% 7.33/1.48  --lt_threshold                          2000
% 7.33/1.48  --clause_weak_htbl                      true
% 7.33/1.48  --gc_record_bc_elim                     false
% 7.33/1.48  
% 7.33/1.48  ------ Preprocessing Options
% 7.33/1.48  
% 7.33/1.48  --preprocessing_flag                    true
% 7.33/1.48  --time_out_prep_mult                    0.1
% 7.33/1.48  --splitting_mode                        input
% 7.33/1.48  --splitting_grd                         true
% 7.33/1.48  --splitting_cvd                         false
% 7.33/1.48  --splitting_cvd_svl                     false
% 7.33/1.48  --splitting_nvd                         32
% 7.33/1.48  --sub_typing                            true
% 7.33/1.48  --prep_gs_sim                           true
% 7.33/1.48  --prep_unflatten                        true
% 7.33/1.48  --prep_res_sim                          true
% 7.33/1.48  --prep_upred                            true
% 7.33/1.48  --prep_sem_filter                       exhaustive
% 7.33/1.48  --prep_sem_filter_out                   false
% 7.33/1.48  --pred_elim                             true
% 7.33/1.48  --res_sim_input                         true
% 7.33/1.48  --eq_ax_congr_red                       true
% 7.33/1.48  --pure_diseq_elim                       true
% 7.33/1.48  --brand_transform                       false
% 7.33/1.48  --non_eq_to_eq                          false
% 7.33/1.48  --prep_def_merge                        true
% 7.33/1.48  --prep_def_merge_prop_impl              false
% 7.33/1.48  --prep_def_merge_mbd                    true
% 7.33/1.48  --prep_def_merge_tr_red                 false
% 7.33/1.48  --prep_def_merge_tr_cl                  false
% 7.33/1.48  --smt_preprocessing                     true
% 7.33/1.48  --smt_ac_axioms                         fast
% 7.33/1.48  --preprocessed_out                      false
% 7.33/1.48  --preprocessed_stats                    false
% 7.33/1.48  
% 7.33/1.48  ------ Abstraction refinement Options
% 7.33/1.48  
% 7.33/1.48  --abstr_ref                             []
% 7.33/1.48  --abstr_ref_prep                        false
% 7.33/1.48  --abstr_ref_until_sat                   false
% 7.33/1.48  --abstr_ref_sig_restrict                funpre
% 7.33/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.33/1.48  --abstr_ref_under                       []
% 7.33/1.48  
% 7.33/1.48  ------ SAT Options
% 7.33/1.48  
% 7.33/1.48  --sat_mode                              false
% 7.33/1.48  --sat_fm_restart_options                ""
% 7.33/1.48  --sat_gr_def                            false
% 7.33/1.48  --sat_epr_types                         true
% 7.33/1.48  --sat_non_cyclic_types                  false
% 7.33/1.48  --sat_finite_models                     false
% 7.33/1.48  --sat_fm_lemmas                         false
% 7.33/1.48  --sat_fm_prep                           false
% 7.33/1.48  --sat_fm_uc_incr                        true
% 7.33/1.48  --sat_out_model                         small
% 7.33/1.48  --sat_out_clauses                       false
% 7.33/1.48  
% 7.33/1.48  ------ QBF Options
% 7.33/1.48  
% 7.33/1.48  --qbf_mode                              false
% 7.33/1.48  --qbf_elim_univ                         false
% 7.33/1.48  --qbf_dom_inst                          none
% 7.33/1.48  --qbf_dom_pre_inst                      false
% 7.33/1.48  --qbf_sk_in                             false
% 7.33/1.48  --qbf_pred_elim                         true
% 7.33/1.48  --qbf_split                             512
% 7.33/1.48  
% 7.33/1.48  ------ BMC1 Options
% 7.33/1.48  
% 7.33/1.48  --bmc1_incremental                      false
% 7.33/1.48  --bmc1_axioms                           reachable_all
% 7.33/1.48  --bmc1_min_bound                        0
% 7.33/1.48  --bmc1_max_bound                        -1
% 7.33/1.48  --bmc1_max_bound_default                -1
% 7.33/1.48  --bmc1_symbol_reachability              true
% 7.33/1.48  --bmc1_property_lemmas                  false
% 7.33/1.48  --bmc1_k_induction                      false
% 7.33/1.48  --bmc1_non_equiv_states                 false
% 7.33/1.48  --bmc1_deadlock                         false
% 7.33/1.48  --bmc1_ucm                              false
% 7.33/1.48  --bmc1_add_unsat_core                   none
% 7.33/1.48  --bmc1_unsat_core_children              false
% 7.33/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.33/1.48  --bmc1_out_stat                         full
% 7.33/1.48  --bmc1_ground_init                      false
% 7.33/1.48  --bmc1_pre_inst_next_state              false
% 7.33/1.48  --bmc1_pre_inst_state                   false
% 7.33/1.48  --bmc1_pre_inst_reach_state             false
% 7.33/1.48  --bmc1_out_unsat_core                   false
% 7.33/1.48  --bmc1_aig_witness_out                  false
% 7.33/1.48  --bmc1_verbose                          false
% 7.33/1.48  --bmc1_dump_clauses_tptp                false
% 7.33/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.33/1.48  --bmc1_dump_file                        -
% 7.33/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.33/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.33/1.48  --bmc1_ucm_extend_mode                  1
% 7.33/1.48  --bmc1_ucm_init_mode                    2
% 7.33/1.48  --bmc1_ucm_cone_mode                    none
% 7.33/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.33/1.48  --bmc1_ucm_relax_model                  4
% 7.33/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.33/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.33/1.48  --bmc1_ucm_layered_model                none
% 7.33/1.48  --bmc1_ucm_max_lemma_size               10
% 7.33/1.48  
% 7.33/1.48  ------ AIG Options
% 7.33/1.48  
% 7.33/1.48  --aig_mode                              false
% 7.33/1.48  
% 7.33/1.48  ------ Instantiation Options
% 7.33/1.48  
% 7.33/1.48  --instantiation_flag                    true
% 7.33/1.48  --inst_sos_flag                         true
% 7.33/1.48  --inst_sos_phase                        true
% 7.33/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.33/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.33/1.48  --inst_lit_sel_side                     none
% 7.33/1.48  --inst_solver_per_active                1400
% 7.33/1.48  --inst_solver_calls_frac                1.
% 7.33/1.48  --inst_passive_queue_type               priority_queues
% 7.33/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.33/1.48  --inst_passive_queues_freq              [25;2]
% 7.33/1.48  --inst_dismatching                      true
% 7.33/1.48  --inst_eager_unprocessed_to_passive     true
% 7.33/1.48  --inst_prop_sim_given                   true
% 7.33/1.48  --inst_prop_sim_new                     false
% 7.33/1.48  --inst_subs_new                         false
% 7.33/1.48  --inst_eq_res_simp                      false
% 7.33/1.48  --inst_subs_given                       false
% 7.33/1.48  --inst_orphan_elimination               true
% 7.33/1.48  --inst_learning_loop_flag               true
% 7.33/1.48  --inst_learning_start                   3000
% 7.33/1.48  --inst_learning_factor                  2
% 7.33/1.48  --inst_start_prop_sim_after_learn       3
% 7.33/1.48  --inst_sel_renew                        solver
% 7.33/1.48  --inst_lit_activity_flag                true
% 7.33/1.48  --inst_restr_to_given                   false
% 7.33/1.48  --inst_activity_threshold               500
% 7.33/1.48  --inst_out_proof                        true
% 7.33/1.48  
% 7.33/1.48  ------ Resolution Options
% 7.33/1.48  
% 7.33/1.48  --resolution_flag                       false
% 7.33/1.48  --res_lit_sel                           adaptive
% 7.33/1.48  --res_lit_sel_side                      none
% 7.33/1.48  --res_ordering                          kbo
% 7.33/1.48  --res_to_prop_solver                    active
% 7.33/1.48  --res_prop_simpl_new                    false
% 7.33/1.48  --res_prop_simpl_given                  true
% 7.33/1.48  --res_passive_queue_type                priority_queues
% 7.33/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.33/1.48  --res_passive_queues_freq               [15;5]
% 7.33/1.48  --res_forward_subs                      full
% 7.33/1.48  --res_backward_subs                     full
% 7.33/1.48  --res_forward_subs_resolution           true
% 7.33/1.48  --res_backward_subs_resolution          true
% 7.33/1.48  --res_orphan_elimination                true
% 7.33/1.48  --res_time_limit                        2.
% 7.33/1.48  --res_out_proof                         true
% 7.33/1.48  
% 7.33/1.48  ------ Superposition Options
% 7.33/1.48  
% 7.33/1.48  --superposition_flag                    true
% 7.33/1.48  --sup_passive_queue_type                priority_queues
% 7.33/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.33/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.33/1.48  --demod_completeness_check              fast
% 7.33/1.48  --demod_use_ground                      true
% 7.33/1.48  --sup_to_prop_solver                    passive
% 7.33/1.48  --sup_prop_simpl_new                    true
% 7.33/1.48  --sup_prop_simpl_given                  true
% 7.33/1.48  --sup_fun_splitting                     true
% 7.33/1.48  --sup_smt_interval                      50000
% 7.33/1.48  
% 7.33/1.48  ------ Superposition Simplification Setup
% 7.33/1.48  
% 7.33/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.33/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.33/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.33/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.33/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.33/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.33/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.33/1.48  --sup_immed_triv                        [TrivRules]
% 7.33/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.48  --sup_immed_bw_main                     []
% 7.33/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.33/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.33/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.33/1.48  --sup_input_bw                          []
% 7.33/1.48  
% 7.33/1.48  ------ Combination Options
% 7.33/1.48  
% 7.33/1.48  --comb_res_mult                         3
% 7.33/1.48  --comb_sup_mult                         2
% 7.33/1.48  --comb_inst_mult                        10
% 7.33/1.48  
% 7.33/1.48  ------ Debug Options
% 7.33/1.48  
% 7.33/1.48  --dbg_backtrace                         false
% 7.33/1.48  --dbg_dump_prop_clauses                 false
% 7.33/1.48  --dbg_dump_prop_clauses_file            -
% 7.33/1.48  --dbg_out_stat                          false
% 7.33/1.48  
% 7.33/1.48  
% 7.33/1.48  
% 7.33/1.48  
% 7.33/1.48  ------ Proving...
% 7.33/1.48  
% 7.33/1.48  
% 7.33/1.48  % SZS status Theorem for theBenchmark.p
% 7.33/1.48  
% 7.33/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.33/1.48  
% 7.33/1.48  fof(f11,axiom,(
% 7.33/1.48    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f38,plain,(
% 7.33/1.48    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.33/1.48    inference(ennf_transformation,[],[f11])).
% 7.33/1.48  
% 7.33/1.48  fof(f39,plain,(
% 7.33/1.48    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.33/1.48    inference(flattening,[],[f38])).
% 7.33/1.48  
% 7.33/1.48  fof(f73,plain,(
% 7.33/1.48    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f39])).
% 7.33/1.48  
% 7.33/1.48  fof(f17,conjecture,(
% 7.33/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f18,negated_conjecture,(
% 7.33/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 7.33/1.48    inference(negated_conjecture,[],[f17])).
% 7.33/1.48  
% 7.33/1.48  fof(f49,plain,(
% 7.33/1.48    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.33/1.48    inference(ennf_transformation,[],[f18])).
% 7.33/1.48  
% 7.33/1.48  fof(f50,plain,(
% 7.33/1.48    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.33/1.48    inference(flattening,[],[f49])).
% 7.33/1.48  
% 7.33/1.48  fof(f56,plain,(
% 7.33/1.48    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 7.33/1.48    introduced(choice_axiom,[])).
% 7.33/1.48  
% 7.33/1.48  fof(f55,plain,(
% 7.33/1.48    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 7.33/1.48    introduced(choice_axiom,[])).
% 7.33/1.48  
% 7.33/1.48  fof(f54,plain,(
% 7.33/1.48    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 7.33/1.48    introduced(choice_axiom,[])).
% 7.33/1.48  
% 7.33/1.48  fof(f57,plain,(
% 7.33/1.48    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 7.33/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f50,f56,f55,f54])).
% 7.33/1.48  
% 7.33/1.48  fof(f85,plain,(
% 7.33/1.48    m1_pre_topc(sK2,sK1)),
% 7.33/1.48    inference(cnf_transformation,[],[f57])).
% 7.33/1.48  
% 7.33/1.48  fof(f88,plain,(
% 7.33/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 7.33/1.48    inference(cnf_transformation,[],[f57])).
% 7.33/1.48  
% 7.33/1.48  fof(f9,axiom,(
% 7.33/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f34,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.33/1.48    inference(ennf_transformation,[],[f9])).
% 7.33/1.48  
% 7.33/1.48  fof(f35,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.33/1.48    inference(flattening,[],[f34])).
% 7.33/1.48  
% 7.33/1.48  fof(f67,plain,(
% 7.33/1.48    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f35])).
% 7.33/1.48  
% 7.33/1.48  fof(f81,plain,(
% 7.33/1.48    ~v2_struct_0(sK1)),
% 7.33/1.48    inference(cnf_transformation,[],[f57])).
% 7.33/1.48  
% 7.33/1.48  fof(f82,plain,(
% 7.33/1.48    v2_pre_topc(sK1)),
% 7.33/1.48    inference(cnf_transformation,[],[f57])).
% 7.33/1.48  
% 7.33/1.48  fof(f83,plain,(
% 7.33/1.48    l1_pre_topc(sK1)),
% 7.33/1.48    inference(cnf_transformation,[],[f57])).
% 7.33/1.48  
% 7.33/1.48  fof(f86,plain,(
% 7.33/1.48    v1_funct_1(sK3)),
% 7.33/1.48    inference(cnf_transformation,[],[f57])).
% 7.33/1.48  
% 7.33/1.48  fof(f87,plain,(
% 7.33/1.48    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 7.33/1.48    inference(cnf_transformation,[],[f57])).
% 7.33/1.48  
% 7.33/1.48  fof(f12,axiom,(
% 7.33/1.48    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f40,plain,(
% 7.33/1.48    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.33/1.48    inference(ennf_transformation,[],[f12])).
% 7.33/1.48  
% 7.33/1.48  fof(f74,plain,(
% 7.33/1.48    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f40])).
% 7.33/1.48  
% 7.33/1.48  fof(f8,axiom,(
% 7.33/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f32,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.33/1.48    inference(ennf_transformation,[],[f8])).
% 7.33/1.48  
% 7.33/1.48  fof(f33,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.33/1.48    inference(flattening,[],[f32])).
% 7.33/1.48  
% 7.33/1.48  fof(f66,plain,(
% 7.33/1.48    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f33])).
% 7.33/1.48  
% 7.33/1.48  fof(f84,plain,(
% 7.33/1.48    ~v2_struct_0(sK2)),
% 7.33/1.48    inference(cnf_transformation,[],[f57])).
% 7.33/1.48  
% 7.33/1.48  fof(f6,axiom,(
% 7.33/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f29,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.33/1.48    inference(ennf_transformation,[],[f6])).
% 7.33/1.48  
% 7.33/1.48  fof(f64,plain,(
% 7.33/1.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f29])).
% 7.33/1.48  
% 7.33/1.48  fof(f5,axiom,(
% 7.33/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f27,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.33/1.48    inference(ennf_transformation,[],[f5])).
% 7.33/1.48  
% 7.33/1.48  fof(f28,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.33/1.48    inference(flattening,[],[f27])).
% 7.33/1.48  
% 7.33/1.48  fof(f63,plain,(
% 7.33/1.48    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f28])).
% 7.33/1.48  
% 7.33/1.48  fof(f10,axiom,(
% 7.33/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f36,plain,(
% 7.33/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.33/1.48    inference(ennf_transformation,[],[f10])).
% 7.33/1.48  
% 7.33/1.48  fof(f37,plain,(
% 7.33/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.33/1.48    inference(flattening,[],[f36])).
% 7.33/1.48  
% 7.33/1.48  fof(f70,plain,(
% 7.33/1.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f37])).
% 7.33/1.48  
% 7.33/1.48  fof(f4,axiom,(
% 7.33/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f25,plain,(
% 7.33/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.33/1.48    inference(ennf_transformation,[],[f4])).
% 7.33/1.48  
% 7.33/1.48  fof(f26,plain,(
% 7.33/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.33/1.48    inference(flattening,[],[f25])).
% 7.33/1.48  
% 7.33/1.48  fof(f51,plain,(
% 7.33/1.48    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.33/1.48    inference(nnf_transformation,[],[f26])).
% 7.33/1.48  
% 7.33/1.48  fof(f61,plain,(
% 7.33/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f51])).
% 7.33/1.48  
% 7.33/1.48  fof(f14,axiom,(
% 7.33/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f43,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.33/1.48    inference(ennf_transformation,[],[f14])).
% 7.33/1.48  
% 7.33/1.48  fof(f44,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.33/1.48    inference(flattening,[],[f43])).
% 7.33/1.48  
% 7.33/1.48  fof(f78,plain,(
% 7.33/1.48    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f44])).
% 7.33/1.48  
% 7.33/1.48  fof(f69,plain,(
% 7.33/1.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f37])).
% 7.33/1.48  
% 7.33/1.48  fof(f68,plain,(
% 7.33/1.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f37])).
% 7.33/1.48  
% 7.33/1.48  fof(f13,axiom,(
% 7.33/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f41,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.33/1.48    inference(ennf_transformation,[],[f13])).
% 7.33/1.48  
% 7.33/1.48  fof(f42,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.33/1.48    inference(flattening,[],[f41])).
% 7.33/1.48  
% 7.33/1.48  fof(f52,plain,(
% 7.33/1.48    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) => (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))))),
% 7.33/1.48    introduced(choice_axiom,[])).
% 7.33/1.48  
% 7.33/1.48  fof(f53,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.33/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f52])).
% 7.33/1.48  
% 7.33/1.48  fof(f76,plain,(
% 7.33/1.48    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f53])).
% 7.33/1.48  
% 7.33/1.48  fof(f75,plain,(
% 7.33/1.48    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f53])).
% 7.33/1.48  
% 7.33/1.48  fof(f7,axiom,(
% 7.33/1.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f30,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 7.33/1.48    inference(ennf_transformation,[],[f7])).
% 7.33/1.48  
% 7.33/1.48  fof(f31,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 7.33/1.48    inference(flattening,[],[f30])).
% 7.33/1.48  
% 7.33/1.48  fof(f65,plain,(
% 7.33/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f31])).
% 7.33/1.48  
% 7.33/1.48  fof(f16,axiom,(
% 7.33/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f47,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.33/1.48    inference(ennf_transformation,[],[f16])).
% 7.33/1.48  
% 7.33/1.48  fof(f48,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.33/1.48    inference(flattening,[],[f47])).
% 7.33/1.48  
% 7.33/1.48  fof(f80,plain,(
% 7.33/1.48    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f48])).
% 7.33/1.48  
% 7.33/1.48  fof(f3,axiom,(
% 7.33/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f23,plain,(
% 7.33/1.48    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 7.33/1.48    inference(ennf_transformation,[],[f3])).
% 7.33/1.48  
% 7.33/1.48  fof(f24,plain,(
% 7.33/1.48    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 7.33/1.48    inference(flattening,[],[f23])).
% 7.33/1.48  
% 7.33/1.48  fof(f60,plain,(
% 7.33/1.48    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f24])).
% 7.33/1.48  
% 7.33/1.48  fof(f90,plain,(
% 7.33/1.48    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)),
% 7.33/1.48    inference(cnf_transformation,[],[f57])).
% 7.33/1.48  
% 7.33/1.48  fof(f71,plain,(
% 7.33/1.48    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f39])).
% 7.33/1.48  
% 7.33/1.48  fof(f62,plain,(
% 7.33/1.48    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f51])).
% 7.33/1.48  
% 7.33/1.48  fof(f91,plain,(
% 7.33/1.48    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.33/1.48    inference(equality_resolution,[],[f62])).
% 7.33/1.48  
% 7.33/1.48  fof(f72,plain,(
% 7.33/1.48    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f39])).
% 7.33/1.48  
% 7.33/1.48  fof(f1,axiom,(
% 7.33/1.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f19,plain,(
% 7.33/1.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 7.33/1.48    inference(unused_predicate_definition_removal,[],[f1])).
% 7.33/1.48  
% 7.33/1.48  fof(f20,plain,(
% 7.33/1.48    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 7.33/1.48    inference(ennf_transformation,[],[f19])).
% 7.33/1.48  
% 7.33/1.48  fof(f58,plain,(
% 7.33/1.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f20])).
% 7.33/1.48  
% 7.33/1.48  fof(f89,plain,(
% 7.33/1.48    ( ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) )),
% 7.33/1.48    inference(cnf_transformation,[],[f57])).
% 7.33/1.48  
% 7.33/1.48  fof(f2,axiom,(
% 7.33/1.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.33/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.33/1.48  
% 7.33/1.48  fof(f21,plain,(
% 7.33/1.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.33/1.48    inference(ennf_transformation,[],[f2])).
% 7.33/1.48  
% 7.33/1.48  fof(f22,plain,(
% 7.33/1.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.33/1.48    inference(flattening,[],[f21])).
% 7.33/1.48  
% 7.33/1.48  fof(f59,plain,(
% 7.33/1.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f22])).
% 7.33/1.48  
% 7.33/1.48  fof(f77,plain,(
% 7.33/1.48    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.33/1.48    inference(cnf_transformation,[],[f53])).
% 7.33/1.48  
% 7.33/1.48  cnf(c_13,plain,
% 7.33/1.48      ( ~ m1_pre_topc(X0,X1)
% 7.33/1.48      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.33/1.48      | v2_struct_0(X1)
% 7.33/1.48      | ~ l1_pre_topc(X1)
% 7.33/1.48      | ~ v2_pre_topc(X1) ),
% 7.33/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.33/1.48  
% 7.33/1.48  cnf(c_1151,plain,
% 7.33/1.48      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.33/1.48      | m1_subset_1(k4_tmap_1(X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.33/1.48      | v2_struct_0(X1_51)
% 7.33/1.48      | ~ l1_pre_topc(X1_51)
% 7.33/1.48      | ~ v2_pre_topc(X1_51) ),
% 7.33/1.48      inference(subtyping,[status(esa)],[c_13]) ).
% 7.33/1.48  
% 7.33/1.48  cnf(c_1730,plain,
% 7.33/1.48      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.33/1.48      | m1_subset_1(k4_tmap_1(X1_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) = iProver_top
% 7.33/1.48      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.48      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.48      | v2_pre_topc(X1_51) != iProver_top ),
% 7.33/1.48      inference(predicate_to_equality,[status(thm)],[c_1151]) ).
% 7.33/1.48  
% 7.33/1.48  cnf(c_28,negated_conjecture,
% 7.33/1.48      ( m1_pre_topc(sK2,sK1) ),
% 7.33/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.33/1.48  
% 7.33/1.48  cnf(c_1136,negated_conjecture,
% 7.33/1.48      ( m1_pre_topc(sK2,sK1) ),
% 7.33/1.48      inference(subtyping,[status(esa)],[c_28]) ).
% 7.33/1.48  
% 7.33/1.48  cnf(c_1745,plain,
% 7.33/1.48      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.33/1.48      inference(predicate_to_equality,[status(thm)],[c_1136]) ).
% 7.33/1.48  
% 7.33/1.48  cnf(c_25,negated_conjecture,
% 7.33/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 7.33/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.33/1.48  
% 7.33/1.48  cnf(c_1139,negated_conjecture,
% 7.33/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 7.33/1.48      inference(subtyping,[status(esa)],[c_25]) ).
% 7.33/1.48  
% 7.33/1.48  cnf(c_1742,plain,
% 7.33/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.33/1.48      inference(predicate_to_equality,[status(thm)],[c_1139]) ).
% 7.33/1.48  
% 7.33/1.48  cnf(c_9,plain,
% 7.33/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.33/1.48      | ~ m1_pre_topc(X3,X4)
% 7.33/1.48      | ~ m1_pre_topc(X3,X1)
% 7.33/1.48      | ~ m1_pre_topc(X1,X4)
% 7.33/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.33/1.48      | v2_struct_0(X4)
% 7.33/1.48      | v2_struct_0(X2)
% 7.33/1.48      | ~ l1_pre_topc(X4)
% 7.33/1.48      | ~ l1_pre_topc(X2)
% 7.33/1.48      | ~ v2_pre_topc(X4)
% 7.33/1.48      | ~ v2_pre_topc(X2)
% 7.33/1.48      | ~ v1_funct_1(X0)
% 7.33/1.48      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 7.33/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.33/1.48  
% 7.33/1.48  cnf(c_1155,plain,
% 7.33/1.48      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.33/1.48      | ~ m1_pre_topc(X2_51,X0_51)
% 7.33/1.48      | ~ m1_pre_topc(X0_51,X3_51)
% 7.33/1.48      | ~ m1_pre_topc(X2_51,X3_51)
% 7.33/1.48      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.33/1.48      | v2_struct_0(X1_51)
% 7.33/1.48      | v2_struct_0(X3_51)
% 7.33/1.48      | ~ l1_pre_topc(X1_51)
% 7.33/1.48      | ~ l1_pre_topc(X3_51)
% 7.33/1.48      | ~ v2_pre_topc(X1_51)
% 7.33/1.48      | ~ v2_pre_topc(X3_51)
% 7.33/1.48      | ~ v1_funct_1(X0_52)
% 7.33/1.48      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52) ),
% 7.33/1.48      inference(subtyping,[status(esa)],[c_9]) ).
% 7.33/1.48  
% 7.33/1.48  cnf(c_1726,plain,
% 7.33/1.48      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k3_tmap_1(X3_51,X1_51,X0_51,X2_51,X0_52)
% 7.33/1.48      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.33/1.48      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 7.33/1.48      | m1_pre_topc(X0_51,X3_51) != iProver_top
% 7.33/1.48      | m1_pre_topc(X2_51,X3_51) != iProver_top
% 7.33/1.48      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.33/1.48      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.48      | v2_struct_0(X3_51) = iProver_top
% 7.33/1.48      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.48      | l1_pre_topc(X3_51) != iProver_top
% 7.33/1.48      | v2_pre_topc(X1_51) != iProver_top
% 7.33/1.48      | v2_pre_topc(X3_51) != iProver_top
% 7.33/1.48      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.48      inference(predicate_to_equality,[status(thm)],[c_1155]) ).
% 7.33/1.48  
% 7.33/1.48  cnf(c_4312,plain,
% 7.33/1.48      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
% 7.33/1.48      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.48      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.33/1.48      | m1_pre_topc(X0_51,sK2) != iProver_top
% 7.33/1.48      | m1_pre_topc(sK2,X1_51) != iProver_top
% 7.33/1.48      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.48      | v2_struct_0(sK1) = iProver_top
% 7.33/1.48      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.48      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.48      | v2_pre_topc(X1_51) != iProver_top
% 7.33/1.48      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.33/1.48      inference(superposition,[status(thm)],[c_1742,c_1726]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_32,negated_conjecture,
% 7.33/1.49      ( ~ v2_struct_0(sK1) ),
% 7.33/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_33,plain,
% 7.33/1.49      ( v2_struct_0(sK1) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_31,negated_conjecture,
% 7.33/1.49      ( v2_pre_topc(sK1) ),
% 7.33/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_34,plain,
% 7.33/1.49      ( v2_pre_topc(sK1) = iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_30,negated_conjecture,
% 7.33/1.49      ( l1_pre_topc(sK1) ),
% 7.33/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_35,plain,
% 7.33/1.49      ( l1_pre_topc(sK1) = iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_27,negated_conjecture,
% 7.33/1.49      ( v1_funct_1(sK3) ),
% 7.33/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_38,plain,
% 7.33/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_26,negated_conjecture,
% 7.33/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 7.33/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_39,plain,
% 7.33/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_4706,plain,
% 7.33/1.49      ( l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
% 7.33/1.49      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,sK2) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,X1_51) != iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | v2_pre_topc(X1_51) != iProver_top ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_4312,c_33,c_34,c_35,c_38,c_39]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_4707,plain,
% 7.33/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)
% 7.33/1.49      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,sK2) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,X1_51) != iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X1_51) != iProver_top ),
% 7.33/1.49      inference(renaming,[status(thm)],[c_4706]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_4712,plain,
% 7.33/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK1,sK1,sK2,sK2,sK3)
% 7.33/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_1745,c_4707]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_16,plain,
% 7.33/1.49      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.33/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1148,plain,
% 7.33/1.49      ( m1_pre_topc(X0_51,X0_51) | ~ l1_pre_topc(X0_51) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1733,plain,
% 7.33/1.49      ( m1_pre_topc(X0_51,X0_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X0_51) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1148]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_8,plain,
% 7.33/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.33/1.49      | ~ m1_pre_topc(X3,X1)
% 7.33/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.33/1.49      | v2_struct_0(X1)
% 7.33/1.49      | v2_struct_0(X2)
% 7.33/1.49      | ~ l1_pre_topc(X1)
% 7.33/1.49      | ~ l1_pre_topc(X2)
% 7.33/1.49      | ~ v2_pre_topc(X1)
% 7.33/1.49      | ~ v2_pre_topc(X2)
% 7.33/1.49      | ~ v1_funct_1(X0)
% 7.33/1.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.33/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1156,plain,
% 7.33/1.49      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.33/1.49      | ~ m1_pre_topc(X2_51,X0_51)
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.33/1.49      | v2_struct_0(X1_51)
% 7.33/1.49      | v2_struct_0(X0_51)
% 7.33/1.49      | ~ l1_pre_topc(X1_51)
% 7.33/1.49      | ~ l1_pre_topc(X0_51)
% 7.33/1.49      | ~ v2_pre_topc(X1_51)
% 7.33/1.49      | ~ v2_pre_topc(X0_51)
% 7.33/1.49      | ~ v1_funct_1(X0_52)
% 7.33/1.49      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_52,X2_51) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1725,plain,
% 7.33/1.49      ( k2_partfun1(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,u1_struct_0(X2_51)) = k2_tmap_1(X0_51,X1_51,X0_52,X2_51)
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.33/1.49      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.33/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X0_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1156]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3553,plain,
% 7.33/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51)
% 7.33/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,sK2) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | v2_struct_0(sK2) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.33/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_1742,c_1725]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_29,negated_conjecture,
% 7.33/1.49      ( ~ v2_struct_0(sK2) ),
% 7.33/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_36,plain,
% 7.33/1.49      ( v2_struct_0(sK2) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_37,plain,
% 7.33/1.49      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_6,plain,
% 7.33/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.33/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1158,plain,
% 7.33/1.49      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.33/1.49      | ~ l1_pre_topc(X1_51)
% 7.33/1.49      | l1_pre_topc(X0_51) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1916,plain,
% 7.33/1.49      ( ~ m1_pre_topc(sK2,X0_51)
% 7.33/1.49      | ~ l1_pre_topc(X0_51)
% 7.33/1.49      | l1_pre_topc(sK2) ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1158]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1917,plain,
% 7.33/1.49      ( m1_pre_topc(sK2,X0_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(sK2) = iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1916]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1919,plain,
% 7.33/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | l1_pre_topc(sK2) = iProver_top ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1917]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5,plain,
% 7.33/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.33/1.49      | ~ l1_pre_topc(X1)
% 7.33/1.49      | ~ v2_pre_topc(X1)
% 7.33/1.49      | v2_pre_topc(X0) ),
% 7.33/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1159,plain,
% 7.33/1.49      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.33/1.49      | ~ l1_pre_topc(X1_51)
% 7.33/1.49      | ~ v2_pre_topc(X1_51)
% 7.33/1.49      | v2_pre_topc(X0_51) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_2157,plain,
% 7.33/1.49      ( ~ m1_pre_topc(sK2,X0_51)
% 7.33/1.49      | ~ l1_pre_topc(X0_51)
% 7.33/1.49      | ~ v2_pre_topc(X0_51)
% 7.33/1.49      | v2_pre_topc(sK2) ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1159]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_2158,plain,
% 7.33/1.49      ( m1_pre_topc(sK2,X0_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X0_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK2) = iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_2157]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_2160,plain,
% 7.33/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK2) = iProver_top ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_2158]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3797,plain,
% 7.33/1.49      ( m1_pre_topc(X0_51,sK2) != iProver_top
% 7.33/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51) ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_3553,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_1919,c_2160]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3798,plain,
% 7.33/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,sK3,X0_51)
% 7.33/1.49      | m1_pre_topc(X0_51,sK2) != iProver_top ),
% 7.33/1.49      inference(renaming,[status(thm)],[c_3797]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3803,plain,
% 7.33/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2)
% 7.33/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_1733,c_3798]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1918,plain,
% 7.33/1.49      ( ~ m1_pre_topc(sK2,sK1) | ~ l1_pre_topc(sK1) | l1_pre_topc(sK2) ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1916]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_2159,plain,
% 7.33/1.49      ( ~ m1_pre_topc(sK2,sK1)
% 7.33/1.49      | ~ l1_pre_topc(sK1)
% 7.33/1.49      | ~ v2_pre_topc(sK1)
% 7.33/1.49      | v2_pre_topc(sK2) ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_2157]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_2541,plain,
% 7.33/1.49      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1148]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1799,plain,
% 7.33/1.49      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(sK1))
% 7.33/1.49      | ~ m1_pre_topc(X1_51,X0_51)
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
% 7.33/1.49      | v2_struct_0(X0_51)
% 7.33/1.49      | v2_struct_0(sK1)
% 7.33/1.49      | ~ l1_pre_topc(X0_51)
% 7.33/1.49      | ~ l1_pre_topc(sK1)
% 7.33/1.49      | ~ v2_pre_topc(X0_51)
% 7.33/1.49      | ~ v2_pre_topc(sK1)
% 7.33/1.49      | ~ v1_funct_1(X0_52)
% 7.33/1.49      | k2_partfun1(u1_struct_0(X0_51),u1_struct_0(sK1),X0_52,u1_struct_0(X1_51)) = k2_tmap_1(X0_51,sK1,X0_52,X1_51) ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1156]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_2600,plain,
% 7.33/1.49      ( ~ v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.33/1.49      | ~ m1_pre_topc(X0_51,sK2)
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.33/1.49      | v2_struct_0(sK1)
% 7.33/1.49      | v2_struct_0(sK2)
% 7.33/1.49      | ~ l1_pre_topc(sK1)
% 7.33/1.49      | ~ l1_pre_topc(sK2)
% 7.33/1.49      | ~ v2_pre_topc(sK1)
% 7.33/1.49      | ~ v2_pre_topc(sK2)
% 7.33/1.49      | ~ v1_funct_1(X0_52)
% 7.33/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,u1_struct_0(X0_51)) = k2_tmap_1(sK2,sK1,X0_52,X0_51) ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1799]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3580,plain,
% 7.33/1.49      ( ~ v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.33/1.49      | ~ m1_pre_topc(sK2,sK2)
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.33/1.49      | v2_struct_0(sK1)
% 7.33/1.49      | v2_struct_0(sK2)
% 7.33/1.49      | ~ l1_pre_topc(sK1)
% 7.33/1.49      | ~ l1_pre_topc(sK2)
% 7.33/1.49      | ~ v2_pre_topc(sK1)
% 7.33/1.49      | ~ v2_pre_topc(sK2)
% 7.33/1.49      | ~ v1_funct_1(X0_52)
% 7.33/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,X0_52,sK2) ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_2600]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3582,plain,
% 7.33/1.49      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.33/1.49      | ~ m1_pre_topc(sK2,sK2)
% 7.33/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.33/1.49      | v2_struct_0(sK1)
% 7.33/1.49      | v2_struct_0(sK2)
% 7.33/1.49      | ~ l1_pre_topc(sK1)
% 7.33/1.49      | ~ l1_pre_topc(sK2)
% 7.33/1.49      | ~ v2_pre_topc(sK1)
% 7.33/1.49      | ~ v2_pre_topc(sK2)
% 7.33/1.49      | ~ v1_funct_1(sK3)
% 7.33/1.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_3580]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3875,plain,
% 7.33/1.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_3803,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25,c_1918,
% 7.33/1.49                 c_2159,c_2541,c_3582]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_4714,plain,
% 7.33/1.49      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2)
% 7.33/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.33/1.49      inference(light_normalisation,[status(thm)],[c_4712,c_3875]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_2542,plain,
% 7.33/1.49      ( m1_pre_topc(sK2,sK2) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_2541]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_4736,plain,
% 7.33/1.49      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_4714,c_33,c_34,c_35,c_37,c_1919,c_2542]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_10,plain,
% 7.33/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.33/1.49      | ~ m1_pre_topc(X3,X4)
% 7.33/1.49      | ~ m1_pre_topc(X1,X4)
% 7.33/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.33/1.49      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 7.33/1.49      | v2_struct_0(X4)
% 7.33/1.49      | v2_struct_0(X2)
% 7.33/1.49      | ~ l1_pre_topc(X4)
% 7.33/1.49      | ~ l1_pre_topc(X2)
% 7.33/1.49      | ~ v2_pre_topc(X4)
% 7.33/1.49      | ~ v2_pre_topc(X2)
% 7.33/1.49      | ~ v1_funct_1(X0) ),
% 7.33/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1154,plain,
% 7.33/1.49      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.33/1.49      | ~ m1_pre_topc(X0_51,X2_51)
% 7.33/1.49      | ~ m1_pre_topc(X3_51,X2_51)
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.33/1.49      | m1_subset_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51))))
% 7.33/1.49      | v2_struct_0(X1_51)
% 7.33/1.49      | v2_struct_0(X2_51)
% 7.33/1.49      | ~ l1_pre_topc(X1_51)
% 7.33/1.49      | ~ l1_pre_topc(X2_51)
% 7.33/1.49      | ~ v2_pre_topc(X1_51)
% 7.33/1.49      | ~ v2_pre_topc(X2_51)
% 7.33/1.49      | ~ v1_funct_1(X0_52) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1727,plain,
% 7.33/1.49      ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 7.33/1.49      | m1_pre_topc(X3_51,X2_51) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.33/1.49      | m1_subset_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_51),u1_struct_0(X1_51)))) = iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X2_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(X2_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X2_51) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1154]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_4739,plain,
% 7.33/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | m1_subset_1(k2_tmap_1(sK2,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 7.33/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_4736,c_1727]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_40,plain,
% 7.33/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5189,plain,
% 7.33/1.49      ( m1_subset_1(k2_tmap_1(sK2,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_4739,c_33,c_34,c_35,c_37,c_38,c_39,c_40]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_4,plain,
% 7.33/1.49      ( ~ r2_funct_2(X0,X1,X2,X3)
% 7.33/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.33/1.49      | ~ v1_funct_2(X3,X0,X1)
% 7.33/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.33/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.33/1.49      | ~ v1_funct_1(X2)
% 7.33/1.49      | ~ v1_funct_1(X3)
% 7.33/1.49      | X3 = X2 ),
% 7.33/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1160,plain,
% 7.33/1.49      ( ~ r2_funct_2(X0_53,X1_53,X0_52,X1_52)
% 7.33/1.49      | ~ v1_funct_2(X0_52,X0_53,X1_53)
% 7.33/1.49      | ~ v1_funct_2(X1_52,X0_53,X1_53)
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.33/1.49      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.33/1.49      | ~ v1_funct_1(X0_52)
% 7.33/1.49      | ~ v1_funct_1(X1_52)
% 7.33/1.49      | X1_52 = X0_52 ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1721,plain,
% 7.33/1.49      ( X0_52 = X1_52
% 7.33/1.49      | r2_funct_2(X0_53,X1_53,X1_52,X0_52) != iProver_top
% 7.33/1.49      | v1_funct_2(X1_52,X0_53,X1_53) != iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 7.33/1.49      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.33/1.49      | v1_funct_1(X1_52) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1160]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3099,plain,
% 7.33/1.49      ( sK3 = X0_52
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,sK3) != iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_1742,c_1721]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3437,plain,
% 7.33/1.49      ( v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | sK3 = X0_52
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,sK3) != iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_3099,c_38,c_39]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3438,plain,
% 7.33/1.49      ( sK3 = X0_52
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,sK3) != iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(renaming,[status(thm)],[c_3437]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5200,plain,
% 7.33/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),sK3) != iProver_top
% 7.33/1.49      | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_5189,c_3438]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_20,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
% 7.33/1.49      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 7.33/1.49      | ~ m1_pre_topc(X0,X3)
% 7.33/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.33/1.49      | v2_struct_0(X3)
% 7.33/1.49      | v2_struct_0(X1)
% 7.33/1.49      | v2_struct_0(X0)
% 7.33/1.49      | ~ l1_pre_topc(X3)
% 7.33/1.49      | ~ l1_pre_topc(X1)
% 7.33/1.49      | ~ v2_pre_topc(X3)
% 7.33/1.49      | ~ v2_pre_topc(X1)
% 7.33/1.49      | ~ v1_funct_1(X2) ),
% 7.33/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1144,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,k3_tmap_1(X2_51,X1_51,X0_51,X0_51,X0_52))
% 7.33/1.49      | ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.33/1.49      | ~ m1_pre_topc(X0_51,X2_51)
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.33/1.49      | v2_struct_0(X1_51)
% 7.33/1.49      | v2_struct_0(X0_51)
% 7.33/1.49      | v2_struct_0(X2_51)
% 7.33/1.49      | ~ l1_pre_topc(X1_51)
% 7.33/1.49      | ~ l1_pre_topc(X2_51)
% 7.33/1.49      | ~ v2_pre_topc(X1_51)
% 7.33/1.49      | ~ v2_pre_topc(X2_51)
% 7.33/1.49      | ~ v1_funct_1(X0_52) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_20]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1737,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,k3_tmap_1(X2_51,X1_51,X0_51,X0_51,X0_52)) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.33/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X2_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(X2_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X2_51) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1144]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_4738,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top
% 7.33/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | v2_struct_0(sK2) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_4736,c_1737]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_11,plain,
% 7.33/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.33/1.49      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 7.33/1.49      | ~ m1_pre_topc(X4,X3)
% 7.33/1.49      | ~ m1_pre_topc(X1,X3)
% 7.33/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.33/1.49      | v2_struct_0(X3)
% 7.33/1.49      | v2_struct_0(X2)
% 7.33/1.49      | ~ l1_pre_topc(X3)
% 7.33/1.49      | ~ l1_pre_topc(X2)
% 7.33/1.49      | ~ v2_pre_topc(X3)
% 7.33/1.49      | ~ v2_pre_topc(X2)
% 7.33/1.49      | ~ v1_funct_1(X0) ),
% 7.33/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1153,plain,
% 7.33/1.49      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.33/1.49      | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),u1_struct_0(X3_51),u1_struct_0(X1_51))
% 7.33/1.49      | ~ m1_pre_topc(X0_51,X2_51)
% 7.33/1.49      | ~ m1_pre_topc(X3_51,X2_51)
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.33/1.49      | v2_struct_0(X1_51)
% 7.33/1.49      | v2_struct_0(X2_51)
% 7.33/1.49      | ~ l1_pre_topc(X1_51)
% 7.33/1.49      | ~ l1_pre_topc(X2_51)
% 7.33/1.49      | ~ v2_pre_topc(X1_51)
% 7.33/1.49      | ~ v2_pre_topc(X2_51)
% 7.33/1.49      | ~ v1_funct_1(X0_52) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1728,plain,
% 7.33/1.49      ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.33/1.49      | v1_funct_2(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52),u1_struct_0(X3_51),u1_struct_0(X1_51)) = iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 7.33/1.49      | m1_pre_topc(X3_51,X2_51) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X2_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(X2_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X2_51) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1153]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_4740,plain,
% 7.33/1.49      ( v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.33/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_4736,c_1728]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_12,plain,
% 7.33/1.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.33/1.49      | ~ m1_pre_topc(X3,X4)
% 7.33/1.49      | ~ m1_pre_topc(X1,X4)
% 7.33/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.33/1.49      | v2_struct_0(X4)
% 7.33/1.49      | v2_struct_0(X2)
% 7.33/1.49      | ~ l1_pre_topc(X4)
% 7.33/1.49      | ~ l1_pre_topc(X2)
% 7.33/1.49      | ~ v2_pre_topc(X4)
% 7.33/1.49      | ~ v2_pre_topc(X2)
% 7.33/1.49      | ~ v1_funct_1(X0)
% 7.33/1.49      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 7.33/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1152,plain,
% 7.33/1.49      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.33/1.49      | ~ m1_pre_topc(X0_51,X2_51)
% 7.33/1.49      | ~ m1_pre_topc(X3_51,X2_51)
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.33/1.49      | v2_struct_0(X1_51)
% 7.33/1.49      | v2_struct_0(X2_51)
% 7.33/1.49      | ~ l1_pre_topc(X1_51)
% 7.33/1.49      | ~ l1_pre_topc(X2_51)
% 7.33/1.49      | ~ v2_pre_topc(X1_51)
% 7.33/1.49      | ~ v2_pre_topc(X2_51)
% 7.33/1.49      | ~ v1_funct_1(X0_52)
% 7.33/1.49      | v1_funct_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52)) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1729,plain,
% 7.33/1.49      ( v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 7.33/1.49      | m1_pre_topc(X3_51,X2_51) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X2_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(X2_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X2_51) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | v1_funct_1(k3_tmap_1(X2_51,X1_51,X0_51,X3_51,X0_52)) = iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1152]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3562,plain,
% 7.33/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,X1_51) != iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)) = iProver_top
% 7.33/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_1742,c_1729]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1801,plain,
% 7.33/1.49      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(sK1))
% 7.33/1.49      | ~ m1_pre_topc(X0_51,X1_51)
% 7.33/1.49      | ~ m1_pre_topc(X2_51,X1_51)
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(sK1))))
% 7.33/1.49      | v2_struct_0(X1_51)
% 7.33/1.49      | v2_struct_0(sK1)
% 7.33/1.49      | ~ l1_pre_topc(X1_51)
% 7.33/1.49      | ~ l1_pre_topc(sK1)
% 7.33/1.49      | ~ v2_pre_topc(X1_51)
% 7.33/1.49      | ~ v2_pre_topc(sK1)
% 7.33/1.49      | ~ v1_funct_1(X0_52)
% 7.33/1.49      | v1_funct_1(k3_tmap_1(X1_51,sK1,X0_51,X2_51,X0_52)) ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1152]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1936,plain,
% 7.33/1.49      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.33/1.49      | ~ m1_pre_topc(X0_51,X1_51)
% 7.33/1.49      | ~ m1_pre_topc(sK2,X1_51)
% 7.33/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.33/1.49      | v2_struct_0(X1_51)
% 7.33/1.49      | v2_struct_0(sK1)
% 7.33/1.49      | ~ l1_pre_topc(X1_51)
% 7.33/1.49      | ~ l1_pre_topc(sK1)
% 7.33/1.49      | ~ v2_pre_topc(X1_51)
% 7.33/1.49      | ~ v2_pre_topc(sK1)
% 7.33/1.49      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3))
% 7.33/1.49      | ~ v1_funct_1(sK3) ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1801]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1937,plain,
% 7.33/1.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,X1_51) != iProver_top
% 7.33/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)) = iProver_top
% 7.33/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1936]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3868,plain,
% 7.33/1.49      ( v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)) = iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,X1_51) != iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | v2_pre_topc(X1_51) != iProver_top ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_3562,c_33,c_34,c_35,c_38,c_39,c_40,c_1937]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3869,plain,
% 7.33/1.49      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,X1_51) != iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v1_funct_1(k3_tmap_1(X1_51,sK1,sK2,X0_51,sK3)) = iProver_top ),
% 7.33/1.49      inference(renaming,[status(thm)],[c_3868]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_4741,plain,
% 7.33/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) = iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_4736,c_3869]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5196,plain,
% 7.33/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = X0_52
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_5189,c_1721]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5211,plain,
% 7.33/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 7.33/1.49      | v1_funct_2(k2_tmap_1(sK2,sK1,sK3,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v1_funct_1(k2_tmap_1(sK2,sK1,sK3,sK2)) != iProver_top
% 7.33/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_5196]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5263,plain,
% 7.33/1.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_5200,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_4738,
% 7.33/1.49                 c_4740,c_4741,c_5211]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_18,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 7.33/1.49      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 7.33/1.49      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 7.33/1.49      | ~ m1_pre_topc(X0,X2)
% 7.33/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.33/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.33/1.49      | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
% 7.33/1.49      | v2_struct_0(X1)
% 7.33/1.49      | v2_struct_0(X2)
% 7.33/1.49      | v2_struct_0(X0)
% 7.33/1.49      | ~ l1_pre_topc(X1)
% 7.33/1.49      | ~ l1_pre_topc(X2)
% 7.33/1.49      | ~ v2_pre_topc(X1)
% 7.33/1.49      | ~ v2_pre_topc(X2)
% 7.33/1.49      | ~ v1_funct_1(X3)
% 7.33/1.49      | ~ v1_funct_1(X4) ),
% 7.33/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1146,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52)
% 7.33/1.49      | ~ v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.33/1.49      | ~ v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51))
% 7.33/1.49      | ~ m1_pre_topc(X0_51,X2_51)
% 7.33/1.49      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
% 7.33/1.49      | r2_hidden(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X0_51))
% 7.33/1.49      | v2_struct_0(X1_51)
% 7.33/1.49      | v2_struct_0(X0_51)
% 7.33/1.49      | v2_struct_0(X2_51)
% 7.33/1.49      | ~ l1_pre_topc(X1_51)
% 7.33/1.49      | ~ l1_pre_topc(X2_51)
% 7.33/1.49      | ~ v2_pre_topc(X1_51)
% 7.33/1.49      | ~ v2_pre_topc(X2_51)
% 7.33/1.49      | ~ v1_funct_1(X0_52)
% 7.33/1.49      | ~ v1_funct_1(X1_52) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1735,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 7.33/1.49      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
% 7.33/1.49      | r2_hidden(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X0_51)) = iProver_top
% 7.33/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X2_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(X2_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X2_51) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | v1_funct_1(X1_52) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1146]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5272,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | v2_struct_0(sK2) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_5263,c_1735]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_6157,plain,
% 7.33/1.49      ( v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_5272,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_1919,
% 7.33/1.49                 c_2160,c_2542]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_6158,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(renaming,[status(thm)],[c_6157]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_19,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 7.33/1.49      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 7.33/1.49      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 7.33/1.49      | ~ m1_pre_topc(X0,X2)
% 7.33/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.33/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.33/1.49      | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2))
% 7.33/1.49      | v2_struct_0(X1)
% 7.33/1.49      | v2_struct_0(X2)
% 7.33/1.49      | v2_struct_0(X0)
% 7.33/1.49      | ~ l1_pre_topc(X1)
% 7.33/1.49      | ~ l1_pre_topc(X2)
% 7.33/1.49      | ~ v2_pre_topc(X1)
% 7.33/1.49      | ~ v2_pre_topc(X2)
% 7.33/1.49      | ~ v1_funct_1(X3)
% 7.33/1.49      | ~ v1_funct_1(X4) ),
% 7.33/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1145,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52)
% 7.33/1.49      | ~ v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.33/1.49      | ~ v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51))
% 7.33/1.49      | ~ m1_pre_topc(X0_51,X2_51)
% 7.33/1.49      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
% 7.33/1.49      | m1_subset_1(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X2_51))
% 7.33/1.49      | v2_struct_0(X1_51)
% 7.33/1.49      | v2_struct_0(X0_51)
% 7.33/1.49      | v2_struct_0(X2_51)
% 7.33/1.49      | ~ l1_pre_topc(X1_51)
% 7.33/1.49      | ~ l1_pre_topc(X2_51)
% 7.33/1.49      | ~ v2_pre_topc(X1_51)
% 7.33/1.49      | ~ v2_pre_topc(X2_51)
% 7.33/1.49      | ~ v1_funct_1(X0_52)
% 7.33/1.49      | ~ v1_funct_1(X1_52) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_19]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1736,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,X2_51) != iProver_top
% 7.33/1.49      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
% 7.33/1.49      | m1_subset_1(sK0(X1_51,X2_51,X0_51,X0_52,X1_52),u1_struct_0(X2_51)) = iProver_top
% 7.33/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X2_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(X2_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X2_51) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | v1_funct_1(X1_52) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1145]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5271,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 7.33/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | v2_struct_0(sK2) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_5263,c_1736]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5611,plain,
% 7.33/1.49      ( v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_5271,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_1919,
% 7.33/1.49                 c_2160,c_2542]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5612,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(renaming,[status(thm)],[c_5611]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7,plain,
% 7.33/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.33/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.33/1.49      | m1_subset_1(X2,u1_struct_0(X1))
% 7.33/1.49      | v2_struct_0(X1)
% 7.33/1.49      | v2_struct_0(X0)
% 7.33/1.49      | ~ l1_pre_topc(X1) ),
% 7.33/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1157,plain,
% 7.33/1.49      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.33/1.49      | ~ m1_subset_1(X0_52,u1_struct_0(X0_51))
% 7.33/1.49      | m1_subset_1(X0_52,u1_struct_0(X1_51))
% 7.33/1.49      | v2_struct_0(X1_51)
% 7.33/1.49      | v2_struct_0(X0_51)
% 7.33/1.49      | ~ l1_pre_topc(X1_51) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1724,plain,
% 7.33/1.49      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,u1_struct_0(X1_51)) = iProver_top
% 7.33/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1157]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5617,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) = iProver_top
% 7.33/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | v2_struct_0(sK2) = iProver_top
% 7.33/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_5612,c_1724]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_6473,plain,
% 7.33/1.49      ( v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) = iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_5617,c_36]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_6474,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) = iProver_top
% 7.33/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(renaming,[status(thm)],[c_6473]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_6480,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X1_51)) = iProver_top
% 7.33/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_6474,c_1724]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1198,plain,
% 7.33/1.49      ( m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(X0_51) = iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1158]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7654,plain,
% 7.33/1.49      ( v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X1_51)) = iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_6480,c_1198]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7655,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,X1_51) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,X0_51) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X1_51)) = iProver_top
% 7.33/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(renaming,[status(thm)],[c_7654]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7658,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | v2_struct_0(sK2) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_1745,c_7655]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7662,plain,
% 7.33/1.49      ( m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_7658,c_33,c_35,c_36,c_37,c_1919,c_2542]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7663,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK1)) = iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(renaming,[status(thm)],[c_7662]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_22,plain,
% 7.33/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.33/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.33/1.49      | ~ r2_hidden(X2,u1_struct_0(X0))
% 7.33/1.49      | v2_struct_0(X1)
% 7.33/1.49      | v2_struct_0(X0)
% 7.33/1.49      | ~ l1_pre_topc(X1)
% 7.33/1.49      | ~ v2_pre_topc(X1)
% 7.33/1.49      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 7.33/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1142,plain,
% 7.33/1.49      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.33/1.49      | ~ m1_subset_1(X0_52,u1_struct_0(X1_51))
% 7.33/1.49      | ~ r2_hidden(X0_52,u1_struct_0(X0_51))
% 7.33/1.49      | v2_struct_0(X1_51)
% 7.33/1.49      | v2_struct_0(X0_51)
% 7.33/1.49      | ~ l1_pre_topc(X1_51)
% 7.33/1.49      | ~ v2_pre_topc(X1_51)
% 7.33/1.49      | k1_funct_1(k4_tmap_1(X1_51,X0_51),X0_52) = X0_52 ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_22]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1739,plain,
% 7.33/1.49      ( k1_funct_1(k4_tmap_1(X0_51,X1_51),X0_52) = X0_52
% 7.33/1.49      | m1_pre_topc(X1_51,X0_51) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,u1_struct_0(X0_51)) != iProver_top
% 7.33/1.49      | r2_hidden(X0_52,u1_struct_0(X1_51)) != iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X0_51) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1142]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7668,plain,
% 7.33/1.49      ( k1_funct_1(k4_tmap_1(sK1,X0_51),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,sK1) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) != iProver_top
% 7.33/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_7663,c_1739]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7814,plain,
% 7.33/1.49      ( v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,sK1) != iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | k1_funct_1(k4_tmap_1(sK1,X0_51),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_7668,c_33,c_34,c_35]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7815,plain,
% 7.33/1.49      ( k1_funct_1(k4_tmap_1(sK1,X0_51),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(X0_51,sK1) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(X0_51)) != iProver_top
% 7.33/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(renaming,[status(thm)],[c_7814]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7818,plain,
% 7.33/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v2_struct_0(sK2) = iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_6158,c_7815]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7870,plain,
% 7.33/1.49      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_7818,c_36,c_37]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7871,plain,
% 7.33/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(renaming,[status(thm)],[c_7870]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7875,plain,
% 7.33/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.33/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_1730,c_7871]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_2,plain,
% 7.33/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.33/1.49      | ~ m1_subset_1(X3,X1)
% 7.33/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.33/1.49      | ~ v1_funct_1(X0)
% 7.33/1.49      | v1_xboole_0(X1)
% 7.33/1.49      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.33/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1162,plain,
% 7.33/1.49      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 7.33/1.49      | ~ m1_subset_1(X1_52,X0_53)
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.33/1.49      | ~ v1_funct_1(X0_52)
% 7.33/1.49      | v1_xboole_0(X0_53)
% 7.33/1.49      | k3_funct_2(X0_53,X1_53,X0_52,X1_52) = k1_funct_1(X0_52,X1_52) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1719,plain,
% 7.33/1.49      ( k3_funct_2(X0_53,X1_53,X0_52,X1_52) = k1_funct_1(X0_52,X1_52)
% 7.33/1.49      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 7.33/1.49      | m1_subset_1(X1_52,X0_53) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1162]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_2762,plain,
% 7.33/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
% 7.33/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.33/1.49      | v1_funct_1(sK3) != iProver_top
% 7.33/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_1742,c_1719]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3092,plain,
% 7.33/1.49      ( m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.33/1.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
% 7.33/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_2762,c_38,c_39]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3093,plain,
% 7.33/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = k1_funct_1(sK3,X0_52)
% 7.33/1.49      | m1_subset_1(X0_52,u1_struct_0(sK2)) != iProver_top
% 7.33/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.33/1.49      inference(renaming,[status(thm)],[c_3092]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5619,plain,
% 7.33/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52))
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_5612,c_3093]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5772,plain,
% 7.33/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.33/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.33/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_1730,c_5619]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_23,negated_conjecture,
% 7.33/1.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
% 7.33/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_44,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1166,plain,( X0_52 = X0_52 ),theory(equality) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1183,plain,
% 7.33/1.49      ( sK3 = sK3 ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1166]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1174,plain,
% 7.33/1.49      ( ~ r2_funct_2(X0_53,X1_53,X0_52,X1_52)
% 7.33/1.49      | r2_funct_2(X0_53,X1_53,X2_52,X3_52)
% 7.33/1.49      | X2_52 != X0_52
% 7.33/1.49      | X3_52 != X1_52 ),
% 7.33/1.49      theory(equality) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1903,plain,
% 7.33/1.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,X1_52)
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)
% 7.33/1.49      | k4_tmap_1(sK1,sK2) != X0_52
% 7.33/1.49      | sK3 != X1_52 ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1174]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1904,plain,
% 7.33/1.49      ( k4_tmap_1(sK1,sK2) != X0_52
% 7.33/1.49      | sK3 != X1_52
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,X1_52) != iProver_top
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1903]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1906,plain,
% 7.33/1.49      ( k4_tmap_1(sK1,sK2) != sK3
% 7.33/1.49      | sK3 != sK3
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) = iProver_top
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) != iProver_top ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1904]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_15,plain,
% 7.33/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.33/1.49      | v2_struct_0(X1)
% 7.33/1.49      | ~ l1_pre_topc(X1)
% 7.33/1.49      | ~ v2_pre_topc(X1)
% 7.33/1.49      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 7.33/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1149,plain,
% 7.33/1.49      ( ~ m1_pre_topc(X0_51,X1_51)
% 7.33/1.49      | v2_struct_0(X1_51)
% 7.33/1.49      | ~ l1_pre_topc(X1_51)
% 7.33/1.49      | ~ v2_pre_topc(X1_51)
% 7.33/1.49      | v1_funct_1(k4_tmap_1(X1_51,X0_51)) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_15]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_2204,plain,
% 7.33/1.49      ( ~ m1_pre_topc(sK2,sK1)
% 7.33/1.49      | v2_struct_0(sK1)
% 7.33/1.49      | ~ l1_pre_topc(sK1)
% 7.33/1.49      | ~ v2_pre_topc(sK1)
% 7.33/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1149]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_2205,plain,
% 7.33/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_2204]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3,plain,
% 7.33/1.49      ( r2_funct_2(X0,X1,X2,X2)
% 7.33/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.33/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.33/1.49      | ~ v1_funct_1(X2) ),
% 7.33/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1161,plain,
% 7.33/1.49      ( r2_funct_2(X0_53,X1_53,X0_52,X0_52)
% 7.33/1.49      | ~ v1_funct_2(X0_52,X0_53,X1_53)
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.33/1.49      | ~ v1_funct_1(X0_52) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1720,plain,
% 7.33/1.49      ( r2_funct_2(X0_53,X1_53,X0_52,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1161]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_2727,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK3) = iProver_top
% 7.33/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_1742,c_1720]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_2037,plain,
% 7.33/1.49      ( ~ r2_funct_2(X0_53,X1_53,X0_52,k4_tmap_1(sK1,sK2))
% 7.33/1.49      | ~ v1_funct_2(X0_52,X0_53,X1_53)
% 7.33/1.49      | ~ v1_funct_2(k4_tmap_1(sK1,sK2),X0_53,X1_53)
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.33/1.49      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.33/1.49      | ~ v1_funct_1(X0_52)
% 7.33/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.33/1.49      | k4_tmap_1(sK1,sK2) = X0_52 ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1160]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3261,plain,
% 7.33/1.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,k4_tmap_1(sK1,sK2))
% 7.33/1.49      | ~ v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1))
% 7.33/1.49      | ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.33/1.49      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.33/1.49      | ~ v1_funct_1(X0_52)
% 7.33/1.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 7.33/1.49      | k4_tmap_1(sK1,sK2) = X0_52 ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_2037]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3263,plain,
% 7.33/1.49      ( k4_tmap_1(sK1,sK2) = X0_52
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),X0_52,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_3261]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3265,plain,
% 7.33/1.49      ( k4_tmap_1(sK1,sK2) = sK3
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
% 7.33/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.33/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_3263]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_14,plain,
% 7.33/1.49      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 7.33/1.49      | ~ m1_pre_topc(X1,X0)
% 7.33/1.49      | v2_struct_0(X0)
% 7.33/1.49      | ~ l1_pre_topc(X0)
% 7.33/1.49      | ~ v2_pre_topc(X0) ),
% 7.33/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1150,plain,
% 7.33/1.49      ( v1_funct_2(k4_tmap_1(X0_51,X1_51),u1_struct_0(X1_51),u1_struct_0(X0_51))
% 7.33/1.49      | ~ m1_pre_topc(X1_51,X0_51)
% 7.33/1.49      | v2_struct_0(X0_51)
% 7.33/1.49      | ~ l1_pre_topc(X0_51)
% 7.33/1.49      | ~ v2_pre_topc(X0_51) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3479,plain,
% 7.33/1.49      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.33/1.49      | ~ m1_pre_topc(sK2,sK1)
% 7.33/1.49      | v2_struct_0(sK1)
% 7.33/1.49      | ~ l1_pre_topc(sK1)
% 7.33/1.49      | ~ v2_pre_topc(sK1) ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1150]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_3480,plain,
% 7.33/1.49      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_3479]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5302,plain,
% 7.33/1.49      ( ~ m1_pre_topc(sK2,sK1)
% 7.33/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 7.33/1.49      | v2_struct_0(sK1)
% 7.33/1.49      | ~ l1_pre_topc(sK1)
% 7.33/1.49      | ~ v2_pre_topc(sK1) ),
% 7.33/1.49      inference(instantiation,[status(thm)],[c_1151]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5303,plain,
% 7.33/1.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_5302]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5779,plain,
% 7.33/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 7.33/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_5772,c_33,c_34,c_35,c_37,c_38,c_39,c_40,c_44,c_1183,
% 7.33/1.49                 c_1906,c_2205,c_2727,c_3265,c_3480,c_5303]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_0,plain,
% 7.33/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.33/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1164,plain,
% 7.33/1.49      ( ~ r2_hidden(X0_52,X0_53) | ~ v1_xboole_0(X0_53) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1717,plain,
% 7.33/1.49      ( r2_hidden(X0_52,X0_53) != iProver_top
% 7.33/1.49      | v1_xboole_0(X0_53) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1164]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_6161,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_6158,c_1717]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_6191,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.33/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.33/1.49      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_1730,c_6161]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_6467,plain,
% 7.33/1.49      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_6191,c_33,c_34,c_35,c_37,c_38,c_39,c_40,c_44,c_1183,
% 7.33/1.49                 c_1906,c_2205,c_2727,c_3265,c_3480,c_5303]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_6471,plain,
% 7.33/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_5779,c_6467]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_24,negated_conjecture,
% 7.33/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.33/1.49      | ~ r2_hidden(X0,u1_struct_0(sK2))
% 7.33/1.49      | k1_funct_1(sK3,X0) = X0 ),
% 7.33/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1140,negated_conjecture,
% 7.33/1.49      ( ~ m1_subset_1(X0_52,u1_struct_0(sK1))
% 7.33/1.49      | ~ r2_hidden(X0_52,u1_struct_0(sK2))
% 7.33/1.49      | k1_funct_1(sK3,X0_52) = X0_52 ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_24]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1741,plain,
% 7.33/1.49      ( k1_funct_1(sK3,X0_52) = X0_52
% 7.33/1.49      | m1_subset_1(X0_52,u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | r2_hidden(X0_52,u1_struct_0(sK2)) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1140]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_6477,plain,
% 7.33/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_6474,c_1741]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1,plain,
% 7.33/1.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.33/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1163,plain,
% 7.33/1.49      ( ~ m1_subset_1(X0_52,X0_53)
% 7.33/1.49      | r2_hidden(X0_52,X0_53)
% 7.33/1.49      | v1_xboole_0(X0_53) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1718,plain,
% 7.33/1.49      ( m1_subset_1(X0_52,X0_53) != iProver_top
% 7.33/1.49      | r2_hidden(X0_52,X0_53) = iProver_top
% 7.33/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1163]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_5618,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0_52),u1_struct_0(sK2)) = iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_5612,c_1718]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_6700,plain,
% 7.33/1.49      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_6477,c_33,c_34,c_35,c_37,c_38,c_39,c_40,c_44,c_1183,
% 7.33/1.49                 c_1906,c_2205,c_2727,c_3265,c_3480,c_5303,c_5618,c_6191]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_6701,plain,
% 7.33/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0_52)) = sK0(sK1,sK2,sK2,sK3,X0_52)
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top ),
% 7.33/1.49      inference(renaming,[status(thm)],[c_6700]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_6705,plain,
% 7.33/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.33/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_1730,c_6701]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_6712,plain,
% 7.33/1.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 7.33/1.49      inference(global_propositional_subsumption,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_6705,c_33,c_34,c_35,c_37,c_38,c_39,c_40,c_44,c_1183,
% 7.33/1.49                 c_1906,c_2205,c_2727,c_3265,c_3480,c_5303]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7078,plain,
% 7.33/1.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 7.33/1.49      inference(light_normalisation,[status(thm)],[c_6471,c_6471,c_6712]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_17,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 7.33/1.49      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 7.33/1.49      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 7.33/1.49      | ~ m1_pre_topc(X0,X2)
% 7.33/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.33/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 7.33/1.49      | v2_struct_0(X1)
% 7.33/1.49      | v2_struct_0(X2)
% 7.33/1.49      | v2_struct_0(X0)
% 7.33/1.49      | ~ l1_pre_topc(X1)
% 7.33/1.49      | ~ l1_pre_topc(X2)
% 7.33/1.49      | ~ v2_pre_topc(X1)
% 7.33/1.49      | ~ v2_pre_topc(X2)
% 7.33/1.49      | ~ v1_funct_1(X3)
% 7.33/1.49      | ~ v1_funct_1(X4)
% 7.33/1.49      | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK0(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK0(X1,X2,X0,X3,X4)) ),
% 7.33/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1147,plain,
% 7.33/1.49      ( r2_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),k2_tmap_1(X2_51,X1_51,X0_52,X0_51),X1_52)
% 7.33/1.49      | ~ v1_funct_2(X1_52,u1_struct_0(X0_51),u1_struct_0(X1_51))
% 7.33/1.49      | ~ v1_funct_2(X0_52,u1_struct_0(X2_51),u1_struct_0(X1_51))
% 7.33/1.49      | ~ m1_pre_topc(X0_51,X2_51)
% 7.33/1.49      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51))))
% 7.33/1.49      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51))))
% 7.33/1.49      | v2_struct_0(X1_51)
% 7.33/1.49      | v2_struct_0(X0_51)
% 7.33/1.49      | v2_struct_0(X2_51)
% 7.33/1.49      | ~ l1_pre_topc(X1_51)
% 7.33/1.49      | ~ l1_pre_topc(X2_51)
% 7.33/1.49      | ~ v2_pre_topc(X1_51)
% 7.33/1.49      | ~ v2_pre_topc(X2_51)
% 7.33/1.49      | ~ v1_funct_1(X0_52)
% 7.33/1.49      | ~ v1_funct_1(X1_52)
% 7.33/1.49      | k3_funct_2(u1_struct_0(X2_51),u1_struct_0(X1_51),X0_52,sK0(X1_51,X2_51,X0_51,X0_52,X1_52)) != k1_funct_1(X1_52,sK0(X1_51,X2_51,X0_51,X0_52,X1_52)) ),
% 7.33/1.49      inference(subtyping,[status(esa)],[c_17]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_1734,plain,
% 7.33/1.49      ( k3_funct_2(u1_struct_0(X0_51),u1_struct_0(X1_51),X0_52,sK0(X1_51,X0_51,X2_51,X0_52,X1_52)) != k1_funct_1(X1_52,sK0(X1_51,X0_51,X2_51,X0_52,X1_52))
% 7.33/1.49      | r2_funct_2(u1_struct_0(X2_51),u1_struct_0(X1_51),k2_tmap_1(X0_51,X1_51,X0_52,X2_51),X1_52) = iProver_top
% 7.33/1.49      | v1_funct_2(X1_52,u1_struct_0(X2_51),u1_struct_0(X1_51)) != iProver_top
% 7.33/1.49      | v1_funct_2(X0_52,u1_struct_0(X0_51),u1_struct_0(X1_51)) != iProver_top
% 7.33/1.49      | m1_pre_topc(X2_51,X0_51) != iProver_top
% 7.33/1.49      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_51),u1_struct_0(X1_51)))) != iProver_top
% 7.33/1.49      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_51),u1_struct_0(X1_51)))) != iProver_top
% 7.33/1.49      | v2_struct_0(X2_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X1_51) = iProver_top
% 7.33/1.49      | v2_struct_0(X0_51) = iProver_top
% 7.33/1.49      | l1_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | l1_pre_topc(X0_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X1_51) != iProver_top
% 7.33/1.49      | v2_pre_topc(X0_51) != iProver_top
% 7.33/1.49      | v1_funct_1(X0_52) != iProver_top
% 7.33/1.49      | v1_funct_1(X1_52) != iProver_top ),
% 7.33/1.49      inference(predicate_to_equality,[status(thm)],[c_1147]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7079,plain,
% 7.33/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),k4_tmap_1(sK1,sK2)) = iProver_top
% 7.33/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.33/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | v2_struct_0(sK2) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.33/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.33/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.33/1.49      inference(superposition,[status(thm)],[c_7078,c_1734]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(c_7080,plain,
% 7.33/1.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 7.33/1.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 7.33/1.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.33/1.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.33/1.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 7.33/1.49      | v2_struct_0(sK1) = iProver_top
% 7.33/1.49      | v2_struct_0(sK2) = iProver_top
% 7.33/1.49      | l1_pre_topc(sK1) != iProver_top
% 7.33/1.49      | l1_pre_topc(sK2) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK1) != iProver_top
% 7.33/1.49      | v2_pre_topc(sK2) != iProver_top
% 7.33/1.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 7.33/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.33/1.49      inference(light_normalisation,[status(thm)],[c_7079,c_5263]) ).
% 7.33/1.49  
% 7.33/1.49  cnf(contradiction,plain,
% 7.33/1.49      ( $false ),
% 7.33/1.49      inference(minisat,
% 7.33/1.49                [status(thm)],
% 7.33/1.49                [c_7875,c_7080,c_5303,c_3480,c_3265,c_2727,c_2542,c_2205,
% 7.33/1.49                 c_2160,c_1919,c_1906,c_1183,c_44,c_40,c_39,c_38,c_37,
% 7.33/1.49                 c_36,c_35,c_34,c_33]) ).
% 7.33/1.49  
% 7.33/1.49  
% 7.33/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.33/1.49  
% 7.33/1.49  ------                               Statistics
% 7.33/1.49  
% 7.33/1.49  ------ General
% 7.33/1.49  
% 7.33/1.49  abstr_ref_over_cycles:                  0
% 7.33/1.49  abstr_ref_under_cycles:                 0
% 7.33/1.49  gc_basic_clause_elim:                   0
% 7.33/1.49  forced_gc_time:                         0
% 7.33/1.49  parsing_time:                           0.013
% 7.33/1.49  unif_index_cands_time:                  0.
% 7.33/1.49  unif_index_add_time:                    0.
% 7.33/1.49  orderings_time:                         0.
% 7.33/1.49  out_proof_time:                         0.023
% 7.33/1.49  total_time:                             0.6
% 7.33/1.49  num_of_symbols:                         58
% 7.33/1.49  num_of_terms:                           17021
% 7.33/1.49  
% 7.33/1.49  ------ Preprocessing
% 7.33/1.49  
% 7.33/1.49  num_of_splits:                          0
% 7.33/1.49  num_of_split_atoms:                     0
% 7.33/1.49  num_of_reused_defs:                     0
% 7.33/1.49  num_eq_ax_congr_red:                    56
% 7.33/1.49  num_of_sem_filtered_clauses:            1
% 7.33/1.49  num_of_subtypes:                        4
% 7.33/1.49  monotx_restored_types:                  1
% 7.33/1.49  sat_num_of_epr_types:                   0
% 7.33/1.49  sat_num_of_non_cyclic_types:            0
% 7.33/1.49  sat_guarded_non_collapsed_types:        1
% 7.33/1.49  num_pure_diseq_elim:                    0
% 7.33/1.49  simp_replaced_by:                       0
% 7.33/1.49  res_preprocessed:                       118
% 7.33/1.49  prep_upred:                             0
% 7.33/1.49  prep_unflattend:                        35
% 7.33/1.49  smt_new_axioms:                         0
% 7.33/1.49  pred_elim_cands:                        10
% 7.33/1.49  pred_elim:                              0
% 7.33/1.49  pred_elim_cl:                           0
% 7.33/1.49  pred_elim_cycles:                       3
% 7.33/1.49  merged_defs:                            0
% 7.33/1.49  merged_defs_ncl:                        0
% 7.33/1.49  bin_hyper_res:                          0
% 7.33/1.49  prep_cycles:                            3
% 7.33/1.49  pred_elim_time:                         0.027
% 7.33/1.49  splitting_time:                         0.
% 7.33/1.49  sem_filter_time:                        0.
% 7.33/1.49  monotx_time:                            0.001
% 7.33/1.49  subtype_inf_time:                       0.002
% 7.33/1.49  
% 7.33/1.49  ------ Problem properties
% 7.33/1.49  
% 7.33/1.49  clauses:                                33
% 7.33/1.49  conjectures:                            10
% 7.33/1.49  epr:                                    12
% 7.33/1.49  horn:                                   17
% 7.33/1.49  ground:                                 9
% 7.33/1.49  unary:                                  9
% 7.33/1.49  binary:                                 2
% 7.33/1.49  lits:                                   198
% 7.33/1.49  lits_eq:                                7
% 7.33/1.49  fd_pure:                                0
% 7.33/1.49  fd_pseudo:                              0
% 7.33/1.49  fd_cond:                                0
% 7.33/1.49  fd_pseudo_cond:                         1
% 7.33/1.49  ac_symbols:                             0
% 7.33/1.49  
% 7.33/1.49  ------ Propositional Solver
% 7.33/1.49  
% 7.33/1.49  prop_solver_calls:                      26
% 7.33/1.49  prop_fast_solver_calls:                 2799
% 7.33/1.49  smt_solver_calls:                       0
% 7.33/1.49  smt_fast_solver_calls:                  0
% 7.33/1.49  prop_num_of_clauses:                    3754
% 7.33/1.49  prop_preprocess_simplified:             8624
% 7.33/1.49  prop_fo_subsumed:                       249
% 7.33/1.49  prop_solver_time:                       0.
% 7.33/1.49  smt_solver_time:                        0.
% 7.33/1.49  smt_fast_solver_time:                   0.
% 7.33/1.49  prop_fast_solver_time:                  0.
% 7.33/1.49  prop_unsat_core_time:                   0.
% 7.33/1.49  
% 7.33/1.49  ------ QBF
% 7.33/1.49  
% 7.33/1.49  qbf_q_res:                              0
% 7.33/1.49  qbf_num_tautologies:                    0
% 7.33/1.49  qbf_prep_cycles:                        0
% 7.33/1.49  
% 7.33/1.49  ------ BMC1
% 7.33/1.49  
% 7.33/1.49  bmc1_current_bound:                     -1
% 7.33/1.49  bmc1_last_solved_bound:                 -1
% 7.33/1.49  bmc1_unsat_core_size:                   -1
% 7.33/1.49  bmc1_unsat_core_parents_size:           -1
% 7.33/1.49  bmc1_merge_next_fun:                    0
% 7.33/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.33/1.49  
% 7.33/1.49  ------ Instantiation
% 7.33/1.49  
% 7.33/1.49  inst_num_of_clauses:                    907
% 7.33/1.49  inst_num_in_passive:                    127
% 7.33/1.49  inst_num_in_active:                     429
% 7.33/1.49  inst_num_in_unprocessed:                351
% 7.33/1.49  inst_num_of_loops:                      520
% 7.33/1.49  inst_num_of_learning_restarts:          0
% 7.33/1.49  inst_num_moves_active_passive:          89
% 7.33/1.49  inst_lit_activity:                      0
% 7.33/1.49  inst_lit_activity_moves:                1
% 7.33/1.49  inst_num_tautologies:                   0
% 7.33/1.49  inst_num_prop_implied:                  0
% 7.33/1.49  inst_num_existing_simplified:           0
% 7.33/1.49  inst_num_eq_res_simplified:             0
% 7.33/1.49  inst_num_child_elim:                    0
% 7.33/1.49  inst_num_of_dismatching_blockings:      113
% 7.33/1.49  inst_num_of_non_proper_insts:           802
% 7.33/1.49  inst_num_of_duplicates:                 0
% 7.33/1.49  inst_inst_num_from_inst_to_res:         0
% 7.33/1.49  inst_dismatching_checking_time:         0.
% 7.33/1.49  
% 7.33/1.49  ------ Resolution
% 7.33/1.49  
% 7.33/1.49  res_num_of_clauses:                     0
% 7.33/1.49  res_num_in_passive:                     0
% 7.33/1.49  res_num_in_active:                      0
% 7.33/1.49  res_num_of_loops:                       121
% 7.33/1.49  res_forward_subset_subsumed:            10
% 7.33/1.49  res_backward_subset_subsumed:           0
% 7.33/1.49  res_forward_subsumed:                   0
% 7.33/1.49  res_backward_subsumed:                  0
% 7.33/1.49  res_forward_subsumption_resolution:     0
% 7.33/1.49  res_backward_subsumption_resolution:    0
% 7.33/1.49  res_clause_to_clause_subsumption:       643
% 7.33/1.49  res_orphan_elimination:                 0
% 7.33/1.49  res_tautology_del:                      28
% 7.33/1.49  res_num_eq_res_simplified:              0
% 7.33/1.49  res_num_sel_changes:                    0
% 7.33/1.49  res_moves_from_active_to_pass:          0
% 7.33/1.49  
% 7.33/1.49  ------ Superposition
% 7.33/1.49  
% 7.33/1.49  sup_time_total:                         0.
% 7.33/1.49  sup_time_generating:                    0.
% 7.33/1.49  sup_time_sim_full:                      0.
% 7.33/1.49  sup_time_sim_immed:                     0.
% 7.33/1.49  
% 7.33/1.49  sup_num_of_clauses:                     131
% 7.33/1.49  sup_num_in_active:                      92
% 7.33/1.49  sup_num_in_passive:                     39
% 7.33/1.49  sup_num_of_loops:                       103
% 7.33/1.49  sup_fw_superposition:                   92
% 7.33/1.49  sup_bw_superposition:                   76
% 7.33/1.49  sup_immediate_simplified:               40
% 7.33/1.49  sup_given_eliminated:                   1
% 7.33/1.49  comparisons_done:                       0
% 7.33/1.49  comparisons_avoided:                    8
% 7.33/1.49  
% 7.33/1.49  ------ Simplifications
% 7.33/1.49  
% 7.33/1.49  
% 7.33/1.49  sim_fw_subset_subsumed:                 22
% 7.33/1.49  sim_bw_subset_subsumed:                 8
% 7.33/1.49  sim_fw_subsumed:                        12
% 7.33/1.49  sim_bw_subsumed:                        5
% 7.33/1.49  sim_fw_subsumption_res:                 0
% 7.33/1.49  sim_bw_subsumption_res:                 0
% 7.33/1.49  sim_tautology_del:                      11
% 7.33/1.49  sim_eq_tautology_del:                   2
% 7.33/1.49  sim_eq_res_simp:                        0
% 7.33/1.49  sim_fw_demodulated:                     5
% 7.33/1.49  sim_bw_demodulated:                     6
% 7.33/1.49  sim_light_normalised:                   22
% 7.33/1.49  sim_joinable_taut:                      0
% 7.33/1.49  sim_joinable_simp:                      0
% 7.33/1.49  sim_ac_normalised:                      0
% 7.33/1.49  sim_smt_subsumption:                    0
% 7.33/1.49  
%------------------------------------------------------------------------------
