%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:44 EST 2020

% Result     : Theorem 15.39s
% Output     : CNFRefutation 15.39s
% Verified   : 
% Statistics : Number of formulae       :  374 (17755 expanded)
%              Number of clauses        :  277 (5005 expanded)
%              Number of leaves         :   25 (5184 expanded)
%              Depth                    :   37
%              Number of atoms          : 2529 (166672 expanded)
%              Number of equality atoms : 1500 (24801 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal clause size      :   24 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k4_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,
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

fof(f61,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f54,f60,f59,f58])).

fof(f94,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f61])).

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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f88,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f89,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f92,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f93,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

fof(f90,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f91,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(cnf_transformation,[],[f36])).

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

fof(f84,plain,(
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

fof(f11,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f40])).

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

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

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
    inference(nnf_transformation,[],[f28])).

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

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f40])).

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

fof(f56,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
        & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f56])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f86,plain,(
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

fof(f95,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k4_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f57])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f66])).

fof(f96,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f57])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2876,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_18,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2872,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2863,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10,plain,
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

cnf(c_2880,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X4) != iProver_top
    | m1_pre_topc(X0,X4) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X4) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2867,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X2,X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3178,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_pre_topc(X0,X4) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X4) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2880,c_2867])).

cnf(c_6954,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK2,X0,sK3)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2863,c_3178])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_40,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_41,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7149,plain,
    ( l1_pre_topc(X1) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK2,X0,sK3)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6954,c_35,c_36,c_37,c_40,c_41])).

cnf(c_7150,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK2,X0,sK3)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7149])).

cnf(c_7161,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK2,X0,sK3)
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2872,c_7150])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_38,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_39,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2860,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2882,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3601,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_2882])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3714,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3715,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3714])).

cnf(c_3717,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3715])).

cnf(c_7190,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK2,X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7161,c_36,c_37,c_38,c_39,c_3601,c_3717])).

cnf(c_7191,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK2,X0,sK3)
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7190])).

cnf(c_7198,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK2,sK2,sK3)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2872,c_7191])).

cnf(c_9,plain,
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

cnf(c_2881,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5257,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k2_tmap_1(sK2,sK1,sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2863,c_2881])).

cnf(c_5465,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k2_tmap_1(sK2,sK1,sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5257,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_3601,c_3717])).

cnf(c_5466,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k2_tmap_1(sK2,sK1,sK3,X0)
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5465])).

cnf(c_5473,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2872,c_5466])).

cnf(c_3606,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3601])).

cnf(c_3716,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3714])).

cnf(c_3825,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3464,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3612,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k2_tmap_1(sK2,sK1,sK3,X0) ),
    inference(instantiation,[status(thm)],[c_3464])).

cnf(c_4423,plain,
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
    inference(instantiation,[status(thm)],[c_3612])).

cnf(c_5576,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5473,c_34,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_3606,c_3716,c_3825,c_4423])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f84])).

cnf(c_2868,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2)) = iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f75])).

cnf(c_2879,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | m1_pre_topc(X3,X4) != iProver_top
    | m1_pre_topc(X1,X4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X4) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X4) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | X3 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2884,plain,
    ( X0 = X1
    | r2_funct_2(X2,X3,X1,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) != iProver_top
    | v1_funct_2(X0,X2,X3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4736,plain,
    ( sK3 = X0
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2863,c_2884])).

cnf(c_4741,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | sK3 = X0
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4736,c_40,c_41])).

cnf(c_4742,plain,
    ( sK3 = X0
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4741])).

cnf(c_6262,plain,
    ( k3_tmap_1(X0,sK1,X1,sK2,X2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0,sK1,X1,sK2,X2)) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0,sK1,X1,sK2,X2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k3_tmap_1(X0,sK1,X1,sK2,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2879,c_4742])).

cnf(c_6692,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | v1_funct_2(k3_tmap_1(X0,sK1,X1,sK2,X2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0,sK1,X1,sK2,X2)) != iProver_top
    | k3_tmap_1(X0,sK1,X1,sK2,X2) = sK3
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k3_tmap_1(X0,sK1,X1,sK2,X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6262,c_35,c_36,c_37])).

cnf(c_6693,plain,
    ( k3_tmap_1(X0,sK1,X1,sK2,X2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0,sK1,X1,sK2,X2)) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0,sK1,X1,sK2,X2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k3_tmap_1(X0,sK1,X1,sK2,X2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6692])).

cnf(c_6708,plain,
    ( k3_tmap_1(X0,sK1,sK2,sK2,sK3) = sK3
    | v1_funct_2(k3_tmap_1(X0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X0,sK1,sK2,sK2,sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2868,c_6693])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_3484,plain,
    ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,sK3),u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(sK3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3627,plain,
    ( v1_funct_2(k3_tmap_1(X0,sK1,sK2,X1,sK3),u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3484])).

cnf(c_5984,plain,
    ( v1_funct_2(k3_tmap_1(X0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3627])).

cnf(c_5989,plain,
    ( v1_funct_2(k3_tmap_1(X0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5984])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f73])).

cnf(c_3454,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3607,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK2,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3454])).

cnf(c_6662,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X0,sK1,sK2,sK2,sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3607])).

cnf(c_6663,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X0,sK1,sK2,sK2,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6662])).

cnf(c_6784,plain,
    ( v2_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | k3_tmap_1(X0,sK1,sK2,sK2,sK3) = sK3
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6708,c_35,c_36,c_37,c_38,c_40,c_41,c_42,c_5989,c_6663])).

cnf(c_6785,plain,
    ( k3_tmap_1(X0,sK1,sK2,sK2,sK3) = sK3
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6784])).

cnf(c_6795,plain,
    ( k3_tmap_1(sK2,sK1,sK2,sK2,sK3) = sK3
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2872,c_6785])).

cnf(c_6850,plain,
    ( k3_tmap_1(sK2,sK1,sK2,sK2,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6795,c_36,c_37,c_38,c_39,c_3601,c_3717])).

cnf(c_7199,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7198,c_5576,c_6850])).

cnf(c_7487,plain,
    ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7199,c_37,c_3601])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f82])).

cnf(c_2870,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4) = iProver_top
    | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) != iProver_top
    | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7491,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7487,c_2870])).

cnf(c_3830,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3825])).

cnf(c_8422,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(sK2)) = iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7491,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_3601,c_3717,c_3830])).

cnf(c_8423,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8422])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2873,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2887,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4026,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
    | r2_hidden(X2,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2873,c_2887])).

cnf(c_8433,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8423,c_4026])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2888,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9250,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8433,c_2888])).

cnf(c_9639,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9250,c_4026])).

cnf(c_33923,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(X2)) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9639,c_2882])).

cnf(c_33926,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_33923])).

cnf(c_8,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_93,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_95,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_6,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_97,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_99,plain,
    ( l1_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_33956,plain,
    ( v1_funct_1(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33926,c_35,c_37,c_95,c_99])).

cnf(c_33957,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_33956])).

cnf(c_24,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,u1_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2866,plain,
    ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_33972,plain,
    ( k1_funct_1(k4_tmap_1(X0,X1),sK0(sK1,sK2,sK2,sK3,X2)) = sK0(sK1,sK2,sK2,sK3,X2)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X2) = iProver_top
    | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X2),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33957,c_2866])).

cnf(c_34797,plain,
    ( k1_funct_1(k4_tmap_1(X0,sK2),sK0(sK1,sK2,sK2,sK3,X1)) = sK0(sK1,sK2,sK2,sK3,X1)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X1) = iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8423,c_33972])).

cnf(c_9252,plain,
    ( k1_funct_1(k4_tmap_1(X0,X1),sK0(sK1,sK2,sK2,sK3,X2)) = sK0(sK1,sK2,sK2,sK3,X2)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X2) = iProver_top
    | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X2),u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8433,c_2866])).

cnf(c_33054,plain,
    ( k1_funct_1(k4_tmap_1(X0,sK2),sK0(sK1,sK2,sK2,sK3,X1)) = sK0(sK1,sK2,sK2,sK3,X1)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X1) = iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8423,c_9252])).

cnf(c_37092,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | k1_funct_1(k4_tmap_1(X0,sK2),sK0(sK1,sK2,sK2,sK3,X1)) = sK0(sK1,sK2,sK2,sK3,X1)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X1) = iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34797,c_38,c_33054])).

cnf(c_37093,plain,
    ( k1_funct_1(k4_tmap_1(X0,sK2),sK0(sK1,sK2,sK2,sK3,X1)) = sK0(sK1,sK2,sK2,sK3,X1)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X1) = iProver_top
    | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_37092])).

cnf(c_37108,plain,
    ( k1_funct_1(k4_tmap_1(X0,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2876,c_37093])).

cnf(c_37210,plain,
    ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37108])).

cnf(c_26,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,u1_struct_0(sK2))
    | k1_funct_1(sK3,X0) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2864,plain,
    ( k1_funct_1(sK3,X0) = X0
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9253,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0)) = sK0(sK1,sK2,sK2,sK3,X0)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8433,c_2864])).

cnf(c_9644,plain,
    ( v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
    | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0)) = sK0(sK1,sK2,sK2,sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9253,c_37,c_39,c_8423])).

cnf(c_9645,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0)) = sK0(sK1,sK2,sK2,sK3,X0)
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9644])).

cnf(c_9656,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2876,c_9645])).

cnf(c_15,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_4718,plain,
    ( v1_funct_2(k4_tmap_1(X0,sK2),u1_struct_0(sK2),u1_struct_0(X0))
    | ~ m1_pre_topc(sK2,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_4723,plain,
    ( v1_funct_2(k4_tmap_1(X0,sK2),u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4718])).

cnf(c_4725,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4723])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k4_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_7476,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v1_funct_1(k4_tmap_1(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_7477,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(X0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7476])).

cnf(c_7479,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7477])).

cnf(c_9812,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9656,c_35,c_36,c_37,c_39,c_4725,c_7479])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_2869,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4) = iProver_top
    | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2886,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6257,plain,
    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,X4),X5) = k1_funct_1(k3_tmap_1(X2,X1,X3,X0,X4),X5)
    | v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2,X1,X3,X0,X4),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X3,X2) != iProver_top
    | m1_subset_1(X5,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(k3_tmap_1(X2,X1,X3,X0,X4)) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2879,c_2886])).

cnf(c_2877,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | m1_pre_topc(X3,X4) != iProver_top
    | m1_pre_topc(X1,X4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X4) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X4) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2878,plain,
    ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2)) = iProver_top
    | m1_pre_topc(X4,X3) != iProver_top
    | m1_pre_topc(X1,X3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X3) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_15956,plain,
    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,X4),X5) = k1_funct_1(k3_tmap_1(X2,X1,X3,X0,X4),X5)
    | v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X3,X2) != iProver_top
    | m1_subset_1(X5,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6257,c_2877,c_2878])).

cnf(c_15962,plain,
    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK2,X0,sK3),X2) = k1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK3),X2)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2863,c_15956])).

cnf(c_16641,plain,
    ( l1_pre_topc(X1) != iProver_top
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK2,X0,sK3),X2) = k1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK3),X2)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15962,c_35,c_36,c_37,c_40,c_41])).

cnf(c_16642,plain,
    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK2,X0,sK3),X2) = k1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK3),X2)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_16641])).

cnf(c_16655,plain,
    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK2,X0,sK3),sK0(X2,X0,X3,X4,X5)) = k1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK3),sK0(X2,X0,X3,X4,X5))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,X4,X3),X5) = iProver_top
    | v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2869,c_16642])).

cnf(c_96,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_100,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_383,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_6,c_8])).

cnf(c_384,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_17182,plain,
    ( v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)) != iProver_top
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,X4,X3),X5) = iProver_top
    | k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK2,X0,sK3),sK0(X2,X0,X3,X4,X5)) = k1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK3),sK0(X2,X0,X3,X4,X5))
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16655,c_96,c_100,c_384])).

cnf(c_17183,plain,
    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK2,X0,sK3),sK0(X2,X0,X3,X4,X5)) = k1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK3),sK0(X2,X0,X3,X4,X5))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,X4,X3),X5) = iProver_top
    | v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)) != iProver_top
    | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(renaming,[status(thm)],[c_17182])).

cnf(c_17208,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0,sK2,X1,X2,X3)) = k1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0,sK2,X1,X2,X3))
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK2,X0,X2,X1),X3) = iProver_top
    | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_17183])).

cnf(c_6796,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_6785])).

cnf(c_5991,plain,
    ( v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5989])).

cnf(c_6665,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6663])).

cnf(c_6710,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
    | v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6708])).

cnf(c_6816,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6796,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_5991,c_6665,c_6710])).

cnf(c_17227,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0,sK2,X1,X2,X3)) = k1_funct_1(sK3,sK0(X0,sK2,X1,X2,X3))
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK2,X0,X2,X1),X3) = iProver_top
    | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17208,c_6816])).

cnf(c_5113,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k1_funct_1(sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2863,c_2886])).

cnf(c_5455,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k1_funct_1(sK3,X0)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5113,c_40,c_41])).

cnf(c_5456,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5455])).

cnf(c_6024,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0,sK2,X1,X2,X3)) = k1_funct_1(sK3,sK0(X0,sK2,X1,X2,X3))
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK2,X0,X2,X1),X3) = iProver_top
    | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2869,c_5456])).

cnf(c_6713,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK2,X0,X2,X1),X3) = iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0,sK2,X1,X2,X3)) = k1_funct_1(sK3,sK0(X0,sK2,X1,X2,X3))
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6024,c_36,c_37,c_38,c_39,c_3601,c_3717])).

cnf(c_6714,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0,sK2,X1,X2,X3)) = k1_funct_1(sK3,sK0(X0,sK2,X1,X2,X3))
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK2,X0,X2,X1),X3) = iProver_top
    | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6713])).

cnf(c_14155,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_14156,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14155])).

cnf(c_17387,plain,
    ( v2_pre_topc(X0) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK2,X0,X2,X1),X3) = iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0,sK2,X1,X2,X3)) = k1_funct_1(sK3,sK0(X0,sK2,X1,X2,X3))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17227,c_37,c_38,c_3601,c_6714,c_14156])).

cnf(c_17388,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0,sK2,X1,X2,X3)) = k1_funct_1(sK3,sK0(X0,sK2,X1,X2,X3))
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK2,X0,X2,X1),X3) = iProver_top
    | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(renaming,[status(thm)],[c_17387])).

cnf(c_6953,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,k4_tmap_1(X1,X0))
    | v1_funct_2(k4_tmap_1(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | v1_funct_1(k4_tmap_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2876,c_3178])).

cnf(c_69,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(k4_tmap_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9821,plain,
    ( v2_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v1_funct_2(k4_tmap_1(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,k4_tmap_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6953,c_69])).

cnf(c_9822,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,k4_tmap_1(X1,X0))
    | v1_funct_2(k4_tmap_1(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(renaming,[status(thm)],[c_9821])).

cnf(c_2875,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9838,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,k4_tmap_1(X1,X0))
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9822,c_2875])).

cnf(c_9843,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK2,X0,k4_tmap_1(sK1,sK2))
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_9838])).

cnf(c_9997,plain,
    ( v2_pre_topc(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK2,X0,k4_tmap_1(sK1,sK2))
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9843,c_35,c_36,c_37])).

cnf(c_9998,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK2,X0,k4_tmap_1(sK1,sK2))
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9997])).

cnf(c_10007,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK2,X0,k4_tmap_1(sK1,sK2))
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2872,c_9998])).

cnf(c_10218,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK2,X0,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10007,c_36,c_37,c_38,c_39,c_3601,c_3717])).

cnf(c_10219,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK2,X0,k4_tmap_1(sK1,sK2))
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_10218])).

cnf(c_10226,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK2,sK2,k4_tmap_1(sK1,sK2))
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2872,c_10219])).

cnf(c_5256,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k2_tmap_1(X0,X1,k4_tmap_1(X1,X0),X2)
    | v1_funct_2(k4_tmap_1(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2876,c_2881])).

cnf(c_7305,plain,
    ( l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v1_funct_2(k4_tmap_1(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k2_tmap_1(X0,X1,k4_tmap_1(X1,X0),X2)
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5256,c_69,c_96,c_100])).

cnf(c_7306,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k2_tmap_1(X0,X1,k4_tmap_1(X1,X0),X2)
    | v1_funct_2(k4_tmap_1(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7305])).

cnf(c_7319,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k2_tmap_1(X0,X1,k4_tmap_1(X1,X0),X2)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7306,c_2875])).

cnf(c_7324,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),X0)
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_7319])).

cnf(c_7431,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),X0)
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7324,c_35,c_36,c_37,c_38])).

cnf(c_7439,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2872,c_7431])).

cnf(c_7442,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7439,c_37,c_3601])).

cnf(c_10227,plain,
    ( k3_tmap_1(sK2,sK1,sK2,sK2,k4_tmap_1(sK1,sK2)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10226,c_7442])).

cnf(c_10621,plain,
    ( k3_tmap_1(sK2,sK1,sK2,sK2,k4_tmap_1(sK1,sK2)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10227,c_37,c_3601])).

cnf(c_10624,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10621,c_2879])).

cnf(c_10008,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(sK1,sK1,sK2,X0,k4_tmap_1(sK1,sK2))
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_9998])).

cnf(c_10036,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(sK1,sK1,sK2,X0,k4_tmap_1(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10008,c_35,c_36,c_37])).

cnf(c_10037,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(sK1,sK1,sK2,X0,k4_tmap_1(sK1,sK2))
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_10036])).

cnf(c_10044,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k3_tmap_1(sK1,sK1,sK2,sK2,k4_tmap_1(sK1,sK2))
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2872,c_10037])).

cnf(c_10045,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,k4_tmap_1(sK1,sK2)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10044,c_7442])).

cnf(c_10355,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,k4_tmap_1(sK1,sK2)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10045,c_37,c_3601])).

cnf(c_10358,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10355,c_2879])).

cnf(c_12623,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10358,c_35,c_36,c_37,c_39,c_4725,c_7479])).

cnf(c_13419,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_13420,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13419])).

cnf(c_20792,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10624,c_35,c_36,c_37,c_39,c_4725,c_7479,c_10358,c_13420])).

cnf(c_20807,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),X0) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20792,c_2884])).

cnf(c_5319,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X3,X2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(k3_tmap_1(X2,X0,X1,X3,k4_tmap_1(X0,X1))) = iProver_top
    | v1_funct_1(k4_tmap_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2876,c_2877])).

cnf(c_72,plain,
    ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9356,plain,
    ( m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X3,X2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(k3_tmap_1(X2,X0,X1,X3,k4_tmap_1(X0,X1))) = iProver_top
    | v1_funct_1(k4_tmap_1(X0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5319,c_72])).

cnf(c_9357,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X3) != iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X3) != iProver_top
    | v1_funct_1(k3_tmap_1(X3,X1,X0,X2,k4_tmap_1(X1,X0))) = iProver_top
    | v1_funct_1(k4_tmap_1(X1,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9356])).

cnf(c_9362,plain,
    ( v1_funct_1(k3_tmap_1(X3,X1,X0,X2,k4_tmap_1(X1,X0))) = iProver_top
    | v2_pre_topc(X3) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X3) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | m1_pre_topc(X0,X3) != iProver_top
    | m1_pre_topc(X2,X3) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9357,c_69])).

cnf(c_9363,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | m1_pre_topc(X3,X2) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X2) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X2) != iProver_top
    | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,k4_tmap_1(X1,X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_9362])).

cnf(c_10365,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10355,c_9363])).

cnf(c_10359,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10355,c_2878])).

cnf(c_11507,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10359,c_35,c_36,c_37,c_39,c_4725,c_7479])).

cnf(c_22199,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),X0) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20807,c_35,c_36,c_37,c_39,c_4725,c_7479,c_10359,c_10365,c_13420])).

cnf(c_22200,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),X0) != iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_22199])).

cnf(c_22214,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0))
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17388,c_22200])).

cnf(c_22627,plain,
    ( v1_funct_1(X0) != iProver_top
    | k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0))
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22214,c_35,c_36,c_37,c_38,c_39,c_3601,c_3830,c_4725,c_7479,c_13420])).

cnf(c_22628,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0))
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_22627])).

cnf(c_22639,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2)))
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2876,c_22628])).

cnf(c_10360,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10355,c_2868])).

cnf(c_10626,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10621,c_2868])).

cnf(c_17935,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10360,c_35,c_36,c_37,c_38,c_39,c_4725,c_7479,c_13420])).

cnf(c_5014,plain,
    ( k4_tmap_1(X0,X1) = X2
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k4_tmap_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2876,c_2884])).

cnf(c_8081,plain,
    ( v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) != iProver_top
    | k4_tmap_1(X0,X1) = X2
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k4_tmap_1(X0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5014,c_72])).

cnf(c_8082,plain,
    ( k4_tmap_1(X0,X1) = X2
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k4_tmap_1(X0,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8081])).

cnf(c_2874,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(k4_tmap_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8097,plain,
    ( k4_tmap_1(X0,X1) = X2
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8082,c_2874])).

cnf(c_17940,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
    | v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17935,c_8097])).

cnf(c_23727,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22639,c_35,c_36,c_37,c_39,c_4725,c_7479,c_10358,c_10359,c_10365,c_13420,c_17940])).

cnf(c_20811,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20792,c_4742])).

cnf(c_12639,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12623,c_4742])).

cnf(c_10364,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,k4_tmap_1(sK1,sK2)) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,k4_tmap_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10355,c_6693])).

cnf(c_10387,plain,
    ( k3_tmap_1(sK1,sK1,sK2,sK2,k4_tmap_1(sK1,sK2)) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10364,c_10355])).

cnf(c_10388,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10387,c_10355])).

cnf(c_10501,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10359,c_10388])).

cnf(c_10586,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10501,c_10365])).

cnf(c_12955,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12639,c_35,c_36,c_37,c_39,c_4725,c_7479,c_10586])).

cnf(c_12956,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12955])).

cnf(c_21465,plain,
    ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20811,c_35,c_36,c_37,c_39,c_4725,c_7479,c_10586,c_13420])).

cnf(c_23735,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23727,c_21465])).

cnf(c_3,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_25,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_714,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k4_tmap_1(sK1,sK2) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_715,plain,
    ( ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
    | sK3 != k4_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_714])).

cnf(c_2209,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3566,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_4724,plain,
    ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_4718])).

cnf(c_5015,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2876,c_4742])).

cnf(c_5812,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
    | k4_tmap_1(sK1,sK2) = sK3
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5015,c_35,c_36,c_37,c_39,c_4725])).

cnf(c_5813,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5812])).

cnf(c_7478,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_7476])).

cnf(c_2210,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3920,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_2210])).

cnf(c_5390,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3920])).

cnf(c_11161,plain,
    ( k4_tmap_1(sK1,sK2) != sK3
    | sK3 = k4_tmap_1(sK1,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_5390])).

cnf(c_24897,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23735,c_34,c_35,c_33,c_36,c_32,c_37,c_30,c_39,c_715,c_3566,c_4724,c_4725,c_5015,c_7478,c_7479,c_11161,c_13419])).

cnf(c_24902,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_9812,c_24897])).

cnf(c_7493,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7487,c_6714])).

cnf(c_7706,plain,
    ( v1_funct_1(X0) != iProver_top
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7493,c_35,c_36,c_37,c_38,c_40,c_41,c_42,c_3601,c_3830])).

cnf(c_7707,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
    | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7706])).

cnf(c_7719,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2876,c_7707])).

cnf(c_7776,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7719,c_35,c_36,c_37,c_39,c_4725,c_7479])).

cnf(c_7783,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | k4_tmap_1(sK1,sK2) = sK3
    | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7776,c_5813])).

cnf(c_8005,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7783,c_35,c_36,c_37,c_39,c_4725,c_5015,c_7479,c_7776])).

cnf(c_8006,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | k4_tmap_1(sK1,sK2) = sK3
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8005])).

cnf(c_2855,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_8012,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | k4_tmap_1(sK1,sK2) = sK3
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8006,c_2855])).

cnf(c_8015,plain,
    ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | k4_tmap_1(sK1,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8012,c_37,c_38,c_3601])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f83])).

cnf(c_2871,plain,
    ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X1,X0,X3,X2,X4)) != k1_funct_1(X4,sK0(X1,X0,X3,X2,X4))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X0,X1,X2,X3),X4) = iProver_top
    | v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) != iProver_top
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8019,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
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
    inference(superposition,[status(thm)],[c_8015,c_2871])).

cnf(c_8020,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
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
    inference(light_normalisation,[status(thm)],[c_8019,c_7487])).

cnf(c_8561,plain,
    ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | k4_tmap_1(sK1,sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8020,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_3601,c_3717,c_3830,c_4725,c_5015,c_7479])).

cnf(c_8562,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8561])).

cnf(c_24905,plain,
    ( k4_tmap_1(sK1,sK2) = sK3
    | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
    | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24902,c_8562])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37210,c_24905,c_13420,c_13419,c_11161,c_7479,c_7478,c_5813,c_4725,c_4724,c_3566,c_715,c_39,c_30,c_37,c_32,c_36,c_33,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.39/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.39/2.48  
% 15.39/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.39/2.48  
% 15.39/2.48  ------  iProver source info
% 15.39/2.48  
% 15.39/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.39/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.39/2.48  git: non_committed_changes: false
% 15.39/2.48  git: last_make_outside_of_git: false
% 15.39/2.48  
% 15.39/2.48  ------ 
% 15.39/2.48  
% 15.39/2.48  ------ Input Options
% 15.39/2.48  
% 15.39/2.48  --out_options                           all
% 15.39/2.48  --tptp_safe_out                         true
% 15.39/2.48  --problem_path                          ""
% 15.39/2.48  --include_path                          ""
% 15.39/2.48  --clausifier                            res/vclausify_rel
% 15.39/2.48  --clausifier_options                    --mode clausify
% 15.39/2.48  --stdin                                 false
% 15.39/2.48  --stats_out                             all
% 15.39/2.48  
% 15.39/2.48  ------ General Options
% 15.39/2.48  
% 15.39/2.48  --fof                                   false
% 15.39/2.48  --time_out_real                         305.
% 15.39/2.48  --time_out_virtual                      -1.
% 15.39/2.48  --symbol_type_check                     false
% 15.39/2.48  --clausify_out                          false
% 15.39/2.48  --sig_cnt_out                           false
% 15.39/2.48  --trig_cnt_out                          false
% 15.39/2.48  --trig_cnt_out_tolerance                1.
% 15.39/2.48  --trig_cnt_out_sk_spl                   false
% 15.39/2.48  --abstr_cl_out                          false
% 15.39/2.48  
% 15.39/2.48  ------ Global Options
% 15.39/2.48  
% 15.39/2.48  --schedule                              default
% 15.39/2.48  --add_important_lit                     false
% 15.39/2.48  --prop_solver_per_cl                    1000
% 15.39/2.48  --min_unsat_core                        false
% 15.39/2.48  --soft_assumptions                      false
% 15.39/2.48  --soft_lemma_size                       3
% 15.39/2.48  --prop_impl_unit_size                   0
% 15.39/2.48  --prop_impl_unit                        []
% 15.39/2.48  --share_sel_clauses                     true
% 15.39/2.48  --reset_solvers                         false
% 15.39/2.48  --bc_imp_inh                            [conj_cone]
% 15.39/2.48  --conj_cone_tolerance                   3.
% 15.39/2.48  --extra_neg_conj                        none
% 15.39/2.48  --large_theory_mode                     true
% 15.39/2.48  --prolific_symb_bound                   200
% 15.39/2.48  --lt_threshold                          2000
% 15.39/2.48  --clause_weak_htbl                      true
% 15.39/2.48  --gc_record_bc_elim                     false
% 15.39/2.48  
% 15.39/2.48  ------ Preprocessing Options
% 15.39/2.48  
% 15.39/2.48  --preprocessing_flag                    true
% 15.39/2.48  --time_out_prep_mult                    0.1
% 15.39/2.48  --splitting_mode                        input
% 15.39/2.48  --splitting_grd                         true
% 15.39/2.48  --splitting_cvd                         false
% 15.39/2.48  --splitting_cvd_svl                     false
% 15.39/2.48  --splitting_nvd                         32
% 15.39/2.48  --sub_typing                            true
% 15.39/2.48  --prep_gs_sim                           true
% 15.39/2.48  --prep_unflatten                        true
% 15.39/2.48  --prep_res_sim                          true
% 15.39/2.48  --prep_upred                            true
% 15.39/2.48  --prep_sem_filter                       exhaustive
% 15.39/2.48  --prep_sem_filter_out                   false
% 15.39/2.48  --pred_elim                             true
% 15.39/2.48  --res_sim_input                         true
% 15.39/2.48  --eq_ax_congr_red                       true
% 15.39/2.48  --pure_diseq_elim                       true
% 15.39/2.48  --brand_transform                       false
% 15.39/2.48  --non_eq_to_eq                          false
% 15.39/2.48  --prep_def_merge                        true
% 15.39/2.48  --prep_def_merge_prop_impl              false
% 15.39/2.48  --prep_def_merge_mbd                    true
% 15.39/2.48  --prep_def_merge_tr_red                 false
% 15.39/2.48  --prep_def_merge_tr_cl                  false
% 15.39/2.48  --smt_preprocessing                     true
% 15.39/2.48  --smt_ac_axioms                         fast
% 15.39/2.48  --preprocessed_out                      false
% 15.39/2.48  --preprocessed_stats                    false
% 15.39/2.48  
% 15.39/2.48  ------ Abstraction refinement Options
% 15.39/2.48  
% 15.39/2.48  --abstr_ref                             []
% 15.39/2.48  --abstr_ref_prep                        false
% 15.39/2.48  --abstr_ref_until_sat                   false
% 15.39/2.48  --abstr_ref_sig_restrict                funpre
% 15.39/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.39/2.48  --abstr_ref_under                       []
% 15.39/2.48  
% 15.39/2.48  ------ SAT Options
% 15.39/2.48  
% 15.39/2.48  --sat_mode                              false
% 15.39/2.48  --sat_fm_restart_options                ""
% 15.39/2.48  --sat_gr_def                            false
% 15.39/2.48  --sat_epr_types                         true
% 15.39/2.48  --sat_non_cyclic_types                  false
% 15.39/2.48  --sat_finite_models                     false
% 15.39/2.48  --sat_fm_lemmas                         false
% 15.39/2.48  --sat_fm_prep                           false
% 15.39/2.48  --sat_fm_uc_incr                        true
% 15.39/2.48  --sat_out_model                         small
% 15.39/2.48  --sat_out_clauses                       false
% 15.39/2.48  
% 15.39/2.48  ------ QBF Options
% 15.39/2.48  
% 15.39/2.48  --qbf_mode                              false
% 15.39/2.48  --qbf_elim_univ                         false
% 15.39/2.48  --qbf_dom_inst                          none
% 15.39/2.48  --qbf_dom_pre_inst                      false
% 15.39/2.48  --qbf_sk_in                             false
% 15.39/2.48  --qbf_pred_elim                         true
% 15.39/2.48  --qbf_split                             512
% 15.39/2.48  
% 15.39/2.48  ------ BMC1 Options
% 15.39/2.48  
% 15.39/2.48  --bmc1_incremental                      false
% 15.39/2.48  --bmc1_axioms                           reachable_all
% 15.39/2.48  --bmc1_min_bound                        0
% 15.39/2.48  --bmc1_max_bound                        -1
% 15.39/2.48  --bmc1_max_bound_default                -1
% 15.39/2.48  --bmc1_symbol_reachability              true
% 15.39/2.48  --bmc1_property_lemmas                  false
% 15.39/2.48  --bmc1_k_induction                      false
% 15.39/2.48  --bmc1_non_equiv_states                 false
% 15.39/2.48  --bmc1_deadlock                         false
% 15.39/2.48  --bmc1_ucm                              false
% 15.39/2.48  --bmc1_add_unsat_core                   none
% 15.39/2.48  --bmc1_unsat_core_children              false
% 15.39/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.39/2.48  --bmc1_out_stat                         full
% 15.39/2.48  --bmc1_ground_init                      false
% 15.39/2.48  --bmc1_pre_inst_next_state              false
% 15.39/2.48  --bmc1_pre_inst_state                   false
% 15.39/2.48  --bmc1_pre_inst_reach_state             false
% 15.39/2.48  --bmc1_out_unsat_core                   false
% 15.39/2.48  --bmc1_aig_witness_out                  false
% 15.39/2.48  --bmc1_verbose                          false
% 15.39/2.48  --bmc1_dump_clauses_tptp                false
% 15.39/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.39/2.48  --bmc1_dump_file                        -
% 15.39/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.39/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.39/2.48  --bmc1_ucm_extend_mode                  1
% 15.39/2.48  --bmc1_ucm_init_mode                    2
% 15.39/2.48  --bmc1_ucm_cone_mode                    none
% 15.39/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.39/2.48  --bmc1_ucm_relax_model                  4
% 15.39/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.39/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.39/2.48  --bmc1_ucm_layered_model                none
% 15.39/2.48  --bmc1_ucm_max_lemma_size               10
% 15.39/2.48  
% 15.39/2.48  ------ AIG Options
% 15.39/2.48  
% 15.39/2.48  --aig_mode                              false
% 15.39/2.48  
% 15.39/2.48  ------ Instantiation Options
% 15.39/2.48  
% 15.39/2.48  --instantiation_flag                    true
% 15.39/2.48  --inst_sos_flag                         false
% 15.39/2.48  --inst_sos_phase                        true
% 15.39/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.39/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.39/2.48  --inst_lit_sel_side                     num_symb
% 15.39/2.48  --inst_solver_per_active                1400
% 15.39/2.48  --inst_solver_calls_frac                1.
% 15.39/2.48  --inst_passive_queue_type               priority_queues
% 15.39/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.39/2.48  --inst_passive_queues_freq              [25;2]
% 15.39/2.48  --inst_dismatching                      true
% 15.39/2.48  --inst_eager_unprocessed_to_passive     true
% 15.39/2.48  --inst_prop_sim_given                   true
% 15.39/2.48  --inst_prop_sim_new                     false
% 15.39/2.48  --inst_subs_new                         false
% 15.39/2.48  --inst_eq_res_simp                      false
% 15.39/2.48  --inst_subs_given                       false
% 15.39/2.48  --inst_orphan_elimination               true
% 15.39/2.48  --inst_learning_loop_flag               true
% 15.39/2.48  --inst_learning_start                   3000
% 15.39/2.48  --inst_learning_factor                  2
% 15.39/2.48  --inst_start_prop_sim_after_learn       3
% 15.39/2.48  --inst_sel_renew                        solver
% 15.39/2.48  --inst_lit_activity_flag                true
% 15.39/2.48  --inst_restr_to_given                   false
% 15.39/2.48  --inst_activity_threshold               500
% 15.39/2.48  --inst_out_proof                        true
% 15.39/2.48  
% 15.39/2.48  ------ Resolution Options
% 15.39/2.48  
% 15.39/2.48  --resolution_flag                       true
% 15.39/2.48  --res_lit_sel                           adaptive
% 15.39/2.48  --res_lit_sel_side                      none
% 15.39/2.48  --res_ordering                          kbo
% 15.39/2.48  --res_to_prop_solver                    active
% 15.39/2.48  --res_prop_simpl_new                    false
% 15.39/2.48  --res_prop_simpl_given                  true
% 15.39/2.48  --res_passive_queue_type                priority_queues
% 15.39/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.39/2.48  --res_passive_queues_freq               [15;5]
% 15.39/2.48  --res_forward_subs                      full
% 15.39/2.48  --res_backward_subs                     full
% 15.39/2.48  --res_forward_subs_resolution           true
% 15.39/2.48  --res_backward_subs_resolution          true
% 15.39/2.48  --res_orphan_elimination                true
% 15.39/2.48  --res_time_limit                        2.
% 15.39/2.48  --res_out_proof                         true
% 15.39/2.48  
% 15.39/2.48  ------ Superposition Options
% 15.39/2.48  
% 15.39/2.48  --superposition_flag                    true
% 15.39/2.48  --sup_passive_queue_type                priority_queues
% 15.39/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.39/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.39/2.48  --demod_completeness_check              fast
% 15.39/2.48  --demod_use_ground                      true
% 15.39/2.48  --sup_to_prop_solver                    passive
% 15.39/2.48  --sup_prop_simpl_new                    true
% 15.39/2.48  --sup_prop_simpl_given                  true
% 15.39/2.48  --sup_fun_splitting                     false
% 15.39/2.48  --sup_smt_interval                      50000
% 15.39/2.48  
% 15.39/2.48  ------ Superposition Simplification Setup
% 15.39/2.48  
% 15.39/2.48  --sup_indices_passive                   []
% 15.39/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.39/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.39/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.39/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.39/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.39/2.48  --sup_full_bw                           [BwDemod]
% 15.39/2.48  --sup_immed_triv                        [TrivRules]
% 15.39/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.39/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.39/2.48  --sup_immed_bw_main                     []
% 15.39/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.39/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.39/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.39/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.39/2.48  
% 15.39/2.48  ------ Combination Options
% 15.39/2.48  
% 15.39/2.48  --comb_res_mult                         3
% 15.39/2.48  --comb_sup_mult                         2
% 15.39/2.48  --comb_inst_mult                        10
% 15.39/2.48  
% 15.39/2.48  ------ Debug Options
% 15.39/2.48  
% 15.39/2.48  --dbg_backtrace                         false
% 15.39/2.48  --dbg_dump_prop_clauses                 false
% 15.39/2.48  --dbg_dump_prop_clauses_file            -
% 15.39/2.48  --dbg_out_stat                          false
% 15.39/2.48  ------ Parsing...
% 15.39/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.39/2.48  
% 15.39/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.39/2.48  
% 15.39/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.39/2.48  
% 15.39/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.39/2.48  ------ Proving...
% 15.39/2.48  ------ Problem Properties 
% 15.39/2.48  
% 15.39/2.48  
% 15.39/2.48  clauses                                 34
% 15.39/2.48  conjectures                             10
% 15.39/2.48  EPR                                     11
% 15.39/2.48  Horn                                    19
% 15.39/2.48  unary                                   9
% 15.39/2.48  binary                                  1
% 15.39/2.48  lits                                    199
% 15.39/2.48  lits eq                                 7
% 15.39/2.48  fd_pure                                 0
% 15.39/2.48  fd_pseudo                               0
% 15.39/2.48  fd_cond                                 0
% 15.39/2.48  fd_pseudo_cond                          1
% 15.39/2.48  AC symbols                              0
% 15.39/2.48  
% 15.39/2.48  ------ Schedule dynamic 5 is on 
% 15.39/2.48  
% 15.39/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.39/2.48  
% 15.39/2.48  
% 15.39/2.48  ------ 
% 15.39/2.48  Current options:
% 15.39/2.48  ------ 
% 15.39/2.48  
% 15.39/2.48  ------ Input Options
% 15.39/2.48  
% 15.39/2.48  --out_options                           all
% 15.39/2.48  --tptp_safe_out                         true
% 15.39/2.48  --problem_path                          ""
% 15.39/2.48  --include_path                          ""
% 15.39/2.48  --clausifier                            res/vclausify_rel
% 15.39/2.48  --clausifier_options                    --mode clausify
% 15.39/2.48  --stdin                                 false
% 15.39/2.48  --stats_out                             all
% 15.39/2.48  
% 15.39/2.48  ------ General Options
% 15.39/2.48  
% 15.39/2.48  --fof                                   false
% 15.39/2.48  --time_out_real                         305.
% 15.39/2.48  --time_out_virtual                      -1.
% 15.39/2.48  --symbol_type_check                     false
% 15.39/2.48  --clausify_out                          false
% 15.39/2.48  --sig_cnt_out                           false
% 15.39/2.48  --trig_cnt_out                          false
% 15.39/2.48  --trig_cnt_out_tolerance                1.
% 15.39/2.48  --trig_cnt_out_sk_spl                   false
% 15.39/2.48  --abstr_cl_out                          false
% 15.39/2.48  
% 15.39/2.48  ------ Global Options
% 15.39/2.48  
% 15.39/2.48  --schedule                              default
% 15.39/2.48  --add_important_lit                     false
% 15.39/2.48  --prop_solver_per_cl                    1000
% 15.39/2.48  --min_unsat_core                        false
% 15.39/2.48  --soft_assumptions                      false
% 15.39/2.48  --soft_lemma_size                       3
% 15.39/2.48  --prop_impl_unit_size                   0
% 15.39/2.48  --prop_impl_unit                        []
% 15.39/2.48  --share_sel_clauses                     true
% 15.39/2.48  --reset_solvers                         false
% 15.39/2.48  --bc_imp_inh                            [conj_cone]
% 15.39/2.48  --conj_cone_tolerance                   3.
% 15.39/2.48  --extra_neg_conj                        none
% 15.39/2.48  --large_theory_mode                     true
% 15.39/2.48  --prolific_symb_bound                   200
% 15.39/2.48  --lt_threshold                          2000
% 15.39/2.48  --clause_weak_htbl                      true
% 15.39/2.48  --gc_record_bc_elim                     false
% 15.39/2.48  
% 15.39/2.48  ------ Preprocessing Options
% 15.39/2.48  
% 15.39/2.48  --preprocessing_flag                    true
% 15.39/2.48  --time_out_prep_mult                    0.1
% 15.39/2.48  --splitting_mode                        input
% 15.39/2.48  --splitting_grd                         true
% 15.39/2.48  --splitting_cvd                         false
% 15.39/2.48  --splitting_cvd_svl                     false
% 15.39/2.48  --splitting_nvd                         32
% 15.39/2.48  --sub_typing                            true
% 15.39/2.48  --prep_gs_sim                           true
% 15.39/2.48  --prep_unflatten                        true
% 15.39/2.48  --prep_res_sim                          true
% 15.39/2.48  --prep_upred                            true
% 15.39/2.48  --prep_sem_filter                       exhaustive
% 15.39/2.48  --prep_sem_filter_out                   false
% 15.39/2.48  --pred_elim                             true
% 15.39/2.48  --res_sim_input                         true
% 15.39/2.48  --eq_ax_congr_red                       true
% 15.39/2.48  --pure_diseq_elim                       true
% 15.39/2.48  --brand_transform                       false
% 15.39/2.48  --non_eq_to_eq                          false
% 15.39/2.48  --prep_def_merge                        true
% 15.39/2.48  --prep_def_merge_prop_impl              false
% 15.39/2.48  --prep_def_merge_mbd                    true
% 15.39/2.48  --prep_def_merge_tr_red                 false
% 15.39/2.48  --prep_def_merge_tr_cl                  false
% 15.39/2.48  --smt_preprocessing                     true
% 15.39/2.48  --smt_ac_axioms                         fast
% 15.39/2.48  --preprocessed_out                      false
% 15.39/2.48  --preprocessed_stats                    false
% 15.39/2.48  
% 15.39/2.48  ------ Abstraction refinement Options
% 15.39/2.48  
% 15.39/2.48  --abstr_ref                             []
% 15.39/2.48  --abstr_ref_prep                        false
% 15.39/2.48  --abstr_ref_until_sat                   false
% 15.39/2.48  --abstr_ref_sig_restrict                funpre
% 15.39/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.39/2.48  --abstr_ref_under                       []
% 15.39/2.48  
% 15.39/2.48  ------ SAT Options
% 15.39/2.48  
% 15.39/2.48  --sat_mode                              false
% 15.39/2.48  --sat_fm_restart_options                ""
% 15.39/2.48  --sat_gr_def                            false
% 15.39/2.48  --sat_epr_types                         true
% 15.39/2.48  --sat_non_cyclic_types                  false
% 15.39/2.48  --sat_finite_models                     false
% 15.39/2.48  --sat_fm_lemmas                         false
% 15.39/2.48  --sat_fm_prep                           false
% 15.39/2.48  --sat_fm_uc_incr                        true
% 15.39/2.48  --sat_out_model                         small
% 15.39/2.48  --sat_out_clauses                       false
% 15.39/2.48  
% 15.39/2.48  ------ QBF Options
% 15.39/2.48  
% 15.39/2.48  --qbf_mode                              false
% 15.39/2.48  --qbf_elim_univ                         false
% 15.39/2.48  --qbf_dom_inst                          none
% 15.39/2.48  --qbf_dom_pre_inst                      false
% 15.39/2.48  --qbf_sk_in                             false
% 15.39/2.48  --qbf_pred_elim                         true
% 15.39/2.48  --qbf_split                             512
% 15.39/2.48  
% 15.39/2.48  ------ BMC1 Options
% 15.39/2.48  
% 15.39/2.48  --bmc1_incremental                      false
% 15.39/2.48  --bmc1_axioms                           reachable_all
% 15.39/2.48  --bmc1_min_bound                        0
% 15.39/2.48  --bmc1_max_bound                        -1
% 15.39/2.48  --bmc1_max_bound_default                -1
% 15.39/2.48  --bmc1_symbol_reachability              true
% 15.39/2.48  --bmc1_property_lemmas                  false
% 15.39/2.48  --bmc1_k_induction                      false
% 15.39/2.48  --bmc1_non_equiv_states                 false
% 15.39/2.48  --bmc1_deadlock                         false
% 15.39/2.48  --bmc1_ucm                              false
% 15.39/2.48  --bmc1_add_unsat_core                   none
% 15.39/2.48  --bmc1_unsat_core_children              false
% 15.39/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.39/2.48  --bmc1_out_stat                         full
% 15.39/2.48  --bmc1_ground_init                      false
% 15.39/2.48  --bmc1_pre_inst_next_state              false
% 15.39/2.48  --bmc1_pre_inst_state                   false
% 15.39/2.48  --bmc1_pre_inst_reach_state             false
% 15.39/2.48  --bmc1_out_unsat_core                   false
% 15.39/2.48  --bmc1_aig_witness_out                  false
% 15.39/2.48  --bmc1_verbose                          false
% 15.39/2.48  --bmc1_dump_clauses_tptp                false
% 15.39/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.39/2.48  --bmc1_dump_file                        -
% 15.39/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.39/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.39/2.48  --bmc1_ucm_extend_mode                  1
% 15.39/2.48  --bmc1_ucm_init_mode                    2
% 15.39/2.48  --bmc1_ucm_cone_mode                    none
% 15.39/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.39/2.48  --bmc1_ucm_relax_model                  4
% 15.39/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.39/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.39/2.48  --bmc1_ucm_layered_model                none
% 15.39/2.48  --bmc1_ucm_max_lemma_size               10
% 15.39/2.48  
% 15.39/2.48  ------ AIG Options
% 15.39/2.48  
% 15.39/2.48  --aig_mode                              false
% 15.39/2.48  
% 15.39/2.48  ------ Instantiation Options
% 15.39/2.48  
% 15.39/2.48  --instantiation_flag                    true
% 15.39/2.48  --inst_sos_flag                         false
% 15.39/2.48  --inst_sos_phase                        true
% 15.39/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.39/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.39/2.48  --inst_lit_sel_side                     none
% 15.39/2.48  --inst_solver_per_active                1400
% 15.39/2.48  --inst_solver_calls_frac                1.
% 15.39/2.48  --inst_passive_queue_type               priority_queues
% 15.39/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.39/2.48  --inst_passive_queues_freq              [25;2]
% 15.39/2.48  --inst_dismatching                      true
% 15.39/2.48  --inst_eager_unprocessed_to_passive     true
% 15.39/2.48  --inst_prop_sim_given                   true
% 15.39/2.48  --inst_prop_sim_new                     false
% 15.39/2.48  --inst_subs_new                         false
% 15.39/2.48  --inst_eq_res_simp                      false
% 15.39/2.48  --inst_subs_given                       false
% 15.39/2.48  --inst_orphan_elimination               true
% 15.39/2.48  --inst_learning_loop_flag               true
% 15.39/2.48  --inst_learning_start                   3000
% 15.39/2.48  --inst_learning_factor                  2
% 15.39/2.48  --inst_start_prop_sim_after_learn       3
% 15.39/2.48  --inst_sel_renew                        solver
% 15.39/2.48  --inst_lit_activity_flag                true
% 15.39/2.48  --inst_restr_to_given                   false
% 15.39/2.48  --inst_activity_threshold               500
% 15.39/2.48  --inst_out_proof                        true
% 15.39/2.48  
% 15.39/2.48  ------ Resolution Options
% 15.39/2.48  
% 15.39/2.48  --resolution_flag                       false
% 15.39/2.48  --res_lit_sel                           adaptive
% 15.39/2.48  --res_lit_sel_side                      none
% 15.39/2.48  --res_ordering                          kbo
% 15.39/2.48  --res_to_prop_solver                    active
% 15.39/2.48  --res_prop_simpl_new                    false
% 15.39/2.48  --res_prop_simpl_given                  true
% 15.39/2.48  --res_passive_queue_type                priority_queues
% 15.39/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.39/2.48  --res_passive_queues_freq               [15;5]
% 15.39/2.48  --res_forward_subs                      full
% 15.39/2.48  --res_backward_subs                     full
% 15.39/2.48  --res_forward_subs_resolution           true
% 15.39/2.48  --res_backward_subs_resolution          true
% 15.39/2.48  --res_orphan_elimination                true
% 15.39/2.48  --res_time_limit                        2.
% 15.39/2.48  --res_out_proof                         true
% 15.39/2.48  
% 15.39/2.48  ------ Superposition Options
% 15.39/2.48  
% 15.39/2.48  --superposition_flag                    true
% 15.39/2.48  --sup_passive_queue_type                priority_queues
% 15.39/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.39/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.39/2.48  --demod_completeness_check              fast
% 15.39/2.48  --demod_use_ground                      true
% 15.39/2.48  --sup_to_prop_solver                    passive
% 15.39/2.48  --sup_prop_simpl_new                    true
% 15.39/2.48  --sup_prop_simpl_given                  true
% 15.39/2.48  --sup_fun_splitting                     false
% 15.39/2.48  --sup_smt_interval                      50000
% 15.39/2.48  
% 15.39/2.48  ------ Superposition Simplification Setup
% 15.39/2.48  
% 15.39/2.48  --sup_indices_passive                   []
% 15.39/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.39/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.39/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.39/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.39/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.39/2.48  --sup_full_bw                           [BwDemod]
% 15.39/2.48  --sup_immed_triv                        [TrivRules]
% 15.39/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.39/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.39/2.48  --sup_immed_bw_main                     []
% 15.39/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.39/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.39/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.39/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.39/2.48  
% 15.39/2.48  ------ Combination Options
% 15.39/2.48  
% 15.39/2.48  --comb_res_mult                         3
% 15.39/2.48  --comb_sup_mult                         2
% 15.39/2.48  --comb_inst_mult                        10
% 15.39/2.48  
% 15.39/2.48  ------ Debug Options
% 15.39/2.48  
% 15.39/2.48  --dbg_backtrace                         false
% 15.39/2.48  --dbg_dump_prop_clauses                 false
% 15.39/2.48  --dbg_dump_prop_clauses_file            -
% 15.39/2.48  --dbg_out_stat                          false
% 15.39/2.48  
% 15.39/2.48  
% 15.39/2.48  
% 15.39/2.48  
% 15.39/2.48  ------ Proving...
% 15.39/2.48  
% 15.39/2.48  
% 15.39/2.48  % SZS status Theorem for theBenchmark.p
% 15.39/2.48  
% 15.39/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.39/2.48  
% 15.39/2.48  fof(f12,axiom,(
% 15.39/2.48    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f41,plain,(
% 15.39/2.48    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.39/2.48    inference(ennf_transformation,[],[f12])).
% 15.39/2.48  
% 15.39/2.48  fof(f42,plain,(
% 15.39/2.48    ! [X0,X1] : ((m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k4_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.39/2.48    inference(flattening,[],[f41])).
% 15.39/2.48  
% 15.39/2.48  fof(f78,plain,(
% 15.39/2.48    ( ! [X0,X1] : (m1_subset_1(k4_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f42])).
% 15.39/2.48  
% 15.39/2.48  fof(f14,axiom,(
% 15.39/2.48    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f44,plain,(
% 15.39/2.48    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 15.39/2.48    inference(ennf_transformation,[],[f14])).
% 15.39/2.48  
% 15.39/2.48  fof(f80,plain,(
% 15.39/2.48    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f44])).
% 15.39/2.48  
% 15.39/2.48  fof(f19,conjecture,(
% 15.39/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f20,negated_conjecture,(
% 15.39/2.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,u1_struct_0(X1)) => k1_funct_1(X2,X3) = X3)) => r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2)))))),
% 15.39/2.48    inference(negated_conjecture,[],[f19])).
% 15.39/2.48  
% 15.39/2.48  fof(f53,plain,(
% 15.39/2.48    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : ((k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 15.39/2.48    inference(ennf_transformation,[],[f20])).
% 15.39/2.48  
% 15.39/2.48  fof(f54,plain,(
% 15.39/2.48    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 15.39/2.48    inference(flattening,[],[f53])).
% 15.39/2.48  
% 15.39/2.48  fof(f60,plain,(
% 15.39/2.48    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 15.39/2.48    introduced(choice_axiom,[])).
% 15.39/2.48  
% 15.39/2.48  fof(f59,plain,(
% 15.39/2.48    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k4_tmap_1(X0,sK2),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 15.39/2.48    introduced(choice_axiom,[])).
% 15.39/2.48  
% 15.39/2.48  fof(f58,plain,(
% 15.39/2.48    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X1),u1_struct_0(sK1),k4_tmap_1(sK1,X1),X2) & ! [X3] : (k1_funct_1(X2,X3) = X3 | ~r2_hidden(X3,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 15.39/2.48    introduced(choice_axiom,[])).
% 15.39/2.48  
% 15.39/2.48  fof(f61,plain,(
% 15.39/2.48    ((~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) & ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 15.39/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f54,f60,f59,f58])).
% 15.39/2.48  
% 15.39/2.48  fof(f94,plain,(
% 15.39/2.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 15.39/2.48    inference(cnf_transformation,[],[f61])).
% 15.39/2.48  
% 15.39/2.48  fof(f10,axiom,(
% 15.39/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f37,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.39/2.48    inference(ennf_transformation,[],[f10])).
% 15.39/2.48  
% 15.39/2.48  fof(f38,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.39/2.48    inference(flattening,[],[f37])).
% 15.39/2.48  
% 15.39/2.48  fof(f72,plain,(
% 15.39/2.48    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f38])).
% 15.39/2.48  
% 15.39/2.48  fof(f17,axiom,(
% 15.39/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f49,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.39/2.48    inference(ennf_transformation,[],[f17])).
% 15.39/2.48  
% 15.39/2.48  fof(f50,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.39/2.48    inference(flattening,[],[f49])).
% 15.39/2.48  
% 15.39/2.48  fof(f85,plain,(
% 15.39/2.48    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f50])).
% 15.39/2.48  
% 15.39/2.48  fof(f87,plain,(
% 15.39/2.48    ~v2_struct_0(sK1)),
% 15.39/2.48    inference(cnf_transformation,[],[f61])).
% 15.39/2.48  
% 15.39/2.48  fof(f88,plain,(
% 15.39/2.48    v2_pre_topc(sK1)),
% 15.39/2.48    inference(cnf_transformation,[],[f61])).
% 15.39/2.48  
% 15.39/2.48  fof(f89,plain,(
% 15.39/2.48    l1_pre_topc(sK1)),
% 15.39/2.48    inference(cnf_transformation,[],[f61])).
% 15.39/2.48  
% 15.39/2.48  fof(f92,plain,(
% 15.39/2.48    v1_funct_1(sK3)),
% 15.39/2.48    inference(cnf_transformation,[],[f61])).
% 15.39/2.48  
% 15.39/2.48  fof(f93,plain,(
% 15.39/2.48    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 15.39/2.48    inference(cnf_transformation,[],[f61])).
% 15.39/2.48  
% 15.39/2.48  fof(f90,plain,(
% 15.39/2.48    ~v2_struct_0(sK2)),
% 15.39/2.48    inference(cnf_transformation,[],[f61])).
% 15.39/2.48  
% 15.39/2.48  fof(f91,plain,(
% 15.39/2.48    m1_pre_topc(sK2,sK1)),
% 15.39/2.48    inference(cnf_transformation,[],[f61])).
% 15.39/2.48  
% 15.39/2.48  fof(f7,axiom,(
% 15.39/2.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f32,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.39/2.48    inference(ennf_transformation,[],[f7])).
% 15.39/2.48  
% 15.39/2.48  fof(f69,plain,(
% 15.39/2.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f32])).
% 15.39/2.48  
% 15.39/2.48  fof(f5,axiom,(
% 15.39/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f29,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.39/2.48    inference(ennf_transformation,[],[f5])).
% 15.39/2.48  
% 15.39/2.48  fof(f30,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.39/2.48    inference(flattening,[],[f29])).
% 15.39/2.48  
% 15.39/2.48  fof(f67,plain,(
% 15.39/2.48    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f30])).
% 15.39/2.48  
% 15.39/2.48  fof(f9,axiom,(
% 15.39/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f35,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.39/2.48    inference(ennf_transformation,[],[f9])).
% 15.39/2.48  
% 15.39/2.48  fof(f36,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.39/2.48    inference(flattening,[],[f35])).
% 15.39/2.48  
% 15.39/2.48  fof(f71,plain,(
% 15.39/2.48    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f36])).
% 15.39/2.48  
% 15.39/2.48  fof(f16,axiom,(
% 15.39/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f47,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.39/2.48    inference(ennf_transformation,[],[f16])).
% 15.39/2.48  
% 15.39/2.48  fof(f48,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.39/2.48    inference(flattening,[],[f47])).
% 15.39/2.48  
% 15.39/2.48  fof(f84,plain,(
% 15.39/2.48    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f48])).
% 15.39/2.48  
% 15.39/2.48  fof(f11,axiom,(
% 15.39/2.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f39,plain,(
% 15.39/2.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.39/2.48    inference(ennf_transformation,[],[f11])).
% 15.39/2.48  
% 15.39/2.48  fof(f40,plain,(
% 15.39/2.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.39/2.48    inference(flattening,[],[f39])).
% 15.39/2.48  
% 15.39/2.48  fof(f75,plain,(
% 15.39/2.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f40])).
% 15.39/2.48  
% 15.39/2.48  fof(f4,axiom,(
% 15.39/2.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f27,plain,(
% 15.39/2.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.39/2.48    inference(ennf_transformation,[],[f4])).
% 15.39/2.48  
% 15.39/2.48  fof(f28,plain,(
% 15.39/2.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.39/2.48    inference(flattening,[],[f27])).
% 15.39/2.48  
% 15.39/2.48  fof(f55,plain,(
% 15.39/2.48    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.39/2.48    inference(nnf_transformation,[],[f28])).
% 15.39/2.48  
% 15.39/2.48  fof(f65,plain,(
% 15.39/2.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f55])).
% 15.39/2.48  
% 15.39/2.48  fof(f74,plain,(
% 15.39/2.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f40])).
% 15.39/2.48  
% 15.39/2.48  fof(f73,plain,(
% 15.39/2.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f40])).
% 15.39/2.48  
% 15.39/2.48  fof(f15,axiom,(
% 15.39/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => (r2_hidden(X5,u1_struct_0(X2)) => k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) = k1_funct_1(X4,X5))) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f45,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : ((k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.39/2.48    inference(ennf_transformation,[],[f15])).
% 15.39/2.48  
% 15.39/2.48  fof(f46,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | ? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.39/2.48    inference(flattening,[],[f45])).
% 15.39/2.48  
% 15.39/2.48  fof(f56,plain,(
% 15.39/2.48    ! [X4,X3,X2,X1,X0] : (? [X5] : (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5) & r2_hidden(X5,u1_struct_0(X2)) & m1_subset_1(X5,u1_struct_0(X1))) => (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))))),
% 15.39/2.48    introduced(choice_axiom,[])).
% 15.39/2.48  
% 15.39/2.48  fof(f57,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | (k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.39/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f56])).
% 15.39/2.48  
% 15.39/2.48  fof(f82,plain,(
% 15.39/2.48    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f57])).
% 15.39/2.48  
% 15.39/2.48  fof(f13,axiom,(
% 15.39/2.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f43,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.39/2.48    inference(ennf_transformation,[],[f13])).
% 15.39/2.48  
% 15.39/2.48  fof(f79,plain,(
% 15.39/2.48    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f43])).
% 15.39/2.48  
% 15.39/2.48  fof(f2,axiom,(
% 15.39/2.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f23,plain,(
% 15.39/2.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 15.39/2.48    inference(ennf_transformation,[],[f2])).
% 15.39/2.48  
% 15.39/2.48  fof(f24,plain,(
% 15.39/2.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 15.39/2.48    inference(flattening,[],[f23])).
% 15.39/2.48  
% 15.39/2.48  fof(f63,plain,(
% 15.39/2.48    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f24])).
% 15.39/2.48  
% 15.39/2.48  fof(f1,axiom,(
% 15.39/2.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f21,plain,(
% 15.39/2.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 15.39/2.48    inference(ennf_transformation,[],[f1])).
% 15.39/2.48  
% 15.39/2.48  fof(f22,plain,(
% 15.39/2.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 15.39/2.48    inference(flattening,[],[f21])).
% 15.39/2.48  
% 15.39/2.48  fof(f62,plain,(
% 15.39/2.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f22])).
% 15.39/2.48  
% 15.39/2.48  fof(f8,axiom,(
% 15.39/2.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f33,plain,(
% 15.39/2.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 15.39/2.48    inference(ennf_transformation,[],[f8])).
% 15.39/2.48  
% 15.39/2.48  fof(f34,plain,(
% 15.39/2.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 15.39/2.48    inference(flattening,[],[f33])).
% 15.39/2.48  
% 15.39/2.48  fof(f70,plain,(
% 15.39/2.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f34])).
% 15.39/2.48  
% 15.39/2.48  fof(f6,axiom,(
% 15.39/2.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f31,plain,(
% 15.39/2.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 15.39/2.48    inference(ennf_transformation,[],[f6])).
% 15.39/2.48  
% 15.39/2.48  fof(f68,plain,(
% 15.39/2.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f31])).
% 15.39/2.48  
% 15.39/2.48  fof(f18,axiom,(
% 15.39/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,u1_struct_0(X1)) => k1_funct_1(k4_tmap_1(X0,X1),X2) = X2))))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f51,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (! [X2] : ((k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.39/2.48    inference(ennf_transformation,[],[f18])).
% 15.39/2.48  
% 15.39/2.48  fof(f52,plain,(
% 15.39/2.48    ! [X0] : (! [X1] : (! [X2] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.39/2.48    inference(flattening,[],[f51])).
% 15.39/2.48  
% 15.39/2.48  fof(f86,plain,(
% 15.39/2.48    ( ! [X2,X0,X1] : (k1_funct_1(k4_tmap_1(X0,X1),X2) = X2 | ~r2_hidden(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f52])).
% 15.39/2.48  
% 15.39/2.48  fof(f95,plain,(
% 15.39/2.48    ( ! [X3] : (k1_funct_1(sK3,X3) = X3 | ~r2_hidden(X3,u1_struct_0(sK2)) | ~m1_subset_1(X3,u1_struct_0(sK1))) )),
% 15.39/2.48    inference(cnf_transformation,[],[f61])).
% 15.39/2.48  
% 15.39/2.48  fof(f77,plain,(
% 15.39/2.48    ( ! [X0,X1] : (v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f42])).
% 15.39/2.48  
% 15.39/2.48  fof(f76,plain,(
% 15.39/2.48    ( ! [X0,X1] : (v1_funct_1(k4_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f42])).
% 15.39/2.48  
% 15.39/2.48  fof(f81,plain,(
% 15.39/2.48    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f57])).
% 15.39/2.48  
% 15.39/2.48  fof(f3,axiom,(
% 15.39/2.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 15.39/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.39/2.48  
% 15.39/2.48  fof(f25,plain,(
% 15.39/2.48    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 15.39/2.48    inference(ennf_transformation,[],[f3])).
% 15.39/2.48  
% 15.39/2.48  fof(f26,plain,(
% 15.39/2.48    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 15.39/2.48    inference(flattening,[],[f25])).
% 15.39/2.48  
% 15.39/2.48  fof(f64,plain,(
% 15.39/2.48    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f26])).
% 15.39/2.48  
% 15.39/2.48  fof(f66,plain,(
% 15.39/2.48    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f55])).
% 15.39/2.48  
% 15.39/2.48  fof(f97,plain,(
% 15.39/2.48    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 15.39/2.48    inference(equality_resolution,[],[f66])).
% 15.39/2.48  
% 15.39/2.48  fof(f96,plain,(
% 15.39/2.48    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3)),
% 15.39/2.48    inference(cnf_transformation,[],[f61])).
% 15.39/2.48  
% 15.39/2.48  fof(f83,plain,(
% 15.39/2.48    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.39/2.48    inference(cnf_transformation,[],[f57])).
% 15.39/2.48  
% 15.39/2.48  cnf(c_14,plain,
% 15.39/2.48      ( ~ m1_pre_topc(X0,X1)
% 15.39/2.48      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.39/2.48      | v2_struct_0(X1)
% 15.39/2.48      | ~ l1_pre_topc(X1)
% 15.39/2.48      | ~ v2_pre_topc(X1) ),
% 15.39/2.48      inference(cnf_transformation,[],[f78]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_2876,plain,
% 15.39/2.48      ( m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.48      | m1_subset_1(k4_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) = iProver_top
% 15.39/2.48      | v2_struct_0(X1) = iProver_top
% 15.39/2.48      | l1_pre_topc(X1) != iProver_top
% 15.39/2.48      | v2_pre_topc(X1) != iProver_top ),
% 15.39/2.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_18,plain,
% 15.39/2.48      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 15.39/2.48      inference(cnf_transformation,[],[f80]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_2872,plain,
% 15.39/2.48      ( m1_pre_topc(X0,X0) = iProver_top
% 15.39/2.48      | l1_pre_topc(X0) != iProver_top ),
% 15.39/2.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_27,negated_conjecture,
% 15.39/2.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
% 15.39/2.48      inference(cnf_transformation,[],[f94]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_2863,plain,
% 15.39/2.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 15.39/2.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_10,plain,
% 15.39/2.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.39/2.48      | ~ m1_pre_topc(X3,X4)
% 15.39/2.48      | ~ m1_pre_topc(X3,X1)
% 15.39/2.48      | ~ m1_pre_topc(X1,X4)
% 15.39/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.39/2.48      | v2_struct_0(X4)
% 15.39/2.48      | v2_struct_0(X2)
% 15.39/2.48      | ~ l1_pre_topc(X4)
% 15.39/2.48      | ~ l1_pre_topc(X2)
% 15.39/2.48      | ~ v2_pre_topc(X4)
% 15.39/2.48      | ~ v2_pre_topc(X2)
% 15.39/2.48      | ~ v1_funct_1(X0)
% 15.39/2.48      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 15.39/2.48      inference(cnf_transformation,[],[f72]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_2880,plain,
% 15.39/2.48      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 15.39/2.48      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.39/2.48      | m1_pre_topc(X3,X4) != iProver_top
% 15.39/2.48      | m1_pre_topc(X0,X4) != iProver_top
% 15.39/2.48      | m1_pre_topc(X3,X0) != iProver_top
% 15.39/2.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 15.39/2.48      | v2_struct_0(X1) = iProver_top
% 15.39/2.48      | v2_struct_0(X4) = iProver_top
% 15.39/2.48      | l1_pre_topc(X1) != iProver_top
% 15.39/2.48      | l1_pre_topc(X4) != iProver_top
% 15.39/2.48      | v2_pre_topc(X1) != iProver_top
% 15.39/2.48      | v2_pre_topc(X4) != iProver_top
% 15.39/2.48      | v1_funct_1(X2) != iProver_top ),
% 15.39/2.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_23,plain,
% 15.39/2.48      ( ~ m1_pre_topc(X0,X1)
% 15.39/2.48      | ~ m1_pre_topc(X2,X0)
% 15.39/2.48      | m1_pre_topc(X2,X1)
% 15.39/2.48      | ~ l1_pre_topc(X1)
% 15.39/2.48      | ~ v2_pre_topc(X1) ),
% 15.39/2.48      inference(cnf_transformation,[],[f85]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_2867,plain,
% 15.39/2.48      ( m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.48      | m1_pre_topc(X2,X0) != iProver_top
% 15.39/2.48      | m1_pre_topc(X2,X1) = iProver_top
% 15.39/2.48      | l1_pre_topc(X1) != iProver_top
% 15.39/2.48      | v2_pre_topc(X1) != iProver_top ),
% 15.39/2.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_3178,plain,
% 15.39/2.48      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k3_tmap_1(X4,X1,X0,X3,X2)
% 15.39/2.48      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.39/2.48      | m1_pre_topc(X3,X0) != iProver_top
% 15.39/2.48      | m1_pre_topc(X0,X4) != iProver_top
% 15.39/2.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 15.39/2.48      | v2_struct_0(X1) = iProver_top
% 15.39/2.48      | v2_struct_0(X4) = iProver_top
% 15.39/2.48      | l1_pre_topc(X1) != iProver_top
% 15.39/2.48      | l1_pre_topc(X4) != iProver_top
% 15.39/2.48      | v2_pre_topc(X1) != iProver_top
% 15.39/2.48      | v2_pre_topc(X4) != iProver_top
% 15.39/2.48      | v1_funct_1(X2) != iProver_top ),
% 15.39/2.48      inference(forward_subsumption_resolution,
% 15.39/2.48                [status(thm)],
% 15.39/2.48                [c_2880,c_2867]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_6954,plain,
% 15.39/2.48      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK2,X0,sK3)
% 15.39/2.48      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.48      | m1_pre_topc(X0,sK2) != iProver_top
% 15.39/2.48      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.48      | v2_struct_0(X1) = iProver_top
% 15.39/2.48      | v2_struct_0(sK1) = iProver_top
% 15.39/2.48      | l1_pre_topc(X1) != iProver_top
% 15.39/2.48      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.48      | v2_pre_topc(X1) != iProver_top
% 15.39/2.48      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.48      | v1_funct_1(sK3) != iProver_top ),
% 15.39/2.48      inference(superposition,[status(thm)],[c_2863,c_3178]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_34,negated_conjecture,
% 15.39/2.48      ( ~ v2_struct_0(sK1) ),
% 15.39/2.48      inference(cnf_transformation,[],[f87]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_35,plain,
% 15.39/2.48      ( v2_struct_0(sK1) != iProver_top ),
% 15.39/2.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_33,negated_conjecture,
% 15.39/2.48      ( v2_pre_topc(sK1) ),
% 15.39/2.48      inference(cnf_transformation,[],[f88]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_36,plain,
% 15.39/2.48      ( v2_pre_topc(sK1) = iProver_top ),
% 15.39/2.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_32,negated_conjecture,
% 15.39/2.48      ( l1_pre_topc(sK1) ),
% 15.39/2.48      inference(cnf_transformation,[],[f89]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_37,plain,
% 15.39/2.48      ( l1_pre_topc(sK1) = iProver_top ),
% 15.39/2.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_29,negated_conjecture,
% 15.39/2.48      ( v1_funct_1(sK3) ),
% 15.39/2.48      inference(cnf_transformation,[],[f92]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_40,plain,
% 15.39/2.48      ( v1_funct_1(sK3) = iProver_top ),
% 15.39/2.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_28,negated_conjecture,
% 15.39/2.48      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 15.39/2.48      inference(cnf_transformation,[],[f93]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_41,plain,
% 15.39/2.48      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 15.39/2.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_7149,plain,
% 15.39/2.48      ( l1_pre_topc(X1) != iProver_top
% 15.39/2.48      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK2,X0,sK3)
% 15.39/2.48      | m1_pre_topc(X0,sK2) != iProver_top
% 15.39/2.48      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.48      | v2_struct_0(X1) = iProver_top
% 15.39/2.48      | v2_pre_topc(X1) != iProver_top ),
% 15.39/2.48      inference(global_propositional_subsumption,
% 15.39/2.48                [status(thm)],
% 15.39/2.48                [c_6954,c_35,c_36,c_37,c_40,c_41]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_7150,plain,
% 15.39/2.48      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK2,X0,sK3)
% 15.39/2.48      | m1_pre_topc(X0,sK2) != iProver_top
% 15.39/2.48      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.48      | v2_struct_0(X1) = iProver_top
% 15.39/2.48      | l1_pre_topc(X1) != iProver_top
% 15.39/2.48      | v2_pre_topc(X1) != iProver_top ),
% 15.39/2.48      inference(renaming,[status(thm)],[c_7149]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_7161,plain,
% 15.39/2.48      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK2,X0,sK3)
% 15.39/2.48      | m1_pre_topc(X0,sK2) != iProver_top
% 15.39/2.48      | v2_struct_0(sK2) = iProver_top
% 15.39/2.48      | l1_pre_topc(sK2) != iProver_top
% 15.39/2.48      | v2_pre_topc(sK2) != iProver_top ),
% 15.39/2.48      inference(superposition,[status(thm)],[c_2872,c_7150]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_31,negated_conjecture,
% 15.39/2.48      ( ~ v2_struct_0(sK2) ),
% 15.39/2.48      inference(cnf_transformation,[],[f90]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_38,plain,
% 15.39/2.48      ( v2_struct_0(sK2) != iProver_top ),
% 15.39/2.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_30,negated_conjecture,
% 15.39/2.48      ( m1_pre_topc(sK2,sK1) ),
% 15.39/2.48      inference(cnf_transformation,[],[f91]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_39,plain,
% 15.39/2.48      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 15.39/2.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_2860,plain,
% 15.39/2.48      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 15.39/2.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_7,plain,
% 15.39/2.48      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 15.39/2.48      inference(cnf_transformation,[],[f69]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_2882,plain,
% 15.39/2.48      ( m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.48      | l1_pre_topc(X1) != iProver_top
% 15.39/2.48      | l1_pre_topc(X0) = iProver_top ),
% 15.39/2.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_3601,plain,
% 15.39/2.48      ( l1_pre_topc(sK1) != iProver_top
% 15.39/2.48      | l1_pre_topc(sK2) = iProver_top ),
% 15.39/2.48      inference(superposition,[status(thm)],[c_2860,c_2882]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_5,plain,
% 15.39/2.48      ( ~ m1_pre_topc(X0,X1)
% 15.39/2.48      | ~ l1_pre_topc(X1)
% 15.39/2.48      | ~ v2_pre_topc(X1)
% 15.39/2.48      | v2_pre_topc(X0) ),
% 15.39/2.48      inference(cnf_transformation,[],[f67]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_3714,plain,
% 15.39/2.48      ( ~ m1_pre_topc(sK2,X0)
% 15.39/2.48      | ~ l1_pre_topc(X0)
% 15.39/2.48      | ~ v2_pre_topc(X0)
% 15.39/2.48      | v2_pre_topc(sK2) ),
% 15.39/2.48      inference(instantiation,[status(thm)],[c_5]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_3715,plain,
% 15.39/2.48      ( m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.48      | l1_pre_topc(X0) != iProver_top
% 15.39/2.48      | v2_pre_topc(X0) != iProver_top
% 15.39/2.48      | v2_pre_topc(sK2) = iProver_top ),
% 15.39/2.48      inference(predicate_to_equality,[status(thm)],[c_3714]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_3717,plain,
% 15.39/2.48      ( m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.48      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.48      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.48      | v2_pre_topc(sK2) = iProver_top ),
% 15.39/2.48      inference(instantiation,[status(thm)],[c_3715]) ).
% 15.39/2.48  
% 15.39/2.48  cnf(c_7190,plain,
% 15.39/2.48      ( m1_pre_topc(X0,sK2) != iProver_top
% 15.39/2.48      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK2,X0,sK3) ),
% 15.39/2.48      inference(global_propositional_subsumption,
% 15.39/2.48                [status(thm)],
% 15.39/2.48                [c_7161,c_36,c_37,c_38,c_39,c_3601,c_3717]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7191,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK2,X0,sK3)
% 15.39/2.49      | m1_pre_topc(X0,sK2) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_7190]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7198,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK2,sK2,sK3)
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2872,c_7191]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9,plain,
% 15.39/2.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.39/2.49      | ~ m1_pre_topc(X3,X1)
% 15.39/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.39/2.49      | v2_struct_0(X1)
% 15.39/2.49      | v2_struct_0(X2)
% 15.39/2.49      | ~ l1_pre_topc(X1)
% 15.39/2.49      | ~ l1_pre_topc(X2)
% 15.39/2.49      | ~ v2_pre_topc(X1)
% 15.39/2.49      | ~ v2_pre_topc(X2)
% 15.39/2.49      | ~ v1_funct_1(X0)
% 15.39/2.49      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 15.39/2.49      inference(cnf_transformation,[],[f71]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2881,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X3,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5257,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k2_tmap_1(sK2,sK1,sK3,X0)
% 15.39/2.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,sK2) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2863,c_2881]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5465,plain,
% 15.39/2.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 15.39/2.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k2_tmap_1(sK2,sK1,sK3,X0) ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_5257,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_3601,c_3717]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5466,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k2_tmap_1(sK2,sK1,sK3,X0)
% 15.39/2.49      | m1_pre_topc(X0,sK2) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_5465]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5473,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2)
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2872,c_5466]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_3606,plain,
% 15.39/2.49      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK2) ),
% 15.39/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_3601]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_3716,plain,
% 15.39/2.49      ( ~ m1_pre_topc(sK2,sK1)
% 15.39/2.49      | ~ l1_pre_topc(sK1)
% 15.39/2.49      | ~ v2_pre_topc(sK1)
% 15.39/2.49      | v2_pre_topc(sK2) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_3714]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_3825,plain,
% 15.39/2.49      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_18]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_3464,plain,
% 15.39/2.49      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 15.39/2.49      | ~ m1_pre_topc(X2,X0)
% 15.39/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.39/2.49      | v2_struct_0(X0)
% 15.39/2.49      | v2_struct_0(X1)
% 15.39/2.49      | ~ l1_pre_topc(X0)
% 15.39/2.49      | ~ l1_pre_topc(X1)
% 15.39/2.49      | ~ v2_pre_topc(X0)
% 15.39/2.49      | ~ v2_pre_topc(X1)
% 15.39/2.49      | ~ v1_funct_1(sK3)
% 15.39/2.49      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_9]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_3612,plain,
% 15.39/2.49      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 15.39/2.49      | ~ m1_pre_topc(X0,sK2)
% 15.39/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.39/2.49      | v2_struct_0(sK1)
% 15.39/2.49      | v2_struct_0(sK2)
% 15.39/2.49      | ~ l1_pre_topc(sK1)
% 15.39/2.49      | ~ l1_pre_topc(sK2)
% 15.39/2.49      | ~ v2_pre_topc(sK1)
% 15.39/2.49      | ~ v2_pre_topc(sK2)
% 15.39/2.49      | ~ v1_funct_1(sK3)
% 15.39/2.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(X0)) = k2_tmap_1(sK2,sK1,sK3,X0) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_3464]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4423,plain,
% 15.39/2.49      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 15.39/2.49      | ~ m1_pre_topc(sK2,sK2)
% 15.39/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.39/2.49      | v2_struct_0(sK1)
% 15.39/2.49      | v2_struct_0(sK2)
% 15.39/2.49      | ~ l1_pre_topc(sK1)
% 15.39/2.49      | ~ l1_pre_topc(sK2)
% 15.39/2.49      | ~ v2_pre_topc(sK1)
% 15.39/2.49      | ~ v2_pre_topc(sK2)
% 15.39/2.49      | ~ v1_funct_1(sK3)
% 15.39/2.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_3612]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5576,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,sK3,sK2) ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_5473,c_34,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_3606,
% 15.39/2.49                 c_3716,c_3825,c_4423]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_22,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2))
% 15.39/2.49      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
% 15.39/2.49      | ~ m1_pre_topc(X0,X3)
% 15.39/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.39/2.49      | v2_struct_0(X3)
% 15.39/2.49      | v2_struct_0(X1)
% 15.39/2.49      | v2_struct_0(X0)
% 15.39/2.49      | ~ l1_pre_topc(X3)
% 15.39/2.49      | ~ l1_pre_topc(X1)
% 15.39/2.49      | ~ v2_pre_topc(X3)
% 15.39/2.49      | ~ v2_pre_topc(X1)
% 15.39/2.49      | ~ v1_funct_1(X2) ),
% 15.39/2.49      inference(cnf_transformation,[],[f84]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2868,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,k3_tmap_1(X3,X1,X0,X0,X2)) = iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X3) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(X3) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X3) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X3) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_11,plain,
% 15.39/2.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.39/2.49      | ~ m1_pre_topc(X3,X4)
% 15.39/2.49      | ~ m1_pre_topc(X1,X4)
% 15.39/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.39/2.49      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 15.39/2.49      | v2_struct_0(X4)
% 15.39/2.49      | v2_struct_0(X2)
% 15.39/2.49      | ~ l1_pre_topc(X4)
% 15.39/2.49      | ~ l1_pre_topc(X2)
% 15.39/2.49      | ~ v2_pre_topc(X4)
% 15.39/2.49      | ~ v2_pre_topc(X2)
% 15.39/2.49      | ~ v1_funct_1(X0) ),
% 15.39/2.49      inference(cnf_transformation,[],[f75]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2879,plain,
% 15.39/2.49      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X3,X4) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X4) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.39/2.49      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) = iProver_top
% 15.39/2.49      | v2_struct_0(X2) = iProver_top
% 15.39/2.49      | v2_struct_0(X4) = iProver_top
% 15.39/2.49      | l1_pre_topc(X2) != iProver_top
% 15.39/2.49      | l1_pre_topc(X4) != iProver_top
% 15.39/2.49      | v2_pre_topc(X2) != iProver_top
% 15.39/2.49      | v2_pre_topc(X4) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4,plain,
% 15.39/2.49      ( ~ r2_funct_2(X0,X1,X2,X3)
% 15.39/2.49      | ~ v1_funct_2(X2,X0,X1)
% 15.39/2.49      | ~ v1_funct_2(X3,X0,X1)
% 15.39/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.39/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.39/2.49      | ~ v1_funct_1(X2)
% 15.39/2.49      | ~ v1_funct_1(X3)
% 15.39/2.49      | X3 = X2 ),
% 15.39/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2884,plain,
% 15.39/2.49      ( X0 = X1
% 15.39/2.49      | r2_funct_2(X2,X3,X1,X0) != iProver_top
% 15.39/2.49      | v1_funct_2(X1,X2,X3) != iProver_top
% 15.39/2.49      | v1_funct_2(X0,X2,X3) != iProver_top
% 15.39/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.39/2.49      | v1_funct_1(X1) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4736,plain,
% 15.39/2.49      ( sK3 = X0
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) != iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2863,c_2884]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4741,plain,
% 15.39/2.49      ( v1_funct_1(X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | sK3 = X0
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) != iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_4736,c_40,c_41]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4742,plain,
% 15.39/2.49      ( sK3 = X0
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) != iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_4741]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6262,plain,
% 15.39/2.49      ( k3_tmap_1(X0,sK1,X1,sK2,X2) = sK3
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0,sK1,X1,sK2,X2)) != iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_2(k3_tmap_1(X0,sK1,X1,sK2,X2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(k3_tmap_1(X0,sK1,X1,sK2,X2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2879,c_4742]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6692,plain,
% 15.39/2.49      ( v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X0) != iProver_top
% 15.39/2.49      | v1_funct_2(k3_tmap_1(X0,sK1,X1,sK2,X2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0,sK1,X1,sK2,X2)) != iProver_top
% 15.39/2.49      | k3_tmap_1(X0,sK1,X1,sK2,X2) = sK3
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(k3_tmap_1(X0,sK1,X1,sK2,X2)) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_6262,c_35,c_36,c_37]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6693,plain,
% 15.39/2.49      ( k3_tmap_1(X0,sK1,X1,sK2,X2) = sK3
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k3_tmap_1(X0,sK1,X1,sK2,X2)) != iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_2(k3_tmap_1(X0,sK1,X1,sK2,X2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(k3_tmap_1(X0,sK1,X1,sK2,X2)) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_6692]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6708,plain,
% 15.39/2.49      ( k3_tmap_1(X0,sK1,sK2,sK2,sK3) = sK3
% 15.39/2.49      | v1_funct_2(k3_tmap_1(X0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k3_tmap_1(X0,sK1,sK2,sK2,sK3)) != iProver_top
% 15.39/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2868,c_6693]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_42,plain,
% 15.39/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_12,plain,
% 15.39/2.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.39/2.49      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 15.39/2.49      | ~ m1_pre_topc(X4,X3)
% 15.39/2.49      | ~ m1_pre_topc(X1,X3)
% 15.39/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.39/2.49      | v2_struct_0(X3)
% 15.39/2.49      | v2_struct_0(X2)
% 15.39/2.49      | ~ l1_pre_topc(X3)
% 15.39/2.49      | ~ l1_pre_topc(X2)
% 15.39/2.49      | ~ v2_pre_topc(X3)
% 15.39/2.49      | ~ v2_pre_topc(X2)
% 15.39/2.49      | ~ v1_funct_1(X0) ),
% 15.39/2.49      inference(cnf_transformation,[],[f74]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_3484,plain,
% 15.39/2.49      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,sK3),u1_struct_0(X3),u1_struct_0(X1))
% 15.39/2.49      | ~ v1_funct_2(sK3,u1_struct_0(X2),u1_struct_0(X1))
% 15.39/2.49      | ~ m1_pre_topc(X3,X0)
% 15.39/2.49      | ~ m1_pre_topc(X2,X0)
% 15.39/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 15.39/2.49      | v2_struct_0(X1)
% 15.39/2.49      | v2_struct_0(X0)
% 15.39/2.49      | ~ l1_pre_topc(X1)
% 15.39/2.49      | ~ l1_pre_topc(X0)
% 15.39/2.49      | ~ v2_pre_topc(X1)
% 15.39/2.49      | ~ v2_pre_topc(X0)
% 15.39/2.49      | ~ v1_funct_1(sK3) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_12]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_3627,plain,
% 15.39/2.49      ( v1_funct_2(k3_tmap_1(X0,sK1,sK2,X1,sK3),u1_struct_0(X1),u1_struct_0(sK1))
% 15.39/2.49      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 15.39/2.49      | ~ m1_pre_topc(X1,X0)
% 15.39/2.49      | ~ m1_pre_topc(sK2,X0)
% 15.39/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.39/2.49      | v2_struct_0(X0)
% 15.39/2.49      | v2_struct_0(sK1)
% 15.39/2.49      | ~ l1_pre_topc(X0)
% 15.39/2.49      | ~ l1_pre_topc(sK1)
% 15.39/2.49      | ~ v2_pre_topc(X0)
% 15.39/2.49      | ~ v2_pre_topc(sK1)
% 15.39/2.49      | ~ v1_funct_1(sK3) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_3484]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5984,plain,
% 15.39/2.49      ( v1_funct_2(k3_tmap_1(X0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.39/2.49      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 15.39/2.49      | ~ m1_pre_topc(sK2,X0)
% 15.39/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.39/2.49      | v2_struct_0(X0)
% 15.39/2.49      | v2_struct_0(sK1)
% 15.39/2.49      | ~ l1_pre_topc(X0)
% 15.39/2.49      | ~ l1_pre_topc(sK1)
% 15.39/2.49      | ~ v2_pre_topc(X0)
% 15.39/2.49      | ~ v2_pre_topc(sK1)
% 15.39/2.49      | ~ v1_funct_1(sK3) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_3627]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5989,plain,
% 15.39/2.49      ( v1_funct_2(k3_tmap_1(X0,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 15.39/2.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_5984]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_13,plain,
% 15.39/2.49      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 15.39/2.49      | ~ m1_pre_topc(X3,X4)
% 15.39/2.49      | ~ m1_pre_topc(X1,X4)
% 15.39/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 15.39/2.49      | v2_struct_0(X4)
% 15.39/2.49      | v2_struct_0(X2)
% 15.39/2.49      | ~ l1_pre_topc(X4)
% 15.39/2.49      | ~ l1_pre_topc(X2)
% 15.39/2.49      | ~ v2_pre_topc(X4)
% 15.39/2.49      | ~ v2_pre_topc(X2)
% 15.39/2.49      | ~ v1_funct_1(X0)
% 15.39/2.49      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 15.39/2.49      inference(cnf_transformation,[],[f73]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_3454,plain,
% 15.39/2.49      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 15.39/2.49      | ~ m1_pre_topc(X0,X2)
% 15.39/2.49      | ~ m1_pre_topc(X3,X2)
% 15.39/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.39/2.49      | v2_struct_0(X1)
% 15.39/2.49      | v2_struct_0(X2)
% 15.39/2.49      | ~ l1_pre_topc(X1)
% 15.39/2.49      | ~ l1_pre_topc(X2)
% 15.39/2.49      | ~ v2_pre_topc(X1)
% 15.39/2.49      | ~ v2_pre_topc(X2)
% 15.39/2.49      | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,sK3))
% 15.39/2.49      | ~ v1_funct_1(sK3) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_13]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_3607,plain,
% 15.39/2.49      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 15.39/2.49      | ~ m1_pre_topc(X0,X1)
% 15.39/2.49      | ~ m1_pre_topc(sK2,X1)
% 15.39/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.39/2.49      | v2_struct_0(X1)
% 15.39/2.49      | v2_struct_0(sK1)
% 15.39/2.49      | ~ l1_pre_topc(X1)
% 15.39/2.49      | ~ l1_pre_topc(sK1)
% 15.39/2.49      | ~ v2_pre_topc(X1)
% 15.39/2.49      | ~ v2_pre_topc(sK1)
% 15.39/2.49      | v1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK3))
% 15.39/2.49      | ~ v1_funct_1(sK3) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_3454]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6662,plain,
% 15.39/2.49      ( ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
% 15.39/2.49      | ~ m1_pre_topc(sK2,X0)
% 15.39/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.39/2.49      | v2_struct_0(X0)
% 15.39/2.49      | v2_struct_0(sK1)
% 15.39/2.49      | ~ l1_pre_topc(X0)
% 15.39/2.49      | ~ l1_pre_topc(sK1)
% 15.39/2.49      | ~ v2_pre_topc(X0)
% 15.39/2.49      | ~ v2_pre_topc(sK1)
% 15.39/2.49      | v1_funct_1(k3_tmap_1(X0,sK1,sK2,sK2,sK3))
% 15.39/2.49      | ~ v1_funct_1(sK3) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_3607]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6663,plain,
% 15.39/2.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k3_tmap_1(X0,sK1,sK2,sK2,sK3)) = iProver_top
% 15.39/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_6662]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6784,plain,
% 15.39/2.49      ( v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | k3_tmap_1(X0,sK1,sK2,sK2,sK3) = sK3
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_6708,c_35,c_36,c_37,c_38,c_40,c_41,c_42,c_5989,c_6663]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6785,plain,
% 15.39/2.49      ( k3_tmap_1(X0,sK1,sK2,sK2,sK3) = sK3
% 15.39/2.49      | m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_6784]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6795,plain,
% 15.39/2.49      ( k3_tmap_1(sK2,sK1,sK2,sK2,sK3) = sK3
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK2) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2872,c_6785]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6850,plain,
% 15.39/2.49      ( k3_tmap_1(sK2,sK1,sK2,sK2,sK3) = sK3 ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_6795,c_36,c_37,c_38,c_39,c_3601,c_3717]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7199,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.39/2.49      inference(light_normalisation,[status(thm)],[c_7198,c_5576,c_6850]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7487,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,sK3,sK2) = sK3 ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_7199,c_37,c_3601]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_20,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 15.39/2.49      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 15.39/2.49      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 15.39/2.49      | ~ m1_pre_topc(X0,X2)
% 15.39/2.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.39/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 15.39/2.49      | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
% 15.39/2.49      | v2_struct_0(X1)
% 15.39/2.49      | v2_struct_0(X2)
% 15.39/2.49      | v2_struct_0(X0)
% 15.39/2.49      | ~ l1_pre_topc(X1)
% 15.39/2.49      | ~ l1_pre_topc(X2)
% 15.39/2.49      | ~ v2_pre_topc(X1)
% 15.39/2.49      | ~ v2_pre_topc(X2)
% 15.39/2.49      | ~ v1_funct_1(X3)
% 15.39/2.49      | ~ v1_funct_1(X4) ),
% 15.39/2.49      inference(cnf_transformation,[],[f82]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2870,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4) = iProver_top
% 15.39/2.49      | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X2) != iProver_top
% 15.39/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 15.39/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) != iProver_top
% 15.39/2.49      | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0)) = iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(X2) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X2) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X3) != iProver_top
% 15.39/2.49      | v1_funct_1(X4) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7491,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(sK2)) = iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_7487,c_2870]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_3830,plain,
% 15.39/2.49      ( m1_pre_topc(sK2,sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_3825]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8422,plain,
% 15.39/2.49      ( v1_funct_1(X0) != iProver_top
% 15.39/2.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(sK2)) = iProver_top
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_7491,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_3601,
% 15.39/2.49                 c_3717,c_3830]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8423,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(sK2)) = iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_8422]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_17,plain,
% 15.39/2.49      ( ~ m1_pre_topc(X0,X1)
% 15.39/2.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.39/2.49      | ~ l1_pre_topc(X1) ),
% 15.39/2.49      inference(cnf_transformation,[],[f79]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2873,plain,
% 15.39/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_1,plain,
% 15.39/2.49      ( m1_subset_1(X0,X1)
% 15.39/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.39/2.49      | ~ r2_hidden(X0,X2) ),
% 15.39/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2887,plain,
% 15.39/2.49      ( m1_subset_1(X0,X1) = iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 15.39/2.49      | r2_hidden(X0,X2) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4026,plain,
% 15.39/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,u1_struct_0(X1)) = iProver_top
% 15.39/2.49      | r2_hidden(X2,u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2873,c_2887]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8433,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(X1)) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_8423,c_4026]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_0,plain,
% 15.39/2.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 15.39/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2888,plain,
% 15.39/2.49      ( m1_subset_1(X0,X1) != iProver_top
% 15.39/2.49      | r2_hidden(X0,X1) = iProver_top
% 15.39/2.49      | v1_xboole_0(X1) = iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9250,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(X1)) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_8433,c_2888]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9639,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X2) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(X2)) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_9250,c_4026]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_33923,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X2) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(X2)) = iProver_top
% 15.39/2.49      | l1_pre_topc(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(X1)) = iProver_top ),
% 15.39/2.49      inference(forward_subsumption_resolution,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_9639,c_2882]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_33926,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK1,X1) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(X1)) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2860,c_33923]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8,plain,
% 15.39/2.49      ( v2_struct_0(X0)
% 15.39/2.49      | ~ l1_struct_0(X0)
% 15.39/2.49      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 15.39/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_93,plain,
% 15.39/2.49      ( v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_struct_0(X0) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_95,plain,
% 15.39/2.49      ( v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_struct_0(sK1) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_93]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6,plain,
% 15.39/2.49      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 15.39/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_97,plain,
% 15.39/2.49      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_99,plain,
% 15.39/2.49      ( l1_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_97]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_33956,plain,
% 15.39/2.49      ( v1_funct_1(X0) != iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(X1)) = iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK1,X1) != iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_33926,c_35,c_37,c_95,c_99]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_33957,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK1,X1) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | m1_subset_1(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(X1)) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_33956]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_24,plain,
% 15.39/2.49      ( ~ m1_pre_topc(X0,X1)
% 15.39/2.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.39/2.49      | ~ r2_hidden(X2,u1_struct_0(X0))
% 15.39/2.49      | v2_struct_0(X1)
% 15.39/2.49      | v2_struct_0(X0)
% 15.39/2.49      | ~ l1_pre_topc(X1)
% 15.39/2.49      | ~ v2_pre_topc(X1)
% 15.39/2.49      | k1_funct_1(k4_tmap_1(X1,X0),X2) = X2 ),
% 15.39/2.49      inference(cnf_transformation,[],[f86]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2866,plain,
% 15.39/2.49      ( k1_funct_1(k4_tmap_1(X0,X1),X2) = X2
% 15.39/2.49      | m1_pre_topc(X1,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | r2_hidden(X2,u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_33972,plain,
% 15.39/2.49      ( k1_funct_1(k4_tmap_1(X0,X1),sK0(sK1,sK2,sK2,sK3,X2)) = sK0(sK1,sK2,sK2,sK3,X2)
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X2) = iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK1,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X2),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_33957,c_2866]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_34797,plain,
% 15.39/2.49      ( k1_funct_1(k4_tmap_1(X0,sK2),sK0(sK1,sK2,sK2,sK3,X1)) = sK0(sK1,sK2,sK2,sK3,X1)
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X1) = iProver_top
% 15.39/2.49      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK1,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X1) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_8423,c_33972]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9252,plain,
% 15.39/2.49      ( k1_funct_1(k4_tmap_1(X0,X1),sK0(sK1,sK2,sK2,sK3,X2)) = sK0(sK1,sK2,sK2,sK3,X2)
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X2) = iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X2),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_8433,c_2866]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_33054,plain,
% 15.39/2.49      ( k1_funct_1(k4_tmap_1(X0,sK2),sK0(sK1,sK2,sK2,sK3,X1)) = sK0(sK1,sK2,sK2,sK3,X1)
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X1) = iProver_top
% 15.39/2.49      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X1) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_8423,c_9252]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_37092,plain,
% 15.39/2.49      ( v2_struct_0(X0) = iProver_top
% 15.39/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | k1_funct_1(k4_tmap_1(X0,sK2),sK0(sK1,sK2,sK2,sK3,X1)) = sK0(sK1,sK2,sK2,sK3,X1)
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X1) = iProver_top
% 15.39/2.49      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X1) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_34797,c_38,c_33054]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_37093,plain,
% 15.39/2.49      ( k1_funct_1(k4_tmap_1(X0,sK2),sK0(sK1,sK2,sK2,sK3,X1)) = sK0(sK1,sK2,sK2,sK3,X1)
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X1) = iProver_top
% 15.39/2.49      | v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X1) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_37092]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_37108,plain,
% 15.39/2.49      ( k1_funct_1(k4_tmap_1(X0,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2876,c_37093]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_37210,plain,
% 15.39/2.49      ( k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_37108]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_26,negated_conjecture,
% 15.39/2.49      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 15.39/2.49      | ~ r2_hidden(X0,u1_struct_0(sK2))
% 15.39/2.49      | k1_funct_1(sK3,X0) = X0 ),
% 15.39/2.49      inference(cnf_transformation,[],[f95]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2864,plain,
% 15.39/2.49      ( k1_funct_1(sK3,X0) = X0
% 15.39/2.49      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9253,plain,
% 15.39/2.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0)) = sK0(sK1,sK2,sK2,sK3,X0)
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | r2_hidden(sK0(sK1,sK2,sK2,sK3,X0),u1_struct_0(sK2)) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_8433,c_2864]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9644,plain,
% 15.39/2.49      ( v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
% 15.39/2.49      | k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0)) = sK0(sK1,sK2,sK2,sK3,X0)
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_9253,c_37,c_39,c_8423]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9645,plain,
% 15.39/2.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0)) = sK0(sK1,sK2,sK2,sK3,X0)
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_9644]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9656,plain,
% 15.39/2.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2876,c_9645]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_15,plain,
% 15.39/2.49      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
% 15.39/2.49      | ~ m1_pre_topc(X1,X0)
% 15.39/2.49      | v2_struct_0(X0)
% 15.39/2.49      | ~ l1_pre_topc(X0)
% 15.39/2.49      | ~ v2_pre_topc(X0) ),
% 15.39/2.49      inference(cnf_transformation,[],[f77]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4718,plain,
% 15.39/2.49      ( v1_funct_2(k4_tmap_1(X0,sK2),u1_struct_0(sK2),u1_struct_0(X0))
% 15.39/2.49      | ~ m1_pre_topc(sK2,X0)
% 15.39/2.49      | v2_struct_0(X0)
% 15.39/2.49      | ~ l1_pre_topc(X0)
% 15.39/2.49      | ~ v2_pre_topc(X0) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_15]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4723,plain,
% 15.39/2.49      ( v1_funct_2(k4_tmap_1(X0,sK2),u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_4718]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4725,plain,
% 15.39/2.49      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_4723]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_16,plain,
% 15.39/2.49      ( ~ m1_pre_topc(X0,X1)
% 15.39/2.49      | v2_struct_0(X1)
% 15.39/2.49      | ~ l1_pre_topc(X1)
% 15.39/2.49      | ~ v2_pre_topc(X1)
% 15.39/2.49      | v1_funct_1(k4_tmap_1(X1,X0)) ),
% 15.39/2.49      inference(cnf_transformation,[],[f76]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7476,plain,
% 15.39/2.49      ( ~ m1_pre_topc(sK2,X0)
% 15.39/2.49      | v2_struct_0(X0)
% 15.39/2.49      | ~ l1_pre_topc(X0)
% 15.39/2.49      | ~ v2_pre_topc(X0)
% 15.39/2.49      | v1_funct_1(k4_tmap_1(X0,sK2)) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_16]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7477,plain,
% 15.39/2.49      ( m1_pre_topc(sK2,X0) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(X0,sK2)) = iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_7476]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7479,plain,
% 15.39/2.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) = iProver_top ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_7477]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9812,plain,
% 15.39/2.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_9656,c_35,c_36,c_37,c_39,c_4725,c_7479]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_21,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 15.39/2.49      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 15.39/2.49      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 15.39/2.49      | ~ m1_pre_topc(X0,X2)
% 15.39/2.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.39/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 15.39/2.49      | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2))
% 15.39/2.49      | v2_struct_0(X1)
% 15.39/2.49      | v2_struct_0(X2)
% 15.39/2.49      | v2_struct_0(X0)
% 15.39/2.49      | ~ l1_pre_topc(X1)
% 15.39/2.49      | ~ l1_pre_topc(X2)
% 15.39/2.49      | ~ v2_pre_topc(X1)
% 15.39/2.49      | ~ v2_pre_topc(X2)
% 15.39/2.49      | ~ v1_funct_1(X3)
% 15.39/2.49      | ~ v1_funct_1(X4) ),
% 15.39/2.49      inference(cnf_transformation,[],[f81]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2869,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4) = iProver_top
% 15.39/2.49      | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X2) != iProver_top
% 15.39/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 15.39/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) != iProver_top
% 15.39/2.49      | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2)) = iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(X2) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X2) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X3) != iProver_top
% 15.39/2.49      | v1_funct_1(X4) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2,plain,
% 15.39/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.39/2.49      | ~ m1_subset_1(X3,X1)
% 15.39/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.39/2.49      | ~ v1_funct_1(X0)
% 15.39/2.49      | v1_xboole_0(X1)
% 15.39/2.49      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 15.39/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2886,plain,
% 15.39/2.49      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 15.39/2.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.39/2.49      | m1_subset_1(X3,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top
% 15.39/2.49      | v1_xboole_0(X0) = iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6257,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,X4),X5) = k1_funct_1(k3_tmap_1(X2,X1,X3,X0,X4),X5)
% 15.39/2.49      | v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | v1_funct_2(k3_tmap_1(X2,X1,X3,X0,X4),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X2) != iProver_top
% 15.39/2.49      | m1_pre_topc(X3,X2) != iProver_top
% 15.39/2.49      | m1_subset_1(X5,u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X2) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X2) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X4) != iProver_top
% 15.39/2.49      | v1_funct_1(k3_tmap_1(X2,X1,X3,X0,X4)) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2879,c_2886]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2877,plain,
% 15.39/2.49      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X3,X4) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X4) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X2) = iProver_top
% 15.39/2.49      | v2_struct_0(X4) = iProver_top
% 15.39/2.49      | l1_pre_topc(X2) != iProver_top
% 15.39/2.49      | l1_pre_topc(X4) != iProver_top
% 15.39/2.49      | v2_pre_topc(X2) != iProver_top
% 15.39/2.49      | v2_pre_topc(X4) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) = iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2878,plain,
% 15.39/2.49      ( v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) != iProver_top
% 15.39/2.49      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2)) = iProver_top
% 15.39/2.49      | m1_pre_topc(X4,X3) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X3) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X3) = iProver_top
% 15.39/2.49      | v2_struct_0(X2) = iProver_top
% 15.39/2.49      | l1_pre_topc(X3) != iProver_top
% 15.39/2.49      | l1_pre_topc(X2) != iProver_top
% 15.39/2.49      | v2_pre_topc(X3) != iProver_top
% 15.39/2.49      | v2_pre_topc(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_15956,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,X0,X4),X5) = k1_funct_1(k3_tmap_1(X2,X1,X3,X0,X4),X5)
% 15.39/2.49      | v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X2) != iProver_top
% 15.39/2.49      | m1_pre_topc(X3,X2) != iProver_top
% 15.39/2.49      | m1_subset_1(X5,u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X2) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X2) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X4) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 15.39/2.49      inference(forward_subsumption_resolution,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_6257,c_2877,c_2878]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_15962,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK2,X0,sK3),X2) = k1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK3),X2)
% 15.39/2.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(sK3) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2863,c_15956]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_16641,plain,
% 15.39/2.49      ( l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK2,X0,sK3),X2) = k1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK3),X2)
% 15.39/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_15962,c_35,c_36,c_37,c_40,c_41]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_16642,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK2,X0,sK3),X2) = k1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK3),X2)
% 15.39/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_16641]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_16655,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK2,X0,sK3),sK0(X2,X0,X3,X4,X5)) = k1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK3),sK0(X2,X0,X3,X4,X5))
% 15.39/2.49      | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,X4,X3),X5) = iProver_top
% 15.39/2.49      | v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)) != iProver_top
% 15.39/2.49      | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X3,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) != iProver_top
% 15.39/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X2) = iProver_top
% 15.39/2.49      | v2_struct_0(X3) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | l1_pre_topc(X2) != iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X2) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v1_funct_1(X4) != iProver_top
% 15.39/2.49      | v1_funct_1(X5) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2869,c_16642]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_96,plain,
% 15.39/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X0) = iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_100,plain,
% 15.39/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) = iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_383,plain,
% 15.39/2.49      ( v2_struct_0(X0)
% 15.39/2.49      | ~ l1_pre_topc(X0)
% 15.39/2.49      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 15.39/2.49      inference(resolution,[status(thm)],[c_6,c_8]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_384,plain,
% 15.39/2.49      ( v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_17182,plain,
% 15.39/2.49      ( v1_funct_1(X5) != iProver_top
% 15.39/2.49      | v1_funct_1(X4) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X2) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(X3) = iProver_top
% 15.39/2.49      | v2_struct_0(X2) = iProver_top
% 15.39/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
% 15.39/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(X3,X0) != iProver_top
% 15.39/2.49      | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
% 15.39/2.49      | v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)) != iProver_top
% 15.39/2.49      | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,X4,X3),X5) = iProver_top
% 15.39/2.49      | k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK2,X0,sK3),sK0(X2,X0,X3,X4,X5)) = k1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK3),sK0(X2,X0,X3,X4,X5))
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X2) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_16655,c_96,c_100,c_384]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_17183,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k3_tmap_1(X1,sK1,sK2,X0,sK3),sK0(X2,X0,X3,X4,X5)) = k1_funct_1(k3_tmap_1(X1,sK1,sK2,X0,sK3),sK0(X2,X0,X3,X4,X5))
% 15.39/2.49      | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X0,X2,X4,X3),X5) = iProver_top
% 15.39/2.49      | v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)) != iProver_top
% 15.39/2.49      | v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X2)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(X3,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) != iProver_top
% 15.39/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(X3) = iProver_top
% 15.39/2.49      | v2_struct_0(X2) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X2) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X4) != iProver_top
% 15.39/2.49      | v1_funct_1(X5) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_17182]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_17208,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0,sK2,X1,X2,X3)) = k1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),sK0(X0,sK2,X1,X2,X3))
% 15.39/2.49      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK2,X0,X2,X1),X3) = iProver_top
% 15.39/2.49      | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,sK2) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X3) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2860,c_17183]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6796,plain,
% 15.39/2.49      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2860,c_6785]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5991,plain,
% 15.39/2.49      ( v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 15.39/2.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_5989]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6665,plain,
% 15.39/2.49      ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) = iProver_top
% 15.39/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_6663]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6710,plain,
% 15.39/2.49      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3
% 15.39/2.49      | v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,sK3)) != iProver_top
% 15.39/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_6708]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6816,plain,
% 15.39/2.49      ( k3_tmap_1(sK1,sK1,sK2,sK2,sK3) = sK3 ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_6796,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_5991,
% 15.39/2.49                 c_6665,c_6710]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_17227,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0,sK2,X1,X2,X3)) = k1_funct_1(sK3,sK0(X0,sK2,X1,X2,X3))
% 15.39/2.49      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK2,X0,X2,X1),X3) = iProver_top
% 15.39/2.49      | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,sK2) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X3) != iProver_top ),
% 15.39/2.49      inference(light_normalisation,[status(thm)],[c_17208,c_6816]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5113,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k1_funct_1(sK3,X0)
% 15.39/2.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 15.39/2.49      | v1_funct_1(sK3) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2863,c_2886]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5455,plain,
% 15.39/2.49      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 15.39/2.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k1_funct_1(sK3,X0)
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_5113,c_40,c_41]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5456,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = k1_funct_1(sK3,X0)
% 15.39/2.49      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_5455]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6024,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0,sK2,X1,X2,X3)) = k1_funct_1(sK3,sK0(X0,sK2,X1,X2,X3))
% 15.39/2.49      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK2,X0,X2,X1),X3) = iProver_top
% 15.39/2.49      | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,sK2) != iProver_top
% 15.39/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X3) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2869,c_5456]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6713,plain,
% 15.39/2.49      ( v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,sK2) != iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK2,X0,X2,X1),X3) = iProver_top
% 15.39/2.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0,sK2,X1,X2,X3)) = k1_funct_1(sK3,sK0(X0,sK2,X1,X2,X3))
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X3) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_6024,c_36,c_37,c_38,c_39,c_3601,c_3717]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6714,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0,sK2,X1,X2,X3)) = k1_funct_1(sK3,sK0(X0,sK2,X1,X2,X3))
% 15.39/2.49      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK2,X0,X2,X1),X3) = iProver_top
% 15.39/2.49      | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,sK2) != iProver_top
% 15.39/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X3) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_6713]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_14155,plain,
% 15.39/2.49      ( v2_struct_0(sK2)
% 15.39/2.49      | ~ l1_pre_topc(sK2)
% 15.39/2.49      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_383]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_14156,plain,
% 15.39/2.49      ( v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_14155]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_17387,plain,
% 15.39/2.49      ( v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,sK2) != iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK2,X0,X2,X1),X3) = iProver_top
% 15.39/2.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0,sK2,X1,X2,X3)) = k1_funct_1(sK3,sK0(X0,sK2,X1,X2,X3))
% 15.39/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X3) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_17227,c_37,c_38,c_3601,c_6714,c_14156]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_17388,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(X0,sK2,X1,X2,X3)) = k1_funct_1(sK3,sK0(X0,sK2,X1,X2,X3))
% 15.39/2.49      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k2_tmap_1(sK2,X0,X2,X1),X3) = iProver_top
% 15.39/2.49      | v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,sK2) != iProver_top
% 15.39/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X3) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_17387]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_6953,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,k4_tmap_1(X1,X0))
% 15.39/2.49      | v1_funct_2(k4_tmap_1(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(X2,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X3) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X3) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X3) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X3) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(X1,X0)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2876,c_3178]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_69,plain,
% 15.39/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(X1,X0)) = iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9821,plain,
% 15.39/2.49      ( v2_pre_topc(X3) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X3) != iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_struct_0(X3) = iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X3) != iProver_top
% 15.39/2.49      | m1_pre_topc(X2,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,k4_tmap_1(X1,X0)) ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_6953,c_69]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9822,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,k4_tmap_1(X1,X0))
% 15.39/2.49      | v1_funct_2(k4_tmap_1(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(X2,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X3) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X3) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X3) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X3) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_9821]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2875,plain,
% 15.39/2.49      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) = iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X0) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9838,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k3_tmap_1(X3,X1,X0,X2,k4_tmap_1(X1,X0))
% 15.39/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(X2,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X3) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X3) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X3) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X3) != iProver_top ),
% 15.39/2.49      inference(forward_subsumption_resolution,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_9822,c_2875]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9843,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK2,X0,k4_tmap_1(sK1,sK2))
% 15.39/2.49      | m1_pre_topc(X0,sK2) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2860,c_9838]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9997,plain,
% 15.39/2.49      ( v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,sK2) != iProver_top
% 15.39/2.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK2,X0,k4_tmap_1(sK1,sK2))
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_9843,c_35,c_36,c_37]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9998,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(X1,sK1,sK2,X0,k4_tmap_1(sK1,sK2))
% 15.39/2.49      | m1_pre_topc(X0,sK2) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,X1) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_9997]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10007,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK2,X0,k4_tmap_1(sK1,sK2))
% 15.39/2.49      | m1_pre_topc(X0,sK2) != iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK2) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2872,c_9998]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10218,plain,
% 15.39/2.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 15.39/2.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK2,X0,k4_tmap_1(sK1,sK2)) ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_10007,c_36,c_37,c_38,c_39,c_3601,c_3717]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10219,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(sK2,sK1,sK2,X0,k4_tmap_1(sK1,sK2))
% 15.39/2.49      | m1_pre_topc(X0,sK2) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_10218]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10226,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k3_tmap_1(sK2,sK1,sK2,sK2,k4_tmap_1(sK1,sK2))
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2872,c_10219]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5256,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k2_tmap_1(X0,X1,k4_tmap_1(X1,X0),X2)
% 15.39/2.49      | v1_funct_2(k4_tmap_1(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(X2,X0) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(X1,X0)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2876,c_2881]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7305,plain,
% 15.39/2.49      ( l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | m1_pre_topc(X2,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k2_tmap_1(X0,X1,k4_tmap_1(X1,X0),X2)
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_5256,c_69,c_96,c_100]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7306,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k2_tmap_1(X0,X1,k4_tmap_1(X1,X0),X2)
% 15.39/2.49      | v1_funct_2(k4_tmap_1(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(X2,X0) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_7305]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7319,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),k4_tmap_1(X1,X0),u1_struct_0(X2)) = k2_tmap_1(X0,X1,k4_tmap_1(X1,X0),X2)
% 15.39/2.49      | m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(X2,X0) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top ),
% 15.39/2.49      inference(forward_subsumption_resolution,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_7306,c_2875]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7324,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),X0)
% 15.39/2.49      | m1_pre_topc(X0,sK2) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2860,c_7319]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7431,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),X0)
% 15.39/2.49      | m1_pre_topc(X0,sK2) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_7324,c_35,c_36,c_37,c_38]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7439,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2872,c_7431]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7442,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_7439,c_37,c_3601]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10227,plain,
% 15.39/2.49      ( k3_tmap_1(sK2,sK1,sK2,sK2,k4_tmap_1(sK1,sK2)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.39/2.49      inference(light_normalisation,[status(thm)],[c_10226,c_7442]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10621,plain,
% 15.39/2.49      ( k3_tmap_1(sK2,sK1,sK2,sK2,k4_tmap_1(sK1,sK2)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_10227,c_37,c_3601]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10624,plain,
% 15.39/2.49      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 15.39/2.49      | m1_subset_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_10621,c_2879]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10008,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(sK1,sK1,sK2,X0,k4_tmap_1(sK1,sK2))
% 15.39/2.49      | m1_pre_topc(X0,sK2) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2860,c_9998]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10036,plain,
% 15.39/2.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 15.39/2.49      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(sK1,sK1,sK2,X0,k4_tmap_1(sK1,sK2)) ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_10008,c_35,c_36,c_37]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10037,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(X0)) = k3_tmap_1(sK1,sK1,sK2,X0,k4_tmap_1(sK1,sK2))
% 15.39/2.49      | m1_pre_topc(X0,sK2) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_10036]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10044,plain,
% 15.39/2.49      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),u1_struct_0(sK2)) = k3_tmap_1(sK1,sK1,sK2,sK2,k4_tmap_1(sK1,sK2))
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2872,c_10037]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10045,plain,
% 15.39/2.49      ( k3_tmap_1(sK1,sK1,sK2,sK2,k4_tmap_1(sK1,sK2)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.39/2.49      inference(light_normalisation,[status(thm)],[c_10044,c_7442]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10355,plain,
% 15.39/2.49      ( k3_tmap_1(sK1,sK1,sK2,sK2,k4_tmap_1(sK1,sK2)) = k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_10045,c_37,c_3601]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10358,plain,
% 15.39/2.49      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_10355,c_2879]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_12623,plain,
% 15.39/2.49      ( m1_subset_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_10358,c_35,c_36,c_37,c_39,c_4725,c_7479]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_13419,plain,
% 15.39/2.49      ( ~ m1_pre_topc(sK2,sK1)
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.39/2.49      | v2_struct_0(sK1)
% 15.39/2.49      | ~ l1_pre_topc(sK1)
% 15.39/2.49      | ~ v2_pre_topc(sK1) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_14]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_13420,plain,
% 15.39/2.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_13419]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_20792,plain,
% 15.39/2.49      ( m1_subset_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_10624,c_35,c_36,c_37,c_39,c_4725,c_7479,c_10358,
% 15.39/2.49                 c_13420]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_20807,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),X0) != iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_20792,c_2884]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5319,plain,
% 15.39/2.49      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X2) != iProver_top
% 15.39/2.49      | m1_pre_topc(X3,X2) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(X2) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | l1_pre_topc(X2) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(k3_tmap_1(X2,X0,X1,X3,k4_tmap_1(X0,X1))) = iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(X0,X1)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2876,c_2877]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_72,plain,
% 15.39/2.49      ( v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) = iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X0) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9356,plain,
% 15.39/2.49      ( m1_pre_topc(X1,X0) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X2) != iProver_top
% 15.39/2.49      | m1_pre_topc(X3,X2) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | v2_struct_0(X2) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | l1_pre_topc(X2) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(k3_tmap_1(X2,X0,X1,X3,k4_tmap_1(X0,X1))) = iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(X0,X1)) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_5319,c_72]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9357,plain,
% 15.39/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(X2,X3) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X3) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X3) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X3) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X3) != iProver_top
% 15.39/2.49      | v1_funct_1(k3_tmap_1(X3,X1,X0,X2,k4_tmap_1(X1,X0))) = iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(X1,X0)) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_9356]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9362,plain,
% 15.39/2.49      ( v1_funct_1(k3_tmap_1(X3,X1,X0,X2,k4_tmap_1(X1,X0))) = iProver_top
% 15.39/2.49      | v2_pre_topc(X3) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X3) != iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_struct_0(X3) = iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X3) != iProver_top
% 15.39/2.49      | m1_pre_topc(X2,X3) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X1) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_9357,c_69]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_9363,plain,
% 15.39/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | m1_pre_topc(X0,X2) != iProver_top
% 15.39/2.49      | m1_pre_topc(X3,X2) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X2) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X2) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(k3_tmap_1(X2,X1,X0,X3,k4_tmap_1(X1,X0))) = iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_9362]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10365,plain,
% 15.39/2.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) = iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_10355,c_9363]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10359,plain,
% 15.39/2.49      ( v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_10355,c_2878]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_11507,plain,
% 15.39/2.49      ( v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_10359,c_35,c_36,c_37,c_39,c_4725,c_7479]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_22199,plain,
% 15.39/2.49      ( v1_funct_1(X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),X0) != iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_20807,c_35,c_36,c_37,c_39,c_4725,c_7479,c_10359,
% 15.39/2.49                 c_10365,c_13420]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_22200,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),X0) != iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_22199]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_22214,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0
% 15.39/2.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0))
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_17388,c_22200]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_22627,plain,
% 15.39/2.49      ( v1_funct_1(X0) != iProver_top
% 15.39/2.49      | k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0
% 15.39/2.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0))
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_22214,c_35,c_36,c_37,c_38,c_39,c_3601,c_3830,c_4725,
% 15.39/2.49                 c_7479,c_13420]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_22628,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = X0
% 15.39/2.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),X0))
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_22627]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_22639,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
% 15.39/2.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,k4_tmap_1(sK1,sK2),k4_tmap_1(sK1,sK2)))
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2876,c_22628]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10360,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) = iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_10355,c_2868]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10626,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) = iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_10621,c_2868]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_17935,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) = iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_10360,c_35,c_36,c_37,c_38,c_39,c_4725,c_7479,c_13420]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5014,plain,
% 15.39/2.49      ( k4_tmap_1(X0,X1) = X2
% 15.39/2.49      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) != iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(X0,X1)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2876,c_2884]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8081,plain,
% 15.39/2.49      ( v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) != iProver_top
% 15.39/2.49      | k4_tmap_1(X0,X1) = X2
% 15.39/2.49      | m1_pre_topc(X1,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(X0,X1)) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_5014,c_72]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8082,plain,
% 15.39/2.49      ( k4_tmap_1(X0,X1) = X2
% 15.39/2.49      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) != iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(X0,X1)) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_8081]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2874,plain,
% 15.39/2.49      ( m1_pre_topc(X0,X1) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(X1,X0)) = iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8097,plain,
% 15.39/2.49      ( k4_tmap_1(X0,X1) = X2
% 15.39/2.49      | r2_funct_2(u1_struct_0(X1),u1_struct_0(X0),k4_tmap_1(X0,X1),X2) != iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X1,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.39/2.49      inference(forward_subsumption_resolution,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_8082,c_2874]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_17940,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2)
% 15.39/2.49      | v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_17935,c_8097]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_23727,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = k4_tmap_1(sK1,sK2) ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_22639,c_35,c_36,c_37,c_39,c_4725,c_7479,c_10358,
% 15.39/2.49                 c_10359,c_10365,c_13420,c_17940]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_20811,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
% 15.39/2.49      | v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_20792,c_4742]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_12639,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
% 15.39/2.49      | v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_12623,c_4742]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10364,plain,
% 15.39/2.49      ( k3_tmap_1(sK1,sK1,sK2,sK2,k4_tmap_1(sK1,sK2)) = sK3
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
% 15.39/2.49      | v1_funct_2(k3_tmap_1(sK1,sK1,sK2,sK2,k4_tmap_1(sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k3_tmap_1(sK1,sK1,sK2,sK2,k4_tmap_1(sK1,sK2))) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_10355,c_6693]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10387,plain,
% 15.39/2.49      ( k3_tmap_1(sK1,sK1,sK2,sK2,k4_tmap_1(sK1,sK2)) = sK3
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
% 15.39/2.49      | v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(light_normalisation,[status(thm)],[c_10364,c_10355]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10388,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
% 15.39/2.49      | v1_funct_2(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_10387,c_10355]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10501,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(backward_subsumption_resolution,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_10359,c_10388]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_10586,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(forward_subsumption_resolution,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_10501,c_10365]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_12955,plain,
% 15.39/2.49      ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_12639,c_35,c_36,c_37,c_39,c_4725,c_7479,c_10586]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_12956,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_12955]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_21465,plain,
% 15.39/2.49      ( k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2) = sK3
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k2_tmap_1(sK2,sK1,k4_tmap_1(sK1,sK2),sK2)) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_20811,c_35,c_36,c_37,c_39,c_4725,c_7479,c_10586,
% 15.39/2.49                 c_13420]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_23735,plain,
% 15.39/2.49      ( k4_tmap_1(sK1,sK2) = sK3
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_23727,c_21465]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_3,plain,
% 15.39/2.49      ( r2_funct_2(X0,X1,X2,X2)
% 15.39/2.49      | ~ v1_funct_2(X2,X0,X1)
% 15.39/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.39/2.49      | ~ v1_funct_1(X2) ),
% 15.39/2.49      inference(cnf_transformation,[],[f97]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_25,negated_conjecture,
% 15.39/2.49      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
% 15.39/2.49      inference(cnf_transformation,[],[f96]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_714,plain,
% 15.39/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.39/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.39/2.49      | ~ v1_funct_1(X0)
% 15.39/2.49      | k4_tmap_1(sK1,sK2) != X0
% 15.39/2.49      | u1_struct_0(sK1) != X2
% 15.39/2.49      | u1_struct_0(sK2) != X1
% 15.39/2.49      | sK3 != X0 ),
% 15.39/2.49      inference(resolution_lifted,[status(thm)],[c_3,c_25]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_715,plain,
% 15.39/2.49      ( ~ v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.39/2.49      | ~ m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 15.39/2.49      | ~ v1_funct_1(k4_tmap_1(sK1,sK2))
% 15.39/2.49      | sK3 != k4_tmap_1(sK1,sK2) ),
% 15.39/2.49      inference(unflattening,[status(thm)],[c_714]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2209,plain,( X0 = X0 ),theory(equality) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_3566,plain,
% 15.39/2.49      ( sK3 = sK3 ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_2209]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_4724,plain,
% 15.39/2.49      ( v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 15.39/2.49      | ~ m1_pre_topc(sK2,sK1)
% 15.39/2.49      | v2_struct_0(sK1)
% 15.39/2.49      | ~ l1_pre_topc(sK1)
% 15.39/2.49      | ~ v2_pre_topc(sK1) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_4718]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5015,plain,
% 15.39/2.49      ( k4_tmap_1(sK1,sK2) = sK3
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2876,c_4742]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5812,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
% 15.39/2.49      | k4_tmap_1(sK1,sK2) = sK3
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_5015,c_35,c_36,c_37,c_39,c_4725]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5813,plain,
% 15.39/2.49      ( k4_tmap_1(sK1,sK2) = sK3
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_5812]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7478,plain,
% 15.39/2.49      ( ~ m1_pre_topc(sK2,sK1)
% 15.39/2.49      | v2_struct_0(sK1)
% 15.39/2.49      | ~ l1_pre_topc(sK1)
% 15.39/2.49      | ~ v2_pre_topc(sK1)
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_7476]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2210,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_3920,plain,
% 15.39/2.49      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_2210]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_5390,plain,
% 15.39/2.49      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_3920]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_11161,plain,
% 15.39/2.49      ( k4_tmap_1(sK1,sK2) != sK3
% 15.39/2.49      | sK3 = k4_tmap_1(sK1,sK2)
% 15.39/2.49      | sK3 != sK3 ),
% 15.39/2.49      inference(instantiation,[status(thm)],[c_5390]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_24897,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) != iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_23735,c_34,c_35,c_33,c_36,c_32,c_37,c_30,c_39,c_715,
% 15.39/2.49                 c_3566,c_4724,c_4725,c_5015,c_7478,c_7479,c_11161,
% 15.39/2.49                 c_13419]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_24902,plain,
% 15.39/2.49      ( k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)) ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_9812,c_24897]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7493,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0))
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(sK3) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_7487,c_6714]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7706,plain,
% 15.39/2.49      ( v1_funct_1(X0) != iProver_top
% 15.39/2.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0))
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_7493,c_35,c_36,c_37,c_38,c_40,c_41,c_42,c_3601,c_3830]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7707,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,X0)) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,X0))
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X0) = iProver_top
% 15.39/2.49      | v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v1_funct_1(X0) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_7706]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7719,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_2876,c_7707]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7776,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_7719,c_35,c_36,c_37,c_39,c_4725,c_7479]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_7783,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 15.39/2.49      | k4_tmap_1(sK1,sK2) = sK3
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_7776,c_5813]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8005,plain,
% 15.39/2.49      ( k4_tmap_1(sK1,sK2) = sK3
% 15.39/2.49      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_7783,c_35,c_36,c_37,c_39,c_4725,c_5015,c_7479,c_7776]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8006,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 15.39/2.49      | k4_tmap_1(sK1,sK2) = sK3
% 15.39/2.49      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_8005]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2855,plain,
% 15.39/2.49      ( v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8012,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 15.39/2.49      | k4_tmap_1(sK1,sK2) = sK3
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_8006,c_2855]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8015,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) = k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 15.39/2.49      | k4_tmap_1(sK1,sK2) = sK3 ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_8012,c_37,c_38,c_3601]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_19,plain,
% 15.39/2.49      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
% 15.39/2.49      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 15.39/2.49      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
% 15.39/2.49      | ~ m1_pre_topc(X0,X2)
% 15.39/2.49      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 15.39/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
% 15.39/2.49      | v2_struct_0(X1)
% 15.39/2.49      | v2_struct_0(X2)
% 15.39/2.49      | v2_struct_0(X0)
% 15.39/2.49      | ~ l1_pre_topc(X1)
% 15.39/2.49      | ~ l1_pre_topc(X2)
% 15.39/2.49      | ~ v2_pre_topc(X1)
% 15.39/2.49      | ~ v2_pre_topc(X2)
% 15.39/2.49      | ~ v1_funct_1(X3)
% 15.39/2.49      | ~ v1_funct_1(X4)
% 15.39/2.49      | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK0(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK0(X1,X2,X0,X3,X4)) ),
% 15.39/2.49      inference(cnf_transformation,[],[f83]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_2871,plain,
% 15.39/2.49      ( k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK0(X1,X0,X3,X2,X4)) != k1_funct_1(X4,sK0(X1,X0,X3,X2,X4))
% 15.39/2.49      | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X0,X1,X2,X3),X4) = iProver_top
% 15.39/2.49      | v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(X3,X0) != iProver_top
% 15.39/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) != iProver_top
% 15.39/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(X1) = iProver_top
% 15.39/2.49      | v2_struct_0(X3) = iProver_top
% 15.39/2.49      | v2_struct_0(X0) = iProver_top
% 15.39/2.49      | l1_pre_topc(X1) != iProver_top
% 15.39/2.49      | l1_pre_topc(X0) != iProver_top
% 15.39/2.49      | v2_pre_topc(X1) != iProver_top
% 15.39/2.49      | v2_pre_topc(X0) != iProver_top
% 15.39/2.49      | v1_funct_1(X2) != iProver_top
% 15.39/2.49      | v1_funct_1(X4) != iProver_top ),
% 15.39/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8019,plain,
% 15.39/2.49      ( k4_tmap_1(sK1,sK2) = sK3
% 15.39/2.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK2,sK1,sK3,sK2),k4_tmap_1(sK1,sK2)) = iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 15.39/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.39/2.49      inference(superposition,[status(thm)],[c_8015,c_2871]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8020,plain,
% 15.39/2.49      ( k4_tmap_1(sK1,sK2) = sK3
% 15.39/2.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 15.39/2.49      | r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k4_tmap_1(sK1,sK2)) = iProver_top
% 15.39/2.49      | v1_funct_2(k4_tmap_1(sK1,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 15.39/2.49      | m1_pre_topc(sK2,sK2) != iProver_top
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | v2_struct_0(sK1) = iProver_top
% 15.39/2.49      | v2_struct_0(sK2) = iProver_top
% 15.39/2.49      | l1_pre_topc(sK1) != iProver_top
% 15.39/2.49      | l1_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK1) != iProver_top
% 15.39/2.49      | v2_pre_topc(sK2) != iProver_top
% 15.39/2.49      | v1_funct_1(k4_tmap_1(sK1,sK2)) != iProver_top
% 15.39/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.39/2.49      inference(light_normalisation,[status(thm)],[c_8019,c_7487]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8561,plain,
% 15.39/2.49      ( m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 15.39/2.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 15.39/2.49      | k4_tmap_1(sK1,sK2) = sK3 ),
% 15.39/2.49      inference(global_propositional_subsumption,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_8020,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_3601,
% 15.39/2.49                 c_3717,c_3830,c_4725,c_5015,c_7479]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_8562,plain,
% 15.39/2.49      ( k4_tmap_1(sK1,sK2) = sK3
% 15.39/2.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != k1_funct_1(sK3,sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2)))
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 15.39/2.49      inference(renaming,[status(thm)],[c_8561]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(c_24905,plain,
% 15.39/2.49      ( k4_tmap_1(sK1,sK2) = sK3
% 15.39/2.49      | k1_funct_1(k4_tmap_1(sK1,sK2),sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))) != sK0(sK1,sK2,sK2,sK3,k4_tmap_1(sK1,sK2))
% 15.39/2.49      | m1_subset_1(k4_tmap_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 15.39/2.49      inference(demodulation,[status(thm)],[c_24902,c_8562]) ).
% 15.39/2.49  
% 15.39/2.49  cnf(contradiction,plain,
% 15.39/2.49      ( $false ),
% 15.39/2.49      inference(minisat,
% 15.39/2.49                [status(thm)],
% 15.39/2.49                [c_37210,c_24905,c_13420,c_13419,c_11161,c_7479,c_7478,
% 15.39/2.49                 c_5813,c_4725,c_4724,c_3566,c_715,c_39,c_30,c_37,c_32,
% 15.39/2.49                 c_36,c_33,c_35,c_34]) ).
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.39/2.49  
% 15.39/2.49  ------                               Statistics
% 15.39/2.49  
% 15.39/2.49  ------ General
% 15.39/2.49  
% 15.39/2.49  abstr_ref_over_cycles:                  0
% 15.39/2.49  abstr_ref_under_cycles:                 0
% 15.39/2.49  gc_basic_clause_elim:                   0
% 15.39/2.49  forced_gc_time:                         0
% 15.39/2.49  parsing_time:                           0.014
% 15.39/2.49  unif_index_cands_time:                  0.
% 15.39/2.49  unif_index_add_time:                    0.
% 15.39/2.49  orderings_time:                         0.
% 15.39/2.49  out_proof_time:                         0.04
% 15.39/2.49  total_time:                             1.753
% 15.39/2.49  num_of_symbols:                         55
% 15.39/2.49  num_of_terms:                           51534
% 15.39/2.49  
% 15.39/2.49  ------ Preprocessing
% 15.39/2.49  
% 15.39/2.49  num_of_splits:                          0
% 15.39/2.49  num_of_split_atoms:                     0
% 15.39/2.49  num_of_reused_defs:                     0
% 15.39/2.49  num_eq_ax_congr_red:                    49
% 15.39/2.49  num_of_sem_filtered_clauses:            1
% 15.39/2.49  num_of_subtypes:                        0
% 15.39/2.49  monotx_restored_types:                  0
% 15.39/2.49  sat_num_of_epr_types:                   0
% 15.39/2.49  sat_num_of_non_cyclic_types:            0
% 15.39/2.49  sat_guarded_non_collapsed_types:        0
% 15.39/2.49  num_pure_diseq_elim:                    0
% 15.39/2.49  simp_replaced_by:                       0
% 15.39/2.49  res_preprocessed:                       176
% 15.39/2.49  prep_upred:                             0
% 15.39/2.49  prep_unflattend:                        78
% 15.39/2.49  smt_new_axioms:                         0
% 15.39/2.49  pred_elim_cands:                        10
% 15.39/2.49  pred_elim:                              1
% 15.39/2.49  pred_elim_cl:                           1
% 15.39/2.49  pred_elim_cycles:                       7
% 15.39/2.49  merged_defs:                            0
% 15.39/2.49  merged_defs_ncl:                        0
% 15.39/2.49  bin_hyper_res:                          0
% 15.39/2.49  prep_cycles:                            4
% 15.39/2.49  pred_elim_time:                         0.049
% 15.39/2.49  splitting_time:                         0.
% 15.39/2.49  sem_filter_time:                        0.
% 15.39/2.49  monotx_time:                            0.001
% 15.39/2.49  subtype_inf_time:                       0.
% 15.39/2.49  
% 15.39/2.49  ------ Problem properties
% 15.39/2.49  
% 15.39/2.49  clauses:                                34
% 15.39/2.49  conjectures:                            10
% 15.39/2.49  epr:                                    11
% 15.39/2.49  horn:                                   19
% 15.39/2.49  ground:                                 9
% 15.39/2.49  unary:                                  9
% 15.39/2.49  binary:                                 1
% 15.39/2.49  lits:                                   199
% 15.39/2.49  lits_eq:                                7
% 15.39/2.49  fd_pure:                                0
% 15.39/2.49  fd_pseudo:                              0
% 15.39/2.49  fd_cond:                                0
% 15.39/2.49  fd_pseudo_cond:                         1
% 15.39/2.49  ac_symbols:                             0
% 15.39/2.49  
% 15.39/2.49  ------ Propositional Solver
% 15.39/2.49  
% 15.39/2.49  prop_solver_calls:                      31
% 15.39/2.49  prop_fast_solver_calls:                 6262
% 15.39/2.49  smt_solver_calls:                       0
% 15.39/2.49  smt_fast_solver_calls:                  0
% 15.39/2.49  prop_num_of_clauses:                    11566
% 15.39/2.49  prop_preprocess_simplified:             19922
% 15.39/2.49  prop_fo_subsumed:                       924
% 15.39/2.49  prop_solver_time:                       0.
% 15.39/2.49  smt_solver_time:                        0.
% 15.39/2.49  smt_fast_solver_time:                   0.
% 15.39/2.49  prop_fast_solver_time:                  0.
% 15.39/2.49  prop_unsat_core_time:                   0.002
% 15.39/2.49  
% 15.39/2.49  ------ QBF
% 15.39/2.49  
% 15.39/2.49  qbf_q_res:                              0
% 15.39/2.49  qbf_num_tautologies:                    0
% 15.39/2.49  qbf_prep_cycles:                        0
% 15.39/2.49  
% 15.39/2.49  ------ BMC1
% 15.39/2.49  
% 15.39/2.49  bmc1_current_bound:                     -1
% 15.39/2.49  bmc1_last_solved_bound:                 -1
% 15.39/2.49  bmc1_unsat_core_size:                   -1
% 15.39/2.49  bmc1_unsat_core_parents_size:           -1
% 15.39/2.49  bmc1_merge_next_fun:                    0
% 15.39/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.39/2.49  
% 15.39/2.49  ------ Instantiation
% 15.39/2.49  
% 15.39/2.49  inst_num_of_clauses:                    2833
% 15.39/2.49  inst_num_in_passive:                    294
% 15.39/2.49  inst_num_in_active:                     1533
% 15.39/2.49  inst_num_in_unprocessed:                1006
% 15.39/2.49  inst_num_of_loops:                      1620
% 15.39/2.49  inst_num_of_learning_restarts:          0
% 15.39/2.49  inst_num_moves_active_passive:          82
% 15.39/2.49  inst_lit_activity:                      0
% 15.39/2.49  inst_lit_activity_moves:                1
% 15.39/2.49  inst_num_tautologies:                   0
% 15.39/2.49  inst_num_prop_implied:                  0
% 15.39/2.49  inst_num_existing_simplified:           0
% 15.39/2.49  inst_num_eq_res_simplified:             0
% 15.39/2.49  inst_num_child_elim:                    0
% 15.39/2.49  inst_num_of_dismatching_blockings:      2103
% 15.39/2.49  inst_num_of_non_proper_insts:           3578
% 15.39/2.49  inst_num_of_duplicates:                 0
% 15.39/2.49  inst_inst_num_from_inst_to_res:         0
% 15.39/2.49  inst_dismatching_checking_time:         0.
% 15.39/2.49  
% 15.39/2.49  ------ Resolution
% 15.39/2.49  
% 15.39/2.49  res_num_of_clauses:                     0
% 15.39/2.49  res_num_in_passive:                     0
% 15.39/2.49  res_num_in_active:                      0
% 15.39/2.49  res_num_of_loops:                       180
% 15.39/2.49  res_forward_subset_subsumed:            79
% 15.39/2.49  res_backward_subset_subsumed:           0
% 15.39/2.49  res_forward_subsumed:                   0
% 15.39/2.49  res_backward_subsumed:                  0
% 15.39/2.49  res_forward_subsumption_resolution:     0
% 15.39/2.49  res_backward_subsumption_resolution:    0
% 15.39/2.49  res_clause_to_clause_subsumption:       4197
% 15.39/2.49  res_orphan_elimination:                 0
% 15.39/2.49  res_tautology_del:                      170
% 15.39/2.49  res_num_eq_res_simplified:              0
% 15.39/2.49  res_num_sel_changes:                    0
% 15.39/2.49  res_moves_from_active_to_pass:          0
% 15.39/2.49  
% 15.39/2.49  ------ Superposition
% 15.39/2.49  
% 15.39/2.49  sup_time_total:                         0.
% 15.39/2.49  sup_time_generating:                    0.
% 15.39/2.49  sup_time_sim_full:                      0.
% 15.39/2.49  sup_time_sim_immed:                     0.
% 15.39/2.49  
% 15.39/2.49  sup_num_of_clauses:                     477
% 15.39/2.49  sup_num_in_active:                      248
% 15.39/2.49  sup_num_in_passive:                     229
% 15.39/2.49  sup_num_of_loops:                       322
% 15.39/2.49  sup_fw_superposition:                   406
% 15.39/2.49  sup_bw_superposition:                   357
% 15.39/2.49  sup_immediate_simplified:               261
% 15.39/2.49  sup_given_eliminated:                   0
% 15.39/2.49  comparisons_done:                       0
% 15.39/2.49  comparisons_avoided:                    107
% 15.39/2.49  
% 15.39/2.49  ------ Simplifications
% 15.39/2.49  
% 15.39/2.49  
% 15.39/2.49  sim_fw_subset_subsumed:                 71
% 15.39/2.49  sim_bw_subset_subsumed:                 56
% 15.39/2.49  sim_fw_subsumed:                        64
% 15.39/2.49  sim_bw_subsumed:                        9
% 15.39/2.49  sim_fw_subsumption_res:                 49
% 15.39/2.49  sim_bw_subsumption_res:                 16
% 15.39/2.49  sim_tautology_del:                      19
% 15.39/2.49  sim_eq_tautology_del:                   32
% 15.39/2.49  sim_eq_res_simp:                        0
% 15.39/2.49  sim_fw_demodulated:                     34
% 15.39/2.49  sim_bw_demodulated:                     58
% 15.39/2.49  sim_light_normalised:                   91
% 15.39/2.49  sim_joinable_taut:                      0
% 15.39/2.49  sim_joinable_simp:                      0
% 15.39/2.49  sim_ac_normalised:                      0
% 15.39/2.49  sim_smt_subsumption:                    0
% 15.39/2.49  
%------------------------------------------------------------------------------
