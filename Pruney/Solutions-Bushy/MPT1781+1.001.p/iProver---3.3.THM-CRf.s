%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1781+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:23 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :  170 (1355 expanded)
%              Number of clauses        :  111 ( 312 expanded)
%              Number of leaves         :   15 ( 439 expanded)
%              Depth                    :   27
%              Number of atoms          : 1069 (13448 expanded)
%              Number of equality atoms :  225 (1408 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal clause size      :   24 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
        & v1_funct_1(k3_struct_0(X0)) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0] :
      ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f34,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f33,f32,f31])).

fof(f51,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f29,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,u1_struct_0(X2))
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,sK0(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK0(X0,X1,X2,X3,X4))
        & r2_hidden(sK0(X0,X1,X2,X3,X4),u1_struct_0(X2))
        & m1_subset_1(sK0(X0,X1,X2,X3,X4),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f29])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f37,plain,(
    ! [X0] :
      ( v1_funct_1(k3_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_tmap_1(X0,X1) = k2_tmap_1(X0,X0,k3_struct_0(X0),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0] :
      ( k3_struct_0(X0) = k6_relat_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X3] :
      ( k1_funct_1(sK3,X3) = X3
      | ~ r2_hidden(X3,u1_struct_0(sK2))
      | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f30])).

cnf(c_5,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_287,plain,
    ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_5,c_3])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1310,plain,
    ( v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_287,c_20])).

cnf(c_1311,plain,
    ( v1_funct_2(k3_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1310])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X2,X0,X3,X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X0,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k4_tmap_1(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_545,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | m1_subset_1(sK0(X2,X4,X1,X3,X0),u1_struct_0(X4))
    | ~ m1_pre_topc(X1,X4)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | k2_tmap_1(X4,X2,X3,X1) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_13])).

cnf(c_546,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(sK3,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X2,X1,X3,X0,sK3),u1_struct_0(X1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,X2,X0,X3) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_550,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | m1_subset_1(sK0(X2,X1,X3,X0,sK3),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(sK3,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,X2,X0,X3) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_546,c_17])).

cnf(c_551,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(sK3,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X2,X1,X3,X0,sK3),u1_struct_0(X1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_tmap_1(X1,X2,X0,X3) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_550])).

cnf(c_993,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(sK3,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(sK0(X2,X1,X3,X0,sK3),u1_struct_0(X1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_tmap_1(X1,X2,X0,X3) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK2)
    | sK1 != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_551])).

cnf(c_994,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,sK1,sK2,X0,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | k2_tmap_1(sK1,X1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_993])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_998,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,sK1,sK2,X0,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | k2_tmap_1(sK1,X1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_994,c_22,c_21,c_20,c_19])).

cnf(c_999,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,sK1,sK2,X0,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(sK1,X1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_998])).

cnf(c_1161,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,sK1,sK2,X0,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(sK1,X1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_999,c_21])).

cnf(c_1162,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | m1_subset_1(sK0(sK1,sK1,sK2,X0,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_tmap_1(sK1,sK1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1161])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1166,plain,
    ( m1_subset_1(sK0(sK1,sK1,sK2,X0,sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK1,sK1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1162,c_22,c_20,c_16,c_15])).

cnf(c_1167,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | m1_subset_1(sK0(sK1,sK1,sK2,X0,sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK1,sK1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1166])).

cnf(c_1686,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | m1_subset_1(sK0(sK1,sK1,sK2,X0,sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK1,sK1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k3_struct_0(sK1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1311,c_1167])).

cnf(c_1687,plain,
    ( m1_subset_1(sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK2) != k4_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_1686])).

cnf(c_57,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( v1_funct_1(k3_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_60,plain,
    ( v1_funct_1(k3_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_66,plain,
    ( m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,X1,k3_struct_0(X1),X0) = k4_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_889,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,X0,k3_struct_0(X0),X1) = k4_tmap_1(X0,X1)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_890,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK2) = k4_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_1689,plain,
    ( m1_subset_1(sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1687,c_22,c_21,c_20,c_57,c_60,c_66,c_890])).

cnf(c_2020,plain,
    ( m1_subset_1(sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1689])).

cnf(c_2358,plain,
    ( m1_subset_1(sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2020])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_262,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_5,c_6])).

cnf(c_1282,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_262,c_22])).

cnf(c_1283,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_1282])).

cnf(c_54,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1285,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1283,c_22,c_20,c_54,c_57])).

cnf(c_1355,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3)
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_1285])).

cnf(c_1356,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(unflattening,[status(thm)],[c_1355])).

cnf(c_1697,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(sK1),X1,X0,X2) = k1_funct_1(X0,X2)
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k3_struct_0(sK1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1311,c_1356])).

cnf(c_1698,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),X0) = k1_funct_1(k3_struct_0(sK1),X0) ),
    inference(unflattening,[status(thm)],[c_1697])).

cnf(c_1702,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),X0) = k1_funct_1(k3_struct_0(sK1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1698,c_20,c_57,c_60,c_66])).

cnf(c_2019,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),X0_52) = k1_funct_1(k3_struct_0(sK1),X0_52) ),
    inference(subtyping,[status(esa)],[c_1702])).

cnf(c_2359,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),X0_52) = k1_funct_1(k3_struct_0(sK1),X0_52)
    | m1_subset_1(X0_52,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2019])).

cnf(c_3015,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3)) = k1_funct_1(k3_struct_0(sK1),sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3)) ),
    inference(superposition,[status(thm)],[c_2358,c_2359])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1343,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | u1_struct_0(sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_1285])).

cnf(c_1344,plain,
    ( r2_hidden(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1343])).

cnf(c_1808,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | X0 != X1
    | k1_funct_1(k6_relat_1(X2),X1) = X1
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_1344])).

cnf(c_1809,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k1_funct_1(k6_relat_1(u1_struct_0(sK1)),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_1808])).

cnf(c_2027,plain,
    ( ~ m1_subset_1(X0_52,u1_struct_0(sK1))
    | k1_funct_1(k6_relat_1(u1_struct_0(sK1)),X0_52) = X0_52 ),
    inference(subtyping,[status(esa)],[c_1809])).

cnf(c_2351,plain,
    ( k1_funct_1(k6_relat_1(u1_struct_0(sK1)),X0_52) = X0_52
    | m1_subset_1(X0_52,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2027])).

cnf(c_0,plain,
    ( ~ l1_struct_0(X0)
    | k6_relat_1(u1_struct_0(X0)) = k3_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_309,plain,
    ( ~ l1_pre_topc(X0)
    | k6_relat_1(u1_struct_0(X0)) = k3_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_5,c_0])).

cnf(c_1298,plain,
    ( k6_relat_1(u1_struct_0(X0)) = k3_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_309,c_20])).

cnf(c_1299,plain,
    ( k6_relat_1(u1_struct_0(sK1)) = k3_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1298])).

cnf(c_2031,plain,
    ( k6_relat_1(u1_struct_0(sK1)) = k3_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_1299])).

cnf(c_2374,plain,
    ( k1_funct_1(k3_struct_0(sK1),X0_52) = X0_52
    | m1_subset_1(X0_52,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2351,c_2031])).

cnf(c_2904,plain,
    ( k1_funct_1(k3_struct_0(sK1),sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3)) = sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2358,c_2374])).

cnf(c_3016,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3)) = sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3) ),
    inference(light_normalisation,[status(thm)],[c_3015,c_2904])).

cnf(c_10,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,sK0(X1,X2,X0,X3,X4)) != k1_funct_1(X4,sK0(X1,X2,X0,X3,X4)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_671,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X1,X4)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X3,sK0(X2,X4,X1,X3,X0)) != k1_funct_1(X0,sK0(X2,X4,X1,X3,X0))
    | k2_tmap_1(X4,X2,X3,X1) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_672,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(sK3,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X2,X1,X3,X0,sK3)) != k1_funct_1(sK3,sK0(X2,X1,X3,X0,sK3))
    | k2_tmap_1(X1,X2,X0,X3) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_671])).

cnf(c_676,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(sK3,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X2,X1,X3,X0,sK3)) != k1_funct_1(sK3,sK0(X2,X1,X3,X0,sK3))
    | k2_tmap_1(X1,X2,X0,X3) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_672,c_17])).

cnf(c_677,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(sK3,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X2,X1,X3,X0,sK3)) != k1_funct_1(sK3,sK0(X2,X1,X3,X0,sK3))
    | k2_tmap_1(X1,X2,X0,X3) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_676])).

cnf(c_897,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(sK3,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X0,sK0(X2,X1,X3,X0,sK3)) != k1_funct_1(sK3,sK0(X2,X1,X3,X0,sK3))
    | k2_tmap_1(X1,X2,X0,X3) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK2)
    | sK1 != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_677])).

cnf(c_898,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(X1,sK1,sK2,X0,sK3)) != k1_funct_1(sK3,sK0(X1,sK1,sK2,X0,sK3))
    | k2_tmap_1(sK1,X1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_897])).

cnf(c_902,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(X1,sK1,sK2,X0,sK3)) != k1_funct_1(sK3,sK0(X1,sK1,sK2,X0,sK3))
    | k2_tmap_1(sK1,X1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_898,c_22,c_21,c_20,c_19])).

cnf(c_903,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(X1,sK1,sK2,X0,sK3)) != k1_funct_1(sK3,sK0(X1,sK1,sK2,X0,sK3))
    | k2_tmap_1(sK1,X1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_902])).

cnf(c_1221,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(X1),X0,sK0(X1,sK1,sK2,X0,sK3)) != k1_funct_1(sK3,sK0(X1,sK1,sK2,X0,sK3))
    | k2_tmap_1(sK1,X1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_903,c_21])).

cnf(c_1222,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),X0,sK0(sK1,sK1,sK2,X0,sK3)) != k1_funct_1(sK3,sK0(sK1,sK1,sK2,X0,sK3))
    | k2_tmap_1(sK1,sK1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1221])).

cnf(c_1226,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),X0,sK0(sK1,sK1,sK2,X0,sK3)) != k1_funct_1(sK3,sK0(sK1,sK1,sK2,X0,sK3))
    | k2_tmap_1(sK1,sK1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1222,c_22,c_20,c_16,c_15])).

cnf(c_1227,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),X0,sK0(sK1,sK1,sK2,X0,sK3)) != k1_funct_1(sK3,sK0(sK1,sK1,sK2,X0,sK3))
    | k2_tmap_1(sK1,sK1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1226])).

cnf(c_1667,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),X0,sK0(sK1,sK1,sK2,X0,sK3)) != k1_funct_1(sK3,sK0(sK1,sK1,sK2,X0,sK3))
    | k2_tmap_1(sK1,sK1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k3_struct_0(sK1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1311,c_1227])).

cnf(c_1668,plain,
    ( ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3)) != k1_funct_1(sK3,sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3))
    | k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK2) != k4_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_1667])).

cnf(c_1670,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3)) != k1_funct_1(sK3,sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1668,c_22,c_21,c_20,c_57,c_60,c_66,c_890])).

cnf(c_2021,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3)) != k1_funct_1(sK3,sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3)) ),
    inference(subtyping,[status(esa)],[c_1670])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k1_funct_1(sK3,X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_11,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tmap_1(X2,X1,X3,X0),X4)
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | r2_hidden(sK0(X1,X2,X0,X3,X4),u1_struct_0(X0))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_608,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | r2_hidden(sK0(X2,X4,X1,X3,X0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X1,X4)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | k2_tmap_1(X4,X2,X3,X1) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X1) != u1_struct_0(sK2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_13])).

cnf(c_609,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(sK3,u1_struct_0(X3),u1_struct_0(X2))
    | r2_hidden(sK0(X2,X1,X3,X0,sK3),u1_struct_0(X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,X2,X0,X3) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_613,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | r2_hidden(sK0(X2,X1,X3,X0,sK3),u1_struct_0(X3))
    | ~ v1_funct_2(sK3,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(X1,X2,X0,X3) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_17])).

cnf(c_614,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(sK3,u1_struct_0(X3),u1_struct_0(X2))
    | r2_hidden(sK0(X2,X1,X3,X0,sK3),u1_struct_0(X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_tmap_1(X1,X2,X0,X3) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_613])).

cnf(c_945,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(sK3,u1_struct_0(X3),u1_struct_0(X2))
    | r2_hidden(sK0(X2,X1,X3,X0,sK3),u1_struct_0(X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k2_tmap_1(X1,X2,X0,X3) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X2) != u1_struct_0(sK1)
    | u1_struct_0(X3) != u1_struct_0(sK2)
    | sK1 != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_614])).

cnf(c_946,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(X1))
    | r2_hidden(sK0(X1,sK1,sK2,X0,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | k2_tmap_1(sK1,X1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_945])).

cnf(c_950,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(X1))
    | r2_hidden(sK0(X1,sK1,sK2,X0,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | k2_tmap_1(sK1,X1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_946,c_22,c_21,c_20,c_19])).

cnf(c_951,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(X1))
    | r2_hidden(sK0(X1,sK1,sK2,X0,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(sK1,X1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_950])).

cnf(c_1191,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(X1))
    | r2_hidden(sK0(X1,sK1,sK2,X0,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_tmap_1(sK1,X1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_951,c_21])).

cnf(c_1192,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | r2_hidden(sK0(sK1,sK1,sK2,X0,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_tmap_1(sK1,sK1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1191])).

cnf(c_1196,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | r2_hidden(sK0(sK1,sK1,sK2,X0,sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK1,sK1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1192,c_22,c_20,c_16,c_15])).

cnf(c_1197,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
    | r2_hidden(sK0(sK1,sK1,sK2,X0,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK1,sK1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_1196])).

cnf(c_1675,plain,
    ( r2_hidden(sK0(sK1,sK1,sK2,X0,sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k2_tmap_1(sK1,sK1,X0,sK2) != k4_tmap_1(sK1,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k3_struct_0(sK1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1311,c_1197])).

cnf(c_1676,plain,
    ( r2_hidden(sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_struct_0(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ v1_funct_1(k3_struct_0(sK1))
    | k2_tmap_1(sK1,sK1,k3_struct_0(sK1),sK2) != k4_tmap_1(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_1675])).

cnf(c_1678,plain,
    ( r2_hidden(sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1676,c_22,c_21,c_20,c_57,c_60,c_66,c_890])).

cnf(c_1872,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3) != X0
    | k1_funct_1(sK3,X0) = X0
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(resolution_lifted,[status(thm)],[c_14,c_1678])).

cnf(c_1873,plain,
    ( ~ m1_subset_1(sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3),u1_struct_0(sK1))
    | k1_funct_1(sK3,sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3)) = sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3) ),
    inference(unflattening,[status(thm)],[c_1872])).

cnf(c_1875,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3)) = sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1873,c_22,c_21,c_20,c_57,c_60,c_66,c_890,c_1687])).

cnf(c_2014,plain,
    ( k1_funct_1(sK3,sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3)) = sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3) ),
    inference(subtyping,[status(esa)],[c_1875])).

cnf(c_2417,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK1),k3_struct_0(sK1),sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3)) != sK0(sK1,sK1,sK2,k3_struct_0(sK1),sK3) ),
    inference(light_normalisation,[status(thm)],[c_2021,c_2014])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3016,c_2417])).


%------------------------------------------------------------------------------
