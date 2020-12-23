%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2067+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:07 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  267 (1378 expanded)
%              Number of clauses        :  167 ( 265 expanded)
%              Number of leaves         :   22 ( 405 expanded)
%              Depth                    :   23
%              Number of atoms          : 1906 (21580 expanded)
%              Number of equality atoms :   55 (  66 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal clause size      :   42 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f74,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ? [X3] :
                      ( r1_waybel_7(X0,X3,X2)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(X0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(X0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(X0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X4] :
                    ( r1_waybel_7(X0,X4,X2)
                    & r2_hidden(X1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X4) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f62])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r1_waybel_7(X0,X4,X2)
          & r2_hidden(X1,X4)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X4) )
     => ( r1_waybel_7(X0,sK4,X2)
        & r2_hidden(X1,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r1_waybel_7(X0,X3,X2)
                | ~ r2_hidden(X1,X3)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X3) )
            | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & ( ? [X4] :
                ( r1_waybel_7(X0,X4,X2)
                & r2_hidden(X1,X4)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                & ~ v1_xboole_0(X4) )
            | r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ! [X3] :
              ( ~ r1_waybel_7(X0,X3,sK3)
              | ~ r2_hidden(X1,X3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
              | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
              | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              | v1_xboole_0(X3) )
          | ~ r2_hidden(sK3,k2_pre_topc(X0,X1)) )
        & ( ? [X4] :
              ( r1_waybel_7(X0,X4,sK3)
              & r2_hidden(X1,X4)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X4) )
          | r2_hidden(sK3,k2_pre_topc(X0,X1)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(X0,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X4] :
                    ( r1_waybel_7(X0,X4,X2)
                    & r2_hidden(X1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X4) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r1_waybel_7(X0,X3,X2)
                  | ~ r2_hidden(sK2,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  | v1_xboole_0(X3) )
              | ~ r2_hidden(X2,k2_pre_topc(X0,sK2)) )
            & ( ? [X4] :
                  ( r1_waybel_7(X0,X4,X2)
                  & r2_hidden(sK2,X4)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  & ~ v1_xboole_0(X4) )
              | r2_hidden(X2,k2_pre_topc(X0,sK2)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r1_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      | v1_xboole_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ? [X4] :
                      ( r1_waybel_7(X0,X4,X2)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      & ~ v1_xboole_0(X4) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r1_waybel_7(sK1,X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK1)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK1)))
                    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(sK1,X1)) )
              & ( ? [X4] :
                    ( r1_waybel_7(sK1,X4,X2)
                    & r2_hidden(X1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
                    & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK1)))
                    & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK1)))
                    & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
                    & ~ v1_xboole_0(X4) )
                | r2_hidden(X2,k2_pre_topc(sK1,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ( ! [X3] :
          ( ~ r1_waybel_7(sK1,X3,sK3)
          | ~ r2_hidden(sK2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
          | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK1)))
          | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK1)))
          | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
          | v1_xboole_0(X3) )
      | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) )
    & ( ( r1_waybel_7(sK1,sK4,sK3)
        & r2_hidden(sK2,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
        & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1)))
        & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1)))
        & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
        & ~ v1_xboole_0(sK4) )
      | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) )
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f63,f67,f66,f65,f64])).

fof(f101,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f99,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X3] :
                      ( r3_waybel_9(X0,X3,X2)
                      & r1_waybel_0(X0,X3,X1)
                      & l1_waybel_0(X3,X0)
                      & v7_waybel_0(X3)
                      & v4_orders_2(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X4] :
                      ( r3_waybel_9(X0,X4,X2)
                      & r1_waybel_0(X0,X4,X1)
                      & l1_waybel_0(X4,X0)
                      & v7_waybel_0(X4)
                      & v4_orders_2(X4)
                      & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X4,X2)
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r3_waybel_9(X0,sK0(X0,X1,X2),X2)
        & r1_waybel_0(X0,sK0(X0,X1,X2),X1)
        & l1_waybel_0(sK0(X0,X1,X2),X0)
        & v7_waybel_0(sK0(X0,X1,X2))
        & v4_orders_2(sK0(X0,X1,X2))
        & ~ v2_struct_0(sK0(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ( r3_waybel_9(X0,sK0(X0,X1,X2),X2)
                    & r1_waybel_0(X0,sK0(X0,X1,X2),X1)
                    & l1_waybel_0(sK0(X0,X1,X2),X0)
                    & v7_waybel_0(sK0(X0,X1,X2))
                    & v4_orders_2(sK0(X0,X1,X2))
                    & ~ v2_struct_0(sK0(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f58,f59])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r3_waybel_9(X0,X3,X2)
      | ~ r1_waybel_0(X0,X3,X1)
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f100,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f110,plain,
    ( r1_waybel_7(sK1,sK4,sK3)
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f68])).

fof(f103,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f68])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f111,plain,(
    ! [X3] :
      ( ~ r1_waybel_7(sK1,X3,sK3)
      | ~ r2_hidden(sK2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK1)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK1)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
      | v1_xboole_0(X3)
      | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_yellow19(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK0(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,sK0(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK0(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(sK0(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f109,plain,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f68])).

fof(f108,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f68])).

fof(f107,plain,
    ( v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1)))
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f68])).

fof(f106,plain,
    ( v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1)))
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f68])).

fof(f105,plain,
    ( v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f68])).

fof(f104,plain,
    ( ~ v1_xboole_0(sK4)
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f68])).

fof(f102,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_yellow19(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_796,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_40])).

cnf(c_797,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_796])).

cnf(c_1061,plain,
    ( ~ r2_hidden(X0,k2_yellow19(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_797])).

cnf(c_1062,plain,
    ( ~ r2_hidden(X0,k2_yellow19(sK1,X1))
    | ~ l1_waybel_0(X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(X1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1061])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1066,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_waybel_0(X1,sK1)
    | ~ r2_hidden(X0,k2_yellow19(sK1,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1062,c_42])).

cnf(c_1067,plain,
    ( ~ r2_hidden(X0,k2_yellow19(sK1,X1))
    | ~ l1_waybel_0(X1,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_1066])).

cnf(c_17,plain,
    ( r1_waybel_0(X0,X1,X2)
    | ~ r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_21,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | r2_hidden(X2,k2_pre_topc(X0,X3))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_621,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | r2_hidden(X2,k2_pre_topc(X0,X3))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_41])).

cnf(c_622,plain,
    ( ~ r3_waybel_9(sK1,X0,X1)
    | ~ r1_waybel_0(sK1,X0,X2)
    | r2_hidden(X1,k2_pre_topc(sK1,X2))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_626,plain,
    ( ~ r3_waybel_9(sK1,X0,X1)
    | ~ r1_waybel_0(sK1,X0,X2)
    | r2_hidden(X1,k2_pre_topc(sK1,X2))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_622,c_42,c_40])).

cnf(c_852,plain,
    ( ~ r3_waybel_9(sK1,X0,X1)
    | ~ r2_hidden(X2,k2_yellow19(X3,X4))
    | r2_hidden(X1,k2_pre_topc(sK1,X5))
    | ~ l1_waybel_0(X4,X3)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X3)
    | X0 != X4
    | X5 != X2
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_626])).

cnf(c_853,plain,
    ( ~ r3_waybel_9(sK1,X0,X1)
    | ~ r2_hidden(X2,k2_yellow19(sK1,X0))
    | r2_hidden(X1,k2_pre_topc(sK1,X2))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_852])).

cnf(c_131,plain,
    ( l1_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_857,plain,
    ( ~ r3_waybel_9(sK1,X0,X1)
    | ~ r2_hidden(X2,k2_yellow19(sK1,X0))
    | r2_hidden(X1,k2_pre_topc(sK1,X2))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_853,c_42,c_40,c_131])).

cnf(c_1298,plain,
    ( ~ r3_waybel_9(sK1,X0,X1)
    | ~ r2_hidden(X2,k2_yellow19(sK1,X0))
    | r2_hidden(X1,k2_pre_topc(sK1,X2))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1067,c_857])).

cnf(c_8191,plain,
    ( ~ r3_waybel_9(sK1,X0_56,X0_57)
    | ~ r2_hidden(X1_57,k2_yellow19(sK1,X0_56))
    | r2_hidden(X0_57,k2_pre_topc(sK1,X1_57))
    | ~ l1_waybel_0(X0_56,sK1)
    | ~ m1_subset_1(X0_57,u1_struct_0(sK1))
    | ~ v4_orders_2(X0_56)
    | ~ v7_waybel_0(X0_56)
    | v2_struct_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_1298])).

cnf(c_9681,plain,
    ( ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK4),X0_57)
    | ~ r2_hidden(X1_57,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK4)))
    | r2_hidden(X0_57,k2_pre_topc(sK1,X1_57))
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK4),sK1)
    | ~ m1_subset_1(X0_57,u1_struct_0(sK1))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK4))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK4))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK4)) ),
    inference(instantiation,[status(thm)],[c_8191])).

cnf(c_9991,plain,
    ( ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK4),sK3)
    | ~ r2_hidden(X0_57,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK4)))
    | r2_hidden(sK3,k2_pre_topc(sK1,X0_57))
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK4),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK4))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK4))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK4)) ),
    inference(instantiation,[status(thm)],[c_9681])).

cnf(c_9993,plain,
    ( ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK4),sK3)
    | ~ r2_hidden(sK2,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK4)))
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK4),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK4))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK4))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK4)) ),
    inference(instantiation,[status(thm)],[c_9991])).

cnf(c_8246,plain,
    ( ~ r2_hidden(X0_57,X1_57)
    | r2_hidden(X2_57,X3_57)
    | X2_57 != X0_57
    | X3_57 != X1_57 ),
    theory(equality)).

cnf(c_9559,plain,
    ( r2_hidden(X0_57,X1_57)
    | ~ r2_hidden(sK2,sK4)
    | X1_57 != sK4
    | X0_57 != sK2 ),
    inference(instantiation,[status(thm)],[c_8246])).

cnf(c_9726,plain,
    ( r2_hidden(X0_57,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK4)))
    | ~ r2_hidden(sK2,sK4)
    | X0_57 != sK2
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK4)) != sK4 ),
    inference(instantiation,[status(thm)],[c_9559])).

cnf(c_9728,plain,
    ( r2_hidden(sK2,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK4)))
    | ~ r2_hidden(sK2,sK4)
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK4)) != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_9726])).

cnf(c_18,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_31,negated_conjecture,
    ( r1_waybel_7(sK1,sK4,sK3)
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_529,plain,
    ( r3_waybel_9(X0,X1,X2)
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | k2_yellow19(X0,X1) != sK4
    | sK3 != X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_31])).

cnf(c_530,plain,
    ( r3_waybel_9(sK1,X0,sK3)
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k2_yellow19(sK1,X0) != sK4 ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_534,plain,
    ( r3_waybel_9(sK1,X0,sK3)
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ l1_waybel_0(X0,sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK1,X0) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_42,c_41,c_40,c_38])).

cnf(c_8213,plain,
    ( r3_waybel_9(sK1,X0_56,sK3)
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ l1_waybel_0(X0_56,sK1)
    | ~ v4_orders_2(X0_56)
    | ~ v7_waybel_0(X0_56)
    | v2_struct_0(X0_56)
    | k2_yellow19(sK1,X0_56) != sK4 ),
    inference(subtyping,[status(esa)],[c_534])).

cnf(c_9679,plain,
    ( r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK4),sK3)
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK4),sK1)
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK4))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK4))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK4))
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK4)) != sK4 ),
    inference(instantiation,[status(thm)],[c_8213])).

cnf(c_20,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1031,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_797])).

cnf(c_1032,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v1_xboole_0(X0)
    | v2_struct_0(sK1)
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_1031])).

cnf(c_1036,plain,
    ( v1_xboole_0(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
    | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1032,c_42])).

cnf(c_1037,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v1_xboole_0(X0)
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) = X0 ),
    inference(renaming,[status(thm)],[c_1036])).

cnf(c_8199,plain,
    ( ~ v1_subset_1(X0_57,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    | ~ v2_waybel_0(X0_57,k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(X0_57,k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v1_xboole_0(X0_57)
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0_57)) = X0_57 ),
    inference(subtyping,[status(esa)],[c_1037])).

cnf(c_9541,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    | ~ v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v1_xboole_0(sK4)
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_8199])).

cnf(c_13,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1121,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_797])).

cnf(c_1122,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v7_waybel_0(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1121])).

cnf(c_1126,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v7_waybel_0(k3_yellow19(sK1,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1122,c_42])).

cnf(c_1127,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v7_waybel_0(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1126])).

cnf(c_8195,plain,
    ( ~ v1_subset_1(X0_57,u1_struct_0(k3_yellow_1(X1_57)))
    | ~ v2_waybel_0(X0_57,k3_yellow_1(X1_57))
    | ~ v13_waybel_0(X0_57,k3_yellow_1(X1_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1_57))))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | v7_waybel_0(k3_yellow19(sK1,X1_57,X0_57))
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1127])).

cnf(c_9529,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    | ~ v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK4))
    | v1_xboole_0(k2_struct_0(sK1))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_8195])).

cnf(c_10,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1157,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_797])).

cnf(c_1158,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1157])).

cnf(c_1162,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v4_orders_2(k3_yellow19(sK1,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1158,c_42])).

cnf(c_1163,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1162])).

cnf(c_8194,plain,
    ( ~ v2_waybel_0(X0_57,k3_yellow_1(X1_57))
    | ~ v13_waybel_0(X0_57,k3_yellow_1(X1_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1_57))))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,X1_57,X0_57))
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1163])).

cnf(c_9530,plain,
    ( ~ v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK4))
    | v1_xboole_0(k2_struct_0(sK1))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_8194])).

cnf(c_4,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1190,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_797])).

cnf(c_1191,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1190])).

cnf(c_1195,plain,
    ( ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1191,c_42])).

cnf(c_1196,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK1,X1,X0)) ),
    inference(renaming,[status(thm)],[c_1195])).

cnf(c_8193,plain,
    ( ~ v2_waybel_0(X0_57,k3_yellow_1(X1_57))
    | ~ v13_waybel_0(X0_57,k3_yellow_1(X1_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1_57))))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X0_57)
    | ~ v2_struct_0(k3_yellow19(sK1,X1_57,X0_57)) ),
    inference(subtyping,[status(esa)],[c_1196])).

cnf(c_9531,plain,
    ( ~ v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v1_xboole_0(k2_struct_0(sK1))
    | v1_xboole_0(sK4)
    | ~ v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK4)) ),
    inference(instantiation,[status(thm)],[c_8193])).

cnf(c_3,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1223,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_797])).

cnf(c_1224,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | l1_waybel_0(k3_yellow19(sK1,X1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1223])).

cnf(c_1228,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | l1_waybel_0(k3_yellow19(sK1,X1,X0),sK1)
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1224,c_42])).

cnf(c_1229,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | l1_waybel_0(k3_yellow19(sK1,X1,X0),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1228])).

cnf(c_8192,plain,
    ( ~ v2_waybel_0(X0_57,k3_yellow_1(X1_57))
    | ~ v13_waybel_0(X0_57,k3_yellow_1(X1_57))
    | l1_waybel_0(k3_yellow19(sK1,X1_57,X0_57),sK1)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1_57))))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1229])).

cnf(c_9532,plain,
    ( ~ v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1)))
    | l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK4),sK1)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v1_xboole_0(k2_struct_0(sK1))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_8192])).

cnf(c_2,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k2_yellow19(X1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1102,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k2_yellow19(X1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_797])).

cnf(c_1103,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | m1_subset_1(k2_yellow19(sK1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1102])).

cnf(c_1107,plain,
    ( v2_struct_0(X0)
    | m1_subset_1(k2_yellow19(sK1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | ~ l1_waybel_0(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1103,c_42])).

cnf(c_1108,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | m1_subset_1(k2_yellow19(sK1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1107])).

cnf(c_6,plain,
    ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1005,plain,
    ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_797])).

cnf(c_1006,plain,
    ( v13_waybel_0(k2_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1)))
    | ~ l1_waybel_0(X0,sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1005])).

cnf(c_1010,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK1)
    | v13_waybel_0(k2_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1006,c_42])).

cnf(c_1011,plain,
    ( v13_waybel_0(k2_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1)))
    | ~ l1_waybel_0(X0,sK1)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_1010])).

cnf(c_8,plain,
    ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_980,plain,
    ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_797])).

cnf(c_981,plain,
    ( v2_waybel_0(k2_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1)))
    | ~ l1_waybel_0(X0,sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_980])).

cnf(c_985,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK1)
    | v2_waybel_0(k2_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_981,c_42])).

cnf(c_986,plain,
    ( v2_waybel_0(k2_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1)))
    | ~ l1_waybel_0(X0,sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_985])).

cnf(c_9,plain,
    ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_955,plain,
    ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
    | ~ l1_waybel_0(X1,X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_797])).

cnf(c_956,plain,
    ( v1_subset_1(k2_yellow19(sK1,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    | ~ l1_waybel_0(X0,sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_955])).

cnf(c_960,plain,
    ( v2_struct_0(X0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK1)
    | v1_subset_1(k2_yellow19(sK1,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_956,c_42])).

cnf(c_961,plain,
    ( v1_subset_1(k2_yellow19(sK1,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    | ~ l1_waybel_0(X0,sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_960])).

cnf(c_19,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_30,negated_conjecture,
    ( ~ r1_waybel_7(sK1,X0,sK3)
    | ~ r2_hidden(sK2,X0)
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_479,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r2_hidden(sK2,X3)
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK1)))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v1_xboole_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | k2_yellow19(X0,X1) != X3
    | sK3 != X2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_480,plain,
    ( ~ r3_waybel_9(sK1,X0,sK3)
    | ~ r2_hidden(sK2,k2_yellow19(sK1,X0))
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ v1_subset_1(k2_yellow19(sK1,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    | ~ v2_waybel_0(k2_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(k2_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1)))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k2_yellow19(sK1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v1_xboole_0(k2_yellow19(sK1,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_484,plain,
    ( ~ r3_waybel_9(sK1,X0,sK3)
    | ~ r2_hidden(sK2,k2_yellow19(sK1,X0))
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ v1_subset_1(k2_yellow19(sK1,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    | ~ v2_waybel_0(k2_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(k2_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1)))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k2_yellow19(sK1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v1_xboole_0(k2_yellow19(sK1,X0))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_480,c_42,c_41,c_40,c_38])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_514,plain,
    ( ~ r3_waybel_9(sK1,X0,sK3)
    | ~ r2_hidden(sK2,k2_yellow19(sK1,X0))
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ v1_subset_1(k2_yellow19(sK1,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    | ~ v2_waybel_0(k2_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(k2_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1)))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k2_yellow19(sK1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_484,c_29])).

cnf(c_1259,plain,
    ( ~ r3_waybel_9(sK1,X0,sK3)
    | ~ r2_hidden(sK2,k2_yellow19(sK1,X0))
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ v2_waybel_0(k2_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(k2_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1)))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k2_yellow19(sK1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_961,c_514])).

cnf(c_1269,plain,
    ( ~ r3_waybel_9(sK1,X0,sK3)
    | ~ r2_hidden(sK2,k2_yellow19(sK1,X0))
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ v13_waybel_0(k2_yellow19(sK1,X0),k3_yellow_1(k2_struct_0(sK1)))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k2_yellow19(sK1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_986,c_1259])).

cnf(c_1279,plain,
    ( ~ r3_waybel_9(sK1,X0,sK3)
    | ~ r2_hidden(sK2,k2_yellow19(sK1,X0))
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(k2_yellow19(sK1,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1011,c_1269])).

cnf(c_1310,plain,
    ( ~ r3_waybel_9(sK1,X0,sK3)
    | ~ r2_hidden(sK2,k2_yellow19(sK1,X0))
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ l1_waybel_0(X0,sK1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v2_struct_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1108,c_1279])).

cnf(c_8190,plain,
    ( ~ r3_waybel_9(sK1,X0_56,sK3)
    | ~ r2_hidden(sK2,k2_yellow19(sK1,X0_56))
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ l1_waybel_0(X0_56,sK1)
    | ~ v4_orders_2(X0_56)
    | ~ v7_waybel_0(X0_56)
    | v2_struct_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_1310])).

cnf(c_9501,plain,
    ( ~ r3_waybel_9(sK1,sK0(sK1,X0_57,sK3),sK3)
    | ~ r2_hidden(sK2,k2_yellow19(sK1,sK0(sK1,X0_57,sK3)))
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ l1_waybel_0(sK0(sK1,X0_57,sK3),sK1)
    | ~ v4_orders_2(sK0(sK1,X0_57,sK3))
    | ~ v7_waybel_0(sK0(sK1,X0_57,sK3))
    | v2_struct_0(sK0(sK1,X0_57,sK3)) ),
    inference(instantiation,[status(thm)],[c_8190])).

cnf(c_9513,plain,
    ( ~ r3_waybel_9(sK1,sK0(sK1,sK2,sK3),sK3)
    | ~ r2_hidden(sK2,k2_yellow19(sK1,sK0(sK1,sK2,sK3)))
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ l1_waybel_0(sK0(sK1,sK2,sK3),sK1)
    | ~ v4_orders_2(sK0(sK1,sK2,sK3))
    | ~ v7_waybel_0(sK0(sK1,sK2,sK3))
    | v2_struct_0(sK0(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_9501])).

cnf(c_15,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | r2_hidden(X2,k2_yellow19(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_23,plain,
    ( r1_waybel_0(X0,sK0(X0,X1,X2),X1)
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_573,plain,
    ( r1_waybel_0(X0,sK0(X0,X1,X2),X1)
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_41])).

cnf(c_574,plain,
    ( r1_waybel_0(sK1,sK0(sK1,X0,X1),X0)
    | ~ r2_hidden(X1,k2_pre_topc(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_578,plain,
    ( r1_waybel_0(sK1,sK0(sK1,X0,X1),X0)
    | ~ r2_hidden(X1,k2_pre_topc(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_574,c_42,c_40])).

cnf(c_821,plain,
    ( r2_hidden(X0,k2_yellow19(X1,X2))
    | ~ r2_hidden(X3,k2_pre_topc(sK1,X4))
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | X4 != X0
    | sK0(sK1,X4,X3) != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_578])).

cnf(c_822,plain,
    ( r2_hidden(X0,k2_yellow19(sK1,sK0(sK1,X0,X1)))
    | ~ r2_hidden(X1,k2_pre_topc(sK1,X0))
    | ~ l1_waybel_0(sK0(sK1,X0,X1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK0(sK1,X0,X1))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_821])).

cnf(c_826,plain,
    ( r2_hidden(X0,k2_yellow19(sK1,sK0(sK1,X0,X1)))
    | ~ r2_hidden(X1,k2_pre_topc(sK1,X0))
    | ~ l1_waybel_0(sK0(sK1,X0,X1),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK0(sK1,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_822,c_42,c_40,c_131])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X2,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_660,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X2,X0))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_41])).

cnf(c_661,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v2_struct_0(sK0(sK1,X1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_665,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v2_struct_0(sK0(sK1,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_661,c_42,c_40])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | l1_waybel_0(sK0(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_732,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | l1_waybel_0(sK0(X1,X2,X0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_41])).

cnf(c_733,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK1,X1))
    | l1_waybel_0(sK0(sK1,X1,X0),sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_737,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK1,X1))
    | l1_waybel_0(sK0(sK1,X1,X0),sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_42,c_40])).

cnf(c_844,plain,
    ( r2_hidden(X0,k2_yellow19(sK1,sK0(sK1,X0,X1)))
    | ~ r2_hidden(X1,k2_pre_topc(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_826,c_665,c_737])).

cnf(c_8206,plain,
    ( r2_hidden(X0_57,k2_yellow19(sK1,sK0(sK1,X0_57,X1_57)))
    | ~ r2_hidden(X1_57,k2_pre_topc(sK1,X0_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_844])).

cnf(c_9371,plain,
    ( r2_hidden(X0_57,k2_yellow19(sK1,sK0(sK1,X0_57,sK3)))
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,X0_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_8206])).

cnf(c_9373,plain,
    ( r2_hidden(sK2,k2_yellow19(sK1,sK0(sK1,sK2,sK3)))
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_9371])).

cnf(c_22,plain,
    ( r3_waybel_9(X0,sK0(X0,X1,X2),X2)
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_597,plain,
    ( r3_waybel_9(X0,sK0(X0,X1,X2),X2)
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_41])).

cnf(c_598,plain,
    ( r3_waybel_9(sK1,sK0(sK1,X0,X1),X1)
    | ~ r2_hidden(X1,k2_pre_topc(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_602,plain,
    ( r3_waybel_9(sK1,sK0(sK1,X0,X1),X1)
    | ~ r2_hidden(X1,k2_pre_topc(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_598,c_42,c_40])).

cnf(c_8212,plain,
    ( r3_waybel_9(sK1,sK0(sK1,X0_57,X1_57),X1_57)
    | ~ r2_hidden(X1_57,k2_pre_topc(sK1,X0_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_57,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_602])).

cnf(c_9361,plain,
    ( r3_waybel_9(sK1,sK0(sK1,X0_57,sK3),sK3)
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,X0_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_8212])).

cnf(c_9363,plain,
    ( r3_waybel_9(sK1,sK0(sK1,sK2,sK3),sK3)
    | ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_9361])).

cnf(c_8211,plain,
    ( ~ r2_hidden(X0_57,k2_pre_topc(sK1,X1_57))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK1))
    | ~ v2_struct_0(sK0(sK1,X1_57,X0_57)) ),
    inference(subtyping,[status(esa)],[c_665])).

cnf(c_9356,plain,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK1,X0_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v2_struct_0(sK0(sK1,X0_57,sK3)) ),
    inference(instantiation,[status(thm)],[c_8211])).

cnf(c_9358,plain,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v2_struct_0(sK0(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_9356])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v4_orders_2(sK0(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_684,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v4_orders_2(sK0(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_41])).

cnf(c_685,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v4_orders_2(sK0(sK1,X1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_689,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v4_orders_2(sK0(sK1,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_685,c_42,c_40])).

cnf(c_8210,plain,
    ( ~ r2_hidden(X0_57,k2_pre_topc(sK1,X1_57))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK1))
    | v4_orders_2(sK0(sK1,X1_57,X0_57)) ),
    inference(subtyping,[status(esa)],[c_689])).

cnf(c_9351,plain,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK1,X0_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v4_orders_2(sK0(sK1,X0_57,sK3)) ),
    inference(instantiation,[status(thm)],[c_8210])).

cnf(c_9353,plain,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v4_orders_2(sK0(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_9351])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v7_waybel_0(sK0(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_708,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_waybel_0(sK0(X1,X2,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_41])).

cnf(c_709,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v7_waybel_0(sK0(sK1,X1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_708])).

cnf(c_713,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK1,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v7_waybel_0(sK0(sK1,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_709,c_42,c_40])).

cnf(c_8209,plain,
    ( ~ r2_hidden(X0_57,k2_pre_topc(sK1,X1_57))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK1))
    | v7_waybel_0(sK0(sK1,X1_57,X0_57)) ),
    inference(subtyping,[status(esa)],[c_713])).

cnf(c_9346,plain,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK1,X0_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v7_waybel_0(sK0(sK1,X0_57,sK3)) ),
    inference(instantiation,[status(thm)],[c_8209])).

cnf(c_9348,plain,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v7_waybel_0(sK0(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_9346])).

cnf(c_8208,plain,
    ( ~ r2_hidden(X0_57,k2_pre_topc(sK1,X1_57))
    | l1_waybel_0(sK0(sK1,X1_57,X0_57),sK1)
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_57,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_737])).

cnf(c_9341,plain,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK1,X0_57))
    | l1_waybel_0(sK0(sK1,X0_57,sK3),sK1)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_8208])).

cnf(c_9343,plain,
    ( ~ r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | l1_waybel_0(sK0(sK1,sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_9341])).

cnf(c_8227,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_8270,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_8227])).

cnf(c_1,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_141,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(k2_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_110,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK2,sK4)
    | r2_hidden(sK3,k2_pre_topc(sK1,sK2)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_33,negated_conjecture,
    ( r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_34,negated_conjecture,
    ( r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_35,negated_conjecture,
    ( r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_36,negated_conjecture,
    ( r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_37,negated_conjecture,
    ( r2_hidden(sK3,k2_pre_topc(sK1,sK2))
    | ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9993,c_9728,c_9679,c_9541,c_9529,c_9530,c_9531,c_9532,c_9513,c_9373,c_9363,c_9358,c_9353,c_9348,c_9343,c_8270,c_141,c_131,c_110,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_42])).


%------------------------------------------------------------------------------
