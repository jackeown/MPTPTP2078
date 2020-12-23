%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:23 EST 2020

% Result     : Theorem 1.45s
% Output     : CNFRefutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  194 (1255 expanded)
%              Number of clauses        :  113 ( 181 expanded)
%              Number of leaves         :   14 ( 400 expanded)
%              Depth                    :   29
%              Number of atoms          : 1442 (20978 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal clause size      :   48 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r1_waybel_7(X0,X2,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_hidden(X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r1_waybel_7(X0,X2,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_hidden(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X2) ) )
      & ( ! [X2] :
            ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r1_waybel_7(X0,X2,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
            | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
            | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            | v1_xboole_0(X2) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X3,X0)
                & r1_waybel_7(X1,X2,X3)
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & r2_hidden(X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            & ~ v1_xboole_0(X2) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r1_waybel_7(X1,X4,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r2_hidden(X0,X4)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
            | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
            | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
            | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            | v1_xboole_0(X4) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X0)
          & r1_waybel_7(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_hidden(sK5(X0,X1),X0)
        & r1_waybel_7(X1,X2,sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X0)
              & r1_waybel_7(X1,X2,X3)
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & r2_hidden(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
          & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
          & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
          & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X0)
            & r1_waybel_7(X1,sK4(X0,X1),X3)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & r2_hidden(X0,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
        & v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1)))
        & v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1)))
        & v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
        & ~ v1_xboole_0(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X0)
          & r1_waybel_7(X1,sK4(X0,X1),sK5(X0,X1))
          & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))
          & r2_hidden(X0,sK4(X0,X1))
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
          & v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1)))
          & v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1)))
          & v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
          & ~ v1_xboole_0(sK4(X0,X1)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(X5,X0)
                | ~ r1_waybel_7(X1,X4,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            | ~ r2_hidden(X0,X4)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
            | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
            | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
            | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            | v1_xboole_0(X4) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f29,f28])).

fof(f57,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X0)
      | ~ r1_waybel_7(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_hidden(X0,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
      | v1_xboole_0(X4)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
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

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r1_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r1_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      | v1_xboole_0(X3) ) )
                & ( ? [X3] :
                      ( r1_waybel_7(X0,X3,X2)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      & ~ v1_xboole_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r1_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      | v1_xboole_0(X3) ) )
                & ( ? [X4] :
                      ( r1_waybel_7(X0,X4,X2)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      & ~ v1_xboole_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_waybel_7(X0,X4,X2)
          & r2_hidden(X1,X4)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X4) )
     => ( r1_waybel_7(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(X1,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK2(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK2(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r1_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                      | v1_xboole_0(X3) ) )
                & ( ( r1_waybel_7(X0,sK2(X0,X1,X2),X2)
                    & r2_hidden(X1,sK2(X0,X1,X2))
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v1_subset_1(sK2(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                    & ~ v1_xboole_0(sK2(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_7(X0,sK2(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK2(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v13_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_subset_1(sK2(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & ~ v1_xboole_0(X2) )
               => ( r2_hidden(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_waybel_7(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X2) )
                 => ( r2_hidden(X1,X2)
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r2_waybel_7(X0,X2,X3)
                         => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r2_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r2_waybel_7(X0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f32])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_waybel_7(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK9,X1)
        & r2_waybel_7(X0,X2,sK9)
        & m1_subset_1(sK9,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_waybel_7(X0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_hidden(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
          & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r2_waybel_7(X0,sK8,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & r2_hidden(X1,sK8)
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(X0)))
        & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r2_waybel_7(X0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X3,sK7)
                  & r2_waybel_7(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_hidden(sK7,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
              & ~ v1_xboole_0(X2) )
          | ~ v4_pre_topc(sK7,X0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,sK7)
                  | ~ r2_waybel_7(X0,X4,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ r2_hidden(sK7,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
              | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
              | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
              | v1_xboole_0(X4) )
          | v4_pre_topc(sK7,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r2_waybel_7(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_hidden(X1,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & ~ v1_xboole_0(X2) )
              | ~ v4_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r2_waybel_7(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X4)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                  | v1_xboole_0(X4) )
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r2_waybel_7(sK6,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK6)) )
                & r2_hidden(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
                & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK6)))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
                & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6)))
                & ~ v1_xboole_0(X2) )
            | ~ v4_pre_topc(X1,sK6) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r2_waybel_7(sK6,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(sK6)) )
                | ~ r2_hidden(X1,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
                | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK6)))
                | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
                | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
                | v1_xboole_0(X4) )
            | v4_pre_topc(X1,sK6) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ( ~ r2_hidden(sK9,sK7)
        & r2_waybel_7(sK6,sK8,sK9)
        & m1_subset_1(sK9,u1_struct_0(sK6))
        & r2_hidden(sK7,sK8)
        & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
        & v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6)))
        & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
        & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
        & ~ v1_xboole_0(sK8) )
      | ~ v4_pre_topc(sK7,sK6) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,sK7)
              | ~ r2_waybel_7(sK6,X4,X5)
              | ~ m1_subset_1(X5,u1_struct_0(sK6)) )
          | ~ r2_hidden(sK7,X4)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
          | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK6)))
          | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
          | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
          | v1_xboole_0(X4) )
      | v4_pre_topc(sK7,sK6) )
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f33,f37,f36,f35,f34])).

fof(f70,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
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
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r2_waybel_7(X0,X3,X2)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X3) ) )
                & ( ? [X3] :
                      ( r2_waybel_7(X0,X3,X2)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & ~ v1_xboole_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X3) ) )
                & ( ? [X4] :
                      ( r2_waybel_7(X0,X4,X2)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
                      & ~ v1_xboole_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_waybel_7(X0,X4,X2)
          & r2_hidden(X1,X4)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0)))
          & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X4) )
     => ( r2_waybel_7(X0,sK3(X0,X1,X2),X2)
        & r2_hidden(X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v3_waybel_7(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v13_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r2_waybel_7(X0,X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X3) ) )
                & ( ( r2_waybel_7(X0,sK3(X0,X1,X2),X2)
                    & r2_hidden(X1,sK3(X0,X1,X2))
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v3_waybel_7(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v13_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(sK3(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK3(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v13_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v3_waybel_7(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,sK3(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK7)
      | ~ r2_waybel_7(sK6,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK6))
      | ~ r2_hidden(sK7,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
      | ~ v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK6)))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6)))
      | v1_xboole_0(X4)
      | v4_pre_topc(sK7,sK6) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK3(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK2(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v4_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v4_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                  & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                  & ~ v1_xboole_0(X2) )
               => ( r2_hidden(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_waybel_7(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_waybel_7(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_hidden(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
                | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                | v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f11,f15,f14])).

fof(f67,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r1_waybel_7(X0,X3,X2)
      | ~ r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r1_waybel_7(X1,sK4(X0,X1),sK5(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ v1_xboole_0(sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_waybel_7(X0,X3,X2)
      | ~ r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,
    ( r2_waybel_7(sK6,sK8,sK9)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,
    ( ~ v1_xboole_0(sK8)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,
    ( v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,
    ( v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,
    ( v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(X0,sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,
    ( ~ r2_hidden(sK9,sK7)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,
    ( r2_hidden(sK7,sK8)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_27,plain,
    ( ~ r1_waybel_7(X0,X1,X2)
    | ~ sP0(X3,X0)
    | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
    | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(X2,X3)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1,plain,
    ( r1_waybel_7(X0,sK2(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_521,plain,
    ( ~ sP0(X0,X1)
    | ~ v1_subset_1(sK2(X1,X2,X3),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(sK2(X1,X2,X3),k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(sK2(X1,X2,X3),k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(sK2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | r2_hidden(X3,X0)
    | ~ r2_hidden(X0,sK2(X1,X2,X3))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(sK2(X1,X2,X3)) ),
    inference(resolution,[status(thm)],[c_27,c_1])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(sK2(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4,plain,
    ( v13_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5,plain,
    ( v2_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6,plain,
    ( v1_subset_1(sK2(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_553,plain,
    ( ~ sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X3,X0)
    | ~ r2_hidden(X0,sK2(X1,X2,X3))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_521,c_7,c_3,c_4,c_5,c_6])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1078,plain,
    ( ~ sP0(X0,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X0,sK2(sK6,X1,X2))
    | ~ r2_hidden(X2,k2_pre_topc(sK6,X1))
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_553,c_40])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1082,plain,
    ( ~ sP0(X0,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2,u1_struct_0(sK6))
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X0,sK2(sK6,X1,X2))
    | ~ r2_hidden(X2,k2_pre_topc(sK6,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1078,c_42,c_41])).

cnf(c_2268,plain,
    ( ~ sP0(X0_56,sK6)
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X2_56,u1_struct_0(sK6))
    | r2_hidden(X2_56,X0_56)
    | ~ r2_hidden(X0_56,sK2(sK6,X1_56,X2_56))
    | ~ r2_hidden(X2_56,k2_pre_topc(sK6,X1_56)) ),
    inference(subtyping,[status(esa)],[c_1082])).

cnf(c_2450,plain,
    ( ~ sP0(X0_56,sK6)
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ r2_hidden(X0_56,sK2(sK6,X1_56,sK9))
    | r2_hidden(sK9,X0_56)
    | ~ r2_hidden(sK9,k2_pre_topc(sK6,X1_56)) ),
    inference(instantiation,[status(thm)],[c_2268])).

cnf(c_2452,plain,
    ( ~ sP0(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ r2_hidden(sK7,sK2(sK6,sK7,sK9))
    | ~ r2_hidden(sK9,k2_pre_topc(sK6,sK7))
    | r2_hidden(sK9,sK7) ),
    inference(instantiation,[status(thm)],[c_2450])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1107,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_11,c_40])).

cnf(c_1111,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1107,c_42,c_41])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(sK3(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_14,plain,
    ( v2_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_13,plain,
    ( v13_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_12,plain,
    ( v3_waybel_7(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9,plain,
    ( r2_waybel_7(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_38,negated_conjecture,
    ( ~ r2_waybel_7(sK6,X0,X1)
    | v4_pre_topc(sK7,sK6)
    | ~ v3_waybel_7(X0,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_760,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ v3_waybel_7(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v13_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | v1_xboole_0(sK3(sK6,X0,X1)) ),
    inference(resolution,[status(thm)],[c_9,c_38])).

cnf(c_764,plain,
    ( ~ r2_hidden(sK7,sK3(sK6,X0,X1))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v13_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v3_waybel_7(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6)
    | v1_xboole_0(sK3(sK6,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_760,c_42,c_41,c_40])).

cnf(c_765,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ v3_waybel_7(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v13_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
    | v1_xboole_0(sK3(sK6,X0,X1)) ),
    inference(renaming,[status(thm)],[c_764])).

cnf(c_821,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v13_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | v1_xboole_0(sK3(sK6,X0,X1)) ),
    inference(resolution,[status(thm)],[c_12,c_765])).

cnf(c_825,plain,
    ( ~ r2_hidden(sK7,sK3(sK6,X0,X1))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v13_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6)
    | v1_xboole_0(sK3(sK6,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_821,c_42,c_41,c_40])).

cnf(c_826,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ v13_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
    | v1_xboole_0(sK3(sK6,X0,X1)) ),
    inference(renaming,[status(thm)],[c_825])).

cnf(c_873,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | v1_xboole_0(sK3(sK6,X0,X1)) ),
    inference(resolution,[status(thm)],[c_13,c_826])).

cnf(c_877,plain,
    ( ~ r2_hidden(sK7,sK3(sK6,X0,X1))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6)
    | v1_xboole_0(sK3(sK6,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_873,c_42,c_41,c_40])).

cnf(c_878,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
    | v1_xboole_0(sK3(sK6,X0,X1)) ),
    inference(renaming,[status(thm)],[c_877])).

cnf(c_921,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | v1_xboole_0(sK3(sK6,X0,X1)) ),
    inference(resolution,[status(thm)],[c_14,c_878])).

cnf(c_925,plain,
    ( ~ r2_hidden(sK7,sK3(sK6,X0,X1))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6)
    | v1_xboole_0(sK3(sK6,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_921,c_42,c_41,c_40])).

cnf(c_926,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
    | v1_xboole_0(sK3(sK6,X0,X1)) ),
    inference(renaming,[status(thm)],[c_925])).

cnf(c_965,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_15,c_926])).

cnf(c_969,plain,
    ( ~ r2_hidden(sK7,sK3(sK6,X0,X1))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | v4_pre_topc(sK7,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_965,c_42,c_41,c_40])).

cnf(c_970,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK3(sK6,X0,X1)) ),
    inference(renaming,[status(thm)],[c_969])).

cnf(c_1245,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | r2_hidden(X1,sK7)
    | ~ r2_hidden(sK7,sK3(sK6,X0,X1)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1111,c_970])).

cnf(c_2265,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
    | ~ r2_hidden(X1_56,k2_pre_topc(sK6,X0_56))
    | r2_hidden(X1_56,sK7)
    | ~ r2_hidden(sK7,sK3(sK6,X0_56,X1_56)) ),
    inference(subtyping,[status(esa)],[c_1245])).

cnf(c_2397,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK5(X1_56,sK6),u1_struct_0(sK6))
    | ~ r2_hidden(sK5(X1_56,sK6),k2_pre_topc(sK6,X0_56))
    | r2_hidden(sK5(X1_56,sK6),sK7)
    | ~ r2_hidden(sK7,sK3(sK6,X0_56,sK5(X1_56,sK6))) ),
    inference(instantiation,[status(thm)],[c_2265])).

cnf(c_2411,plain,
    ( v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(sK5(sK7,sK6),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK5(sK7,sK6),k2_pre_topc(sK6,sK7))
    | r2_hidden(sK5(sK7,sK6),sK7)
    | ~ r2_hidden(sK7,sK3(sK6,sK7,sK5(sK7,sK6))) ),
    inference(instantiation,[status(thm)],[c_2397])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X0,sK3(X1,X0,X2))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1130,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X0,sK3(sK6,X0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_10,c_40])).

cnf(c_1134,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X0,sK3(sK6,X0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1130,c_42,c_41])).

cnf(c_2267,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
    | r2_hidden(X0_56,sK3(sK6,X0_56,X1_56))
    | ~ r2_hidden(X1_56,k2_pre_topc(sK6,X0_56)) ),
    inference(subtyping,[status(esa)],[c_1134])).

cnf(c_2398,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK5(X1_56,sK6),u1_struct_0(sK6))
    | r2_hidden(X0_56,sK3(sK6,X0_56,sK5(X1_56,sK6)))
    | ~ r2_hidden(sK5(X1_56,sK6),k2_pre_topc(sK6,X0_56)) ),
    inference(instantiation,[status(thm)],[c_2267])).

cnf(c_2407,plain,
    ( ~ m1_subset_1(sK5(sK7,sK6),u1_struct_0(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK5(sK7,sK6),k2_pre_topc(sK6,sK7))
    | r2_hidden(sK7,sK3(sK6,sK7,sK5(sK7,sK6))) ),
    inference(instantiation,[status(thm)],[c_2398])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X0,sK2(X1,X0,X2))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1176,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X0,sK2(sK6,X0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_2,c_40])).

cnf(c_1180,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | r2_hidden(X0,sK2(sK6,X0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1176,c_42,c_41])).

cnf(c_2266,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
    | r2_hidden(X0_56,sK2(sK6,X0_56,X1_56))
    | ~ r2_hidden(X1_56,k2_pre_topc(sK6,X0_56)) ),
    inference(subtyping,[status(esa)],[c_1180])).

cnf(c_2375,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | r2_hidden(X0_56,sK2(sK6,X0_56,sK9))
    | ~ r2_hidden(sK9,k2_pre_topc(sK6,X0_56)) ),
    inference(instantiation,[status(thm)],[c_2266])).

cnf(c_2377,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | r2_hidden(sK7,sK2(sK6,sK7,sK9))
    | ~ r2_hidden(sK9,k2_pre_topc(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_2375])).

cnf(c_16,plain,
    ( ~ sP1(X0,X1)
    | ~ sP0(X1,X0)
    | v4_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_28,plain,
    ( sP1(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1199,plain,
    ( sP1(sK6,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_28,c_40])).

cnf(c_1203,plain,
    ( sP1(sK6,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1199,c_42,c_41])).

cnf(c_1283,plain,
    ( ~ sP0(X0,sK6)
    | v4_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(resolution,[status(thm)],[c_16,c_1203])).

cnf(c_2263,plain,
    ( ~ sP0(X0_56,sK6)
    | v4_pre_topc(X0_56,sK6)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_1283])).

cnf(c_2319,plain,
    ( ~ sP0(sK7,sK6)
    | v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_2263])).

cnf(c_17,plain,
    ( ~ sP1(X0,X1)
    | sP0(X1,X0)
    | ~ v4_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1269,plain,
    ( sP0(X0,sK6)
    | ~ v4_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(resolution,[status(thm)],[c_17,c_1203])).

cnf(c_2264,plain,
    ( sP0(X0_56,sK6)
    | ~ v4_pre_topc(X0_56,sK6)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(subtyping,[status(esa)],[c_1269])).

cnf(c_2316,plain,
    ( sP0(sK7,sK6)
    | ~ v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_2264])).

cnf(c_0,plain,
    ( ~ r1_waybel_7(X0,X1,X2)
    | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
    | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(X2,k2_pre_topc(X0,X3))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,plain,
    ( r1_waybel_7(X0,sK4(X1,X0),sK5(X1,X0))
    | sP0(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_633,plain,
    ( sP0(X0,X1)
    | ~ v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ m1_subset_1(sK5(X0,X1),u1_struct_0(X1))
    | ~ r2_hidden(X2,sK4(X0,X1))
    | r2_hidden(sK5(X0,X1),k2_pre_topc(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(sK4(X0,X1)) ),
    inference(resolution,[status(thm)],[c_0,c_19])).

cnf(c_26,plain,
    ( sP0(X0,X1)
    | ~ v1_xboole_0(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,plain,
    ( sP0(X0,X1)
    | v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,plain,
    ( sP0(X0,X1)
    | v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_23,plain,
    ( sP0(X0,X1)
    | v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,plain,
    ( sP0(X0,X1)
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_637,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | r2_hidden(sK5(X0,X1),k2_pre_topc(X1,X2))
    | ~ r2_hidden(X2,sK4(X0,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | sP0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_633,c_26,c_25,c_24,c_23,c_22,c_20])).

cnf(c_638,plain,
    ( sP0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,sK4(X0,X1))
    | r2_hidden(sK5(X0,X1),k2_pre_topc(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_637])).

cnf(c_1030,plain,
    ( sP0(X0,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X1,sK4(X0,sK6))
    | r2_hidden(sK5(X0,sK6),k2_pre_topc(sK6,X1))
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_638,c_40])).

cnf(c_1034,plain,
    ( sP0(X0,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X1,sK4(X0,sK6))
    | r2_hidden(sK5(X0,sK6),k2_pre_topc(sK6,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1030,c_42,c_41])).

cnf(c_2270,plain,
    ( sP0(X0_56,sK6)
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X1_56,sK4(X0_56,sK6))
    | r2_hidden(sK5(X0_56,sK6),k2_pre_topc(sK6,X1_56)) ),
    inference(subtyping,[status(esa)],[c_1034])).

cnf(c_2300,plain,
    ( sP0(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(sK5(sK7,sK6),k2_pre_topc(sK6,sK7))
    | ~ r2_hidden(sK7,sK4(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_2270])).

cnf(c_8,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ v3_waybel_7(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(X2,k2_pre_topc(X0,X3))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_30,negated_conjecture,
    ( r2_waybel_7(sK6,sK8,sK9)
    | ~ v4_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_737,plain,
    ( ~ v4_pre_topc(sK7,sK6)
    | ~ v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
    | ~ m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(sK9,k2_pre_topc(sK6,X0))
    | v2_struct_0(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | v1_xboole_0(sK8) ),
    inference(resolution,[status(thm)],[c_8,c_30])).

cnf(c_37,negated_conjecture,
    ( ~ v4_pre_topc(sK7,sK6)
    | ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_36,negated_conjecture,
    ( ~ v4_pre_topc(sK7,sK6)
    | v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_35,negated_conjecture,
    ( ~ v4_pre_topc(sK7,sK6)
    | v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_34,negated_conjecture,
    ( ~ v4_pre_topc(sK7,sK6)
    | v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_33,negated_conjecture,
    ( ~ v4_pre_topc(sK7,sK6)
    | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_31,negated_conjecture,
    ( ~ v4_pre_topc(sK7,sK6)
    | m1_subset_1(sK9,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_741,plain,
    ( ~ v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,sK8)
    | r2_hidden(sK9,k2_pre_topc(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_737,c_42,c_41,c_40,c_37,c_36,c_35,c_34,c_33,c_31])).

cnf(c_2272,plain,
    ( ~ v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0_56,sK8)
    | r2_hidden(sK9,k2_pre_topc(sK6,X0_56)) ),
    inference(subtyping,[status(esa)],[c_741])).

cnf(c_2296,plain,
    ( ~ v4_pre_topc(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK7,sK8)
    | r2_hidden(sK9,k2_pre_topc(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_2272])).

cnf(c_21,plain,
    ( sP0(X0,X1)
    | r2_hidden(X0,sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2278,plain,
    ( sP0(X0_56,X0_57)
    | r2_hidden(X0_56,sK4(X0_56,X0_57)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2288,plain,
    ( sP0(sK7,sK6)
    | r2_hidden(sK7,sK4(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_2278])).

cnf(c_2279,plain,
    ( sP0(X0_56,X0_57)
    | m1_subset_1(sK5(X0_56,X0_57),u1_struct_0(X0_57)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2285,plain,
    ( sP0(sK7,sK6)
    | m1_subset_1(sK5(sK7,sK6),u1_struct_0(sK6)) ),
    inference(instantiation,[status(thm)],[c_2279])).

cnf(c_18,plain,
    ( sP0(X0,X1)
    | ~ r2_hidden(sK5(X0,X1),X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2280,plain,
    ( sP0(X0_56,X0_57)
    | ~ r2_hidden(sK5(X0_56,X0_57),X0_56) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2282,plain,
    ( sP0(sK7,sK6)
    | ~ r2_hidden(sK5(sK7,sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_2280])).

cnf(c_29,negated_conjecture,
    ( ~ v4_pre_topc(sK7,sK6)
    | ~ r2_hidden(sK9,sK7) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1518,plain,
    ( ~ sP0(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK9,sK7) ),
    inference(resolution,[status(thm)],[c_29,c_1283])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1520,plain,
    ( ~ sP0(sK7,sK6)
    | ~ r2_hidden(sK9,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1518,c_39])).

cnf(c_1505,plain,
    ( ~ sP0(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK9,u1_struct_0(sK6)) ),
    inference(resolution,[status(thm)],[c_31,c_1283])).

cnf(c_1507,plain,
    ( ~ sP0(sK7,sK6)
    | m1_subset_1(sK9,u1_struct_0(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1505,c_39])).

cnf(c_32,negated_conjecture,
    ( ~ v4_pre_topc(sK7,sK6)
    | r2_hidden(sK7,sK8) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1492,plain,
    ( ~ sP0(sK7,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(sK7,sK8) ),
    inference(resolution,[status(thm)],[c_32,c_1283])).

cnf(c_1494,plain,
    ( ~ sP0(sK7,sK6)
    | r2_hidden(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1492,c_39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2452,c_2411,c_2407,c_2377,c_2319,c_2316,c_2300,c_2296,c_2288,c_2285,c_2282,c_1520,c_1507,c_1494,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:36:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 1.45/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.45/1.01  
% 1.45/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.45/1.01  
% 1.45/1.01  ------  iProver source info
% 1.45/1.01  
% 1.45/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.45/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.45/1.01  git: non_committed_changes: false
% 1.45/1.01  git: last_make_outside_of_git: false
% 1.45/1.01  
% 1.45/1.01  ------ 
% 1.45/1.01  
% 1.45/1.01  ------ Input Options
% 1.45/1.01  
% 1.45/1.01  --out_options                           all
% 1.45/1.01  --tptp_safe_out                         true
% 1.45/1.01  --problem_path                          ""
% 1.45/1.01  --include_path                          ""
% 1.45/1.01  --clausifier                            res/vclausify_rel
% 1.45/1.01  --clausifier_options                    --mode clausify
% 1.45/1.01  --stdin                                 false
% 1.45/1.01  --stats_out                             all
% 1.45/1.01  
% 1.45/1.01  ------ General Options
% 1.45/1.01  
% 1.45/1.01  --fof                                   false
% 1.45/1.01  --time_out_real                         305.
% 1.45/1.01  --time_out_virtual                      -1.
% 1.45/1.01  --symbol_type_check                     false
% 1.45/1.01  --clausify_out                          false
% 1.45/1.01  --sig_cnt_out                           false
% 1.45/1.01  --trig_cnt_out                          false
% 1.45/1.01  --trig_cnt_out_tolerance                1.
% 1.45/1.01  --trig_cnt_out_sk_spl                   false
% 1.45/1.01  --abstr_cl_out                          false
% 1.45/1.01  
% 1.45/1.01  ------ Global Options
% 1.45/1.01  
% 1.45/1.01  --schedule                              default
% 1.45/1.01  --add_important_lit                     false
% 1.45/1.01  --prop_solver_per_cl                    1000
% 1.45/1.01  --min_unsat_core                        false
% 1.45/1.01  --soft_assumptions                      false
% 1.45/1.01  --soft_lemma_size                       3
% 1.45/1.01  --prop_impl_unit_size                   0
% 1.45/1.01  --prop_impl_unit                        []
% 1.45/1.01  --share_sel_clauses                     true
% 1.45/1.01  --reset_solvers                         false
% 1.45/1.01  --bc_imp_inh                            [conj_cone]
% 1.45/1.01  --conj_cone_tolerance                   3.
% 1.45/1.01  --extra_neg_conj                        none
% 1.45/1.01  --large_theory_mode                     true
% 1.45/1.01  --prolific_symb_bound                   200
% 1.45/1.01  --lt_threshold                          2000
% 1.45/1.01  --clause_weak_htbl                      true
% 1.45/1.01  --gc_record_bc_elim                     false
% 1.45/1.01  
% 1.45/1.01  ------ Preprocessing Options
% 1.45/1.01  
% 1.45/1.01  --preprocessing_flag                    true
% 1.45/1.01  --time_out_prep_mult                    0.1
% 1.45/1.01  --splitting_mode                        input
% 1.45/1.01  --splitting_grd                         true
% 1.45/1.01  --splitting_cvd                         false
% 1.45/1.01  --splitting_cvd_svl                     false
% 1.45/1.01  --splitting_nvd                         32
% 1.45/1.01  --sub_typing                            true
% 1.45/1.01  --prep_gs_sim                           true
% 1.45/1.01  --prep_unflatten                        true
% 1.45/1.01  --prep_res_sim                          true
% 1.45/1.01  --prep_upred                            true
% 1.45/1.01  --prep_sem_filter                       exhaustive
% 1.45/1.01  --prep_sem_filter_out                   false
% 1.45/1.01  --pred_elim                             true
% 1.45/1.01  --res_sim_input                         true
% 1.45/1.01  --eq_ax_congr_red                       true
% 1.45/1.01  --pure_diseq_elim                       true
% 1.45/1.01  --brand_transform                       false
% 1.45/1.01  --non_eq_to_eq                          false
% 1.45/1.01  --prep_def_merge                        true
% 1.45/1.01  --prep_def_merge_prop_impl              false
% 1.45/1.01  --prep_def_merge_mbd                    true
% 1.45/1.01  --prep_def_merge_tr_red                 false
% 1.45/1.01  --prep_def_merge_tr_cl                  false
% 1.45/1.01  --smt_preprocessing                     true
% 1.45/1.01  --smt_ac_axioms                         fast
% 1.45/1.01  --preprocessed_out                      false
% 1.45/1.01  --preprocessed_stats                    false
% 1.45/1.01  
% 1.45/1.01  ------ Abstraction refinement Options
% 1.45/1.01  
% 1.45/1.01  --abstr_ref                             []
% 1.45/1.01  --abstr_ref_prep                        false
% 1.45/1.01  --abstr_ref_until_sat                   false
% 1.45/1.01  --abstr_ref_sig_restrict                funpre
% 1.45/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.45/1.01  --abstr_ref_under                       []
% 1.45/1.01  
% 1.45/1.01  ------ SAT Options
% 1.45/1.01  
% 1.45/1.01  --sat_mode                              false
% 1.45/1.01  --sat_fm_restart_options                ""
% 1.45/1.01  --sat_gr_def                            false
% 1.45/1.01  --sat_epr_types                         true
% 1.45/1.01  --sat_non_cyclic_types                  false
% 1.45/1.01  --sat_finite_models                     false
% 1.45/1.01  --sat_fm_lemmas                         false
% 1.45/1.01  --sat_fm_prep                           false
% 1.45/1.01  --sat_fm_uc_incr                        true
% 1.45/1.01  --sat_out_model                         small
% 1.45/1.01  --sat_out_clauses                       false
% 1.45/1.01  
% 1.45/1.01  ------ QBF Options
% 1.45/1.01  
% 1.45/1.01  --qbf_mode                              false
% 1.45/1.01  --qbf_elim_univ                         false
% 1.45/1.01  --qbf_dom_inst                          none
% 1.45/1.01  --qbf_dom_pre_inst                      false
% 1.45/1.01  --qbf_sk_in                             false
% 1.45/1.01  --qbf_pred_elim                         true
% 1.45/1.01  --qbf_split                             512
% 1.45/1.01  
% 1.45/1.01  ------ BMC1 Options
% 1.45/1.01  
% 1.45/1.01  --bmc1_incremental                      false
% 1.45/1.01  --bmc1_axioms                           reachable_all
% 1.45/1.01  --bmc1_min_bound                        0
% 1.45/1.01  --bmc1_max_bound                        -1
% 1.45/1.01  --bmc1_max_bound_default                -1
% 1.45/1.01  --bmc1_symbol_reachability              true
% 1.45/1.01  --bmc1_property_lemmas                  false
% 1.45/1.01  --bmc1_k_induction                      false
% 1.45/1.01  --bmc1_non_equiv_states                 false
% 1.45/1.01  --bmc1_deadlock                         false
% 1.45/1.01  --bmc1_ucm                              false
% 1.45/1.01  --bmc1_add_unsat_core                   none
% 1.45/1.01  --bmc1_unsat_core_children              false
% 1.45/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.45/1.01  --bmc1_out_stat                         full
% 1.45/1.01  --bmc1_ground_init                      false
% 1.45/1.01  --bmc1_pre_inst_next_state              false
% 1.45/1.01  --bmc1_pre_inst_state                   false
% 1.45/1.01  --bmc1_pre_inst_reach_state             false
% 1.45/1.01  --bmc1_out_unsat_core                   false
% 1.45/1.01  --bmc1_aig_witness_out                  false
% 1.45/1.01  --bmc1_verbose                          false
% 1.45/1.01  --bmc1_dump_clauses_tptp                false
% 1.45/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.45/1.01  --bmc1_dump_file                        -
% 1.45/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.45/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.45/1.01  --bmc1_ucm_extend_mode                  1
% 1.45/1.01  --bmc1_ucm_init_mode                    2
% 1.45/1.01  --bmc1_ucm_cone_mode                    none
% 1.45/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.45/1.01  --bmc1_ucm_relax_model                  4
% 1.45/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.45/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.45/1.01  --bmc1_ucm_layered_model                none
% 1.45/1.01  --bmc1_ucm_max_lemma_size               10
% 1.45/1.01  
% 1.45/1.01  ------ AIG Options
% 1.45/1.01  
% 1.45/1.01  --aig_mode                              false
% 1.45/1.01  
% 1.45/1.01  ------ Instantiation Options
% 1.45/1.01  
% 1.45/1.01  --instantiation_flag                    true
% 1.45/1.01  --inst_sos_flag                         false
% 1.45/1.01  --inst_sos_phase                        true
% 1.45/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.45/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.45/1.01  --inst_lit_sel_side                     num_symb
% 1.45/1.01  --inst_solver_per_active                1400
% 1.45/1.01  --inst_solver_calls_frac                1.
% 1.45/1.01  --inst_passive_queue_type               priority_queues
% 1.45/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.45/1.01  --inst_passive_queues_freq              [25;2]
% 1.45/1.01  --inst_dismatching                      true
% 1.45/1.01  --inst_eager_unprocessed_to_passive     true
% 1.45/1.01  --inst_prop_sim_given                   true
% 1.45/1.01  --inst_prop_sim_new                     false
% 1.45/1.01  --inst_subs_new                         false
% 1.45/1.01  --inst_eq_res_simp                      false
% 1.45/1.01  --inst_subs_given                       false
% 1.45/1.01  --inst_orphan_elimination               true
% 1.45/1.01  --inst_learning_loop_flag               true
% 1.45/1.01  --inst_learning_start                   3000
% 1.45/1.01  --inst_learning_factor                  2
% 1.45/1.01  --inst_start_prop_sim_after_learn       3
% 1.45/1.01  --inst_sel_renew                        solver
% 1.45/1.01  --inst_lit_activity_flag                true
% 1.45/1.01  --inst_restr_to_given                   false
% 1.45/1.01  --inst_activity_threshold               500
% 1.45/1.01  --inst_out_proof                        true
% 1.45/1.01  
% 1.45/1.01  ------ Resolution Options
% 1.45/1.01  
% 1.45/1.01  --resolution_flag                       true
% 1.45/1.01  --res_lit_sel                           adaptive
% 1.45/1.01  --res_lit_sel_side                      none
% 1.45/1.01  --res_ordering                          kbo
% 1.45/1.01  --res_to_prop_solver                    active
% 1.45/1.01  --res_prop_simpl_new                    false
% 1.45/1.01  --res_prop_simpl_given                  true
% 1.45/1.01  --res_passive_queue_type                priority_queues
% 1.45/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.45/1.01  --res_passive_queues_freq               [15;5]
% 1.45/1.01  --res_forward_subs                      full
% 1.45/1.01  --res_backward_subs                     full
% 1.45/1.01  --res_forward_subs_resolution           true
% 1.45/1.01  --res_backward_subs_resolution          true
% 1.45/1.01  --res_orphan_elimination                true
% 1.45/1.01  --res_time_limit                        2.
% 1.45/1.01  --res_out_proof                         true
% 1.45/1.01  
% 1.45/1.01  ------ Superposition Options
% 1.45/1.01  
% 1.45/1.01  --superposition_flag                    true
% 1.45/1.01  --sup_passive_queue_type                priority_queues
% 1.45/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.45/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.45/1.01  --demod_completeness_check              fast
% 1.45/1.01  --demod_use_ground                      true
% 1.45/1.01  --sup_to_prop_solver                    passive
% 1.45/1.01  --sup_prop_simpl_new                    true
% 1.45/1.01  --sup_prop_simpl_given                  true
% 1.45/1.01  --sup_fun_splitting                     false
% 1.45/1.01  --sup_smt_interval                      50000
% 1.45/1.01  
% 1.45/1.01  ------ Superposition Simplification Setup
% 1.45/1.01  
% 1.45/1.01  --sup_indices_passive                   []
% 1.45/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.45/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/1.01  --sup_full_bw                           [BwDemod]
% 1.45/1.01  --sup_immed_triv                        [TrivRules]
% 1.45/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.45/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/1.01  --sup_immed_bw_main                     []
% 1.45/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.45/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/1.01  
% 1.45/1.01  ------ Combination Options
% 1.45/1.01  
% 1.45/1.01  --comb_res_mult                         3
% 1.45/1.01  --comb_sup_mult                         2
% 1.45/1.01  --comb_inst_mult                        10
% 1.45/1.01  
% 1.45/1.01  ------ Debug Options
% 1.45/1.01  
% 1.45/1.01  --dbg_backtrace                         false
% 1.45/1.01  --dbg_dump_prop_clauses                 false
% 1.45/1.01  --dbg_dump_prop_clauses_file            -
% 1.45/1.01  --dbg_out_stat                          false
% 1.45/1.01  ------ Parsing...
% 1.45/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.45/1.01  
% 1.45/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.45/1.01  
% 1.45/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.45/1.01  ------ Proving...
% 1.45/1.01  ------ Problem Properties 
% 1.45/1.01  
% 1.45/1.01  
% 1.45/1.01  clauses                                 18
% 1.45/1.01  conjectures                             4
% 1.45/1.01  EPR                                     2
% 1.45/1.01  Horn                                    13
% 1.45/1.01  unary                                   1
% 1.45/1.01  binary                                  6
% 1.45/1.01  lits                                    63
% 1.45/1.01  lits eq                                 0
% 1.45/1.01  fd_pure                                 0
% 1.45/1.01  fd_pseudo                               0
% 1.45/1.01  fd_cond                                 0
% 1.45/1.01  fd_pseudo_cond                          0
% 1.45/1.01  AC symbols                              0
% 1.45/1.01  
% 1.45/1.01  ------ Schedule dynamic 5 is on 
% 1.45/1.01  
% 1.45/1.01  ------ no equalities: superposition off 
% 1.45/1.01  
% 1.45/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.45/1.01  
% 1.45/1.01  
% 1.45/1.01  ------ 
% 1.45/1.01  Current options:
% 1.45/1.01  ------ 
% 1.45/1.01  
% 1.45/1.01  ------ Input Options
% 1.45/1.01  
% 1.45/1.01  --out_options                           all
% 1.45/1.01  --tptp_safe_out                         true
% 1.45/1.01  --problem_path                          ""
% 1.45/1.01  --include_path                          ""
% 1.45/1.01  --clausifier                            res/vclausify_rel
% 1.45/1.01  --clausifier_options                    --mode clausify
% 1.45/1.01  --stdin                                 false
% 1.45/1.01  --stats_out                             all
% 1.45/1.01  
% 1.45/1.01  ------ General Options
% 1.45/1.01  
% 1.45/1.01  --fof                                   false
% 1.45/1.01  --time_out_real                         305.
% 1.45/1.01  --time_out_virtual                      -1.
% 1.45/1.01  --symbol_type_check                     false
% 1.45/1.01  --clausify_out                          false
% 1.45/1.01  --sig_cnt_out                           false
% 1.45/1.01  --trig_cnt_out                          false
% 1.45/1.01  --trig_cnt_out_tolerance                1.
% 1.45/1.01  --trig_cnt_out_sk_spl                   false
% 1.45/1.01  --abstr_cl_out                          false
% 1.45/1.01  
% 1.45/1.01  ------ Global Options
% 1.45/1.01  
% 1.45/1.01  --schedule                              default
% 1.45/1.01  --add_important_lit                     false
% 1.45/1.01  --prop_solver_per_cl                    1000
% 1.45/1.01  --min_unsat_core                        false
% 1.45/1.01  --soft_assumptions                      false
% 1.45/1.01  --soft_lemma_size                       3
% 1.45/1.01  --prop_impl_unit_size                   0
% 1.45/1.01  --prop_impl_unit                        []
% 1.45/1.01  --share_sel_clauses                     true
% 1.45/1.01  --reset_solvers                         false
% 1.45/1.01  --bc_imp_inh                            [conj_cone]
% 1.45/1.01  --conj_cone_tolerance                   3.
% 1.45/1.01  --extra_neg_conj                        none
% 1.45/1.01  --large_theory_mode                     true
% 1.45/1.01  --prolific_symb_bound                   200
% 1.45/1.01  --lt_threshold                          2000
% 1.45/1.01  --clause_weak_htbl                      true
% 1.45/1.01  --gc_record_bc_elim                     false
% 1.45/1.01  
% 1.45/1.01  ------ Preprocessing Options
% 1.45/1.01  
% 1.45/1.01  --preprocessing_flag                    true
% 1.45/1.01  --time_out_prep_mult                    0.1
% 1.45/1.01  --splitting_mode                        input
% 1.45/1.01  --splitting_grd                         true
% 1.45/1.01  --splitting_cvd                         false
% 1.45/1.01  --splitting_cvd_svl                     false
% 1.45/1.01  --splitting_nvd                         32
% 1.45/1.01  --sub_typing                            true
% 1.45/1.01  --prep_gs_sim                           true
% 1.45/1.01  --prep_unflatten                        true
% 1.45/1.01  --prep_res_sim                          true
% 1.45/1.01  --prep_upred                            true
% 1.45/1.01  --prep_sem_filter                       exhaustive
% 1.45/1.01  --prep_sem_filter_out                   false
% 1.45/1.01  --pred_elim                             true
% 1.45/1.01  --res_sim_input                         true
% 1.45/1.01  --eq_ax_congr_red                       true
% 1.45/1.01  --pure_diseq_elim                       true
% 1.45/1.01  --brand_transform                       false
% 1.45/1.01  --non_eq_to_eq                          false
% 1.45/1.01  --prep_def_merge                        true
% 1.45/1.01  --prep_def_merge_prop_impl              false
% 1.45/1.01  --prep_def_merge_mbd                    true
% 1.45/1.01  --prep_def_merge_tr_red                 false
% 1.45/1.01  --prep_def_merge_tr_cl                  false
% 1.45/1.01  --smt_preprocessing                     true
% 1.45/1.01  --smt_ac_axioms                         fast
% 1.45/1.01  --preprocessed_out                      false
% 1.45/1.01  --preprocessed_stats                    false
% 1.45/1.01  
% 1.45/1.01  ------ Abstraction refinement Options
% 1.45/1.01  
% 1.45/1.01  --abstr_ref                             []
% 1.45/1.01  --abstr_ref_prep                        false
% 1.45/1.01  --abstr_ref_until_sat                   false
% 1.45/1.01  --abstr_ref_sig_restrict                funpre
% 1.45/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.45/1.01  --abstr_ref_under                       []
% 1.45/1.01  
% 1.45/1.01  ------ SAT Options
% 1.45/1.01  
% 1.45/1.01  --sat_mode                              false
% 1.45/1.01  --sat_fm_restart_options                ""
% 1.45/1.01  --sat_gr_def                            false
% 1.45/1.01  --sat_epr_types                         true
% 1.45/1.01  --sat_non_cyclic_types                  false
% 1.45/1.01  --sat_finite_models                     false
% 1.45/1.01  --sat_fm_lemmas                         false
% 1.45/1.01  --sat_fm_prep                           false
% 1.45/1.01  --sat_fm_uc_incr                        true
% 1.45/1.01  --sat_out_model                         small
% 1.45/1.01  --sat_out_clauses                       false
% 1.45/1.01  
% 1.45/1.01  ------ QBF Options
% 1.45/1.01  
% 1.45/1.01  --qbf_mode                              false
% 1.45/1.01  --qbf_elim_univ                         false
% 1.45/1.01  --qbf_dom_inst                          none
% 1.45/1.01  --qbf_dom_pre_inst                      false
% 1.45/1.01  --qbf_sk_in                             false
% 1.45/1.01  --qbf_pred_elim                         true
% 1.45/1.01  --qbf_split                             512
% 1.45/1.01  
% 1.45/1.01  ------ BMC1 Options
% 1.45/1.01  
% 1.45/1.01  --bmc1_incremental                      false
% 1.45/1.01  --bmc1_axioms                           reachable_all
% 1.45/1.01  --bmc1_min_bound                        0
% 1.45/1.01  --bmc1_max_bound                        -1
% 1.45/1.01  --bmc1_max_bound_default                -1
% 1.45/1.01  --bmc1_symbol_reachability              true
% 1.45/1.01  --bmc1_property_lemmas                  false
% 1.45/1.01  --bmc1_k_induction                      false
% 1.45/1.01  --bmc1_non_equiv_states                 false
% 1.45/1.01  --bmc1_deadlock                         false
% 1.45/1.01  --bmc1_ucm                              false
% 1.45/1.01  --bmc1_add_unsat_core                   none
% 1.45/1.01  --bmc1_unsat_core_children              false
% 1.45/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.45/1.01  --bmc1_out_stat                         full
% 1.45/1.01  --bmc1_ground_init                      false
% 1.45/1.01  --bmc1_pre_inst_next_state              false
% 1.45/1.01  --bmc1_pre_inst_state                   false
% 1.45/1.01  --bmc1_pre_inst_reach_state             false
% 1.45/1.01  --bmc1_out_unsat_core                   false
% 1.45/1.01  --bmc1_aig_witness_out                  false
% 1.45/1.01  --bmc1_verbose                          false
% 1.45/1.01  --bmc1_dump_clauses_tptp                false
% 1.45/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.45/1.01  --bmc1_dump_file                        -
% 1.45/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.45/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.45/1.01  --bmc1_ucm_extend_mode                  1
% 1.45/1.01  --bmc1_ucm_init_mode                    2
% 1.45/1.01  --bmc1_ucm_cone_mode                    none
% 1.45/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.45/1.01  --bmc1_ucm_relax_model                  4
% 1.45/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.45/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.45/1.01  --bmc1_ucm_layered_model                none
% 1.45/1.01  --bmc1_ucm_max_lemma_size               10
% 1.45/1.01  
% 1.45/1.01  ------ AIG Options
% 1.45/1.01  
% 1.45/1.01  --aig_mode                              false
% 1.45/1.01  
% 1.45/1.01  ------ Instantiation Options
% 1.45/1.01  
% 1.45/1.01  --instantiation_flag                    true
% 1.45/1.01  --inst_sos_flag                         false
% 1.45/1.01  --inst_sos_phase                        true
% 1.45/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.45/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.45/1.01  --inst_lit_sel_side                     none
% 1.45/1.01  --inst_solver_per_active                1400
% 1.45/1.01  --inst_solver_calls_frac                1.
% 1.45/1.01  --inst_passive_queue_type               priority_queues
% 1.45/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.45/1.01  --inst_passive_queues_freq              [25;2]
% 1.45/1.01  --inst_dismatching                      true
% 1.45/1.01  --inst_eager_unprocessed_to_passive     true
% 1.45/1.01  --inst_prop_sim_given                   true
% 1.45/1.01  --inst_prop_sim_new                     false
% 1.45/1.01  --inst_subs_new                         false
% 1.45/1.01  --inst_eq_res_simp                      false
% 1.45/1.01  --inst_subs_given                       false
% 1.45/1.01  --inst_orphan_elimination               true
% 1.45/1.01  --inst_learning_loop_flag               true
% 1.45/1.01  --inst_learning_start                   3000
% 1.45/1.01  --inst_learning_factor                  2
% 1.45/1.01  --inst_start_prop_sim_after_learn       3
% 1.45/1.01  --inst_sel_renew                        solver
% 1.45/1.01  --inst_lit_activity_flag                true
% 1.45/1.01  --inst_restr_to_given                   false
% 1.45/1.01  --inst_activity_threshold               500
% 1.45/1.01  --inst_out_proof                        true
% 1.45/1.01  
% 1.45/1.01  ------ Resolution Options
% 1.45/1.01  
% 1.45/1.01  --resolution_flag                       false
% 1.45/1.01  --res_lit_sel                           adaptive
% 1.45/1.01  --res_lit_sel_side                      none
% 1.45/1.01  --res_ordering                          kbo
% 1.45/1.01  --res_to_prop_solver                    active
% 1.45/1.01  --res_prop_simpl_new                    false
% 1.45/1.01  --res_prop_simpl_given                  true
% 1.45/1.01  --res_passive_queue_type                priority_queues
% 1.45/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.45/1.01  --res_passive_queues_freq               [15;5]
% 1.45/1.01  --res_forward_subs                      full
% 1.45/1.01  --res_backward_subs                     full
% 1.45/1.01  --res_forward_subs_resolution           true
% 1.45/1.01  --res_backward_subs_resolution          true
% 1.45/1.01  --res_orphan_elimination                true
% 1.45/1.01  --res_time_limit                        2.
% 1.45/1.01  --res_out_proof                         true
% 1.45/1.01  
% 1.45/1.01  ------ Superposition Options
% 1.45/1.01  
% 1.45/1.01  --superposition_flag                    false
% 1.45/1.01  --sup_passive_queue_type                priority_queues
% 1.45/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.45/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.45/1.01  --demod_completeness_check              fast
% 1.45/1.01  --demod_use_ground                      true
% 1.45/1.01  --sup_to_prop_solver                    passive
% 1.45/1.01  --sup_prop_simpl_new                    true
% 1.45/1.01  --sup_prop_simpl_given                  true
% 1.45/1.01  --sup_fun_splitting                     false
% 1.45/1.01  --sup_smt_interval                      50000
% 1.45/1.01  
% 1.45/1.01  ------ Superposition Simplification Setup
% 1.45/1.01  
% 1.45/1.01  --sup_indices_passive                   []
% 1.45/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.45/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/1.01  --sup_full_bw                           [BwDemod]
% 1.45/1.01  --sup_immed_triv                        [TrivRules]
% 1.45/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.45/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/1.01  --sup_immed_bw_main                     []
% 1.45/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.45/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/1.01  
% 1.45/1.01  ------ Combination Options
% 1.45/1.01  
% 1.45/1.01  --comb_res_mult                         3
% 1.45/1.01  --comb_sup_mult                         2
% 1.45/1.01  --comb_inst_mult                        10
% 1.45/1.01  
% 1.45/1.01  ------ Debug Options
% 1.45/1.01  
% 1.45/1.01  --dbg_backtrace                         false
% 1.45/1.01  --dbg_dump_prop_clauses                 false
% 1.45/1.01  --dbg_dump_prop_clauses_file            -
% 1.45/1.01  --dbg_out_stat                          false
% 1.45/1.01  
% 1.45/1.01  
% 1.45/1.01  
% 1.45/1.01  
% 1.45/1.01  ------ Proving...
% 1.45/1.01  
% 1.45/1.01  
% 1.45/1.01  % SZS status Theorem for theBenchmark.p
% 1.45/1.01  
% 1.45/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.45/1.01  
% 1.45/1.01  fof(f14,plain,(
% 1.45/1.01    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X2)))),
% 1.45/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.45/1.01  
% 1.45/1.01  fof(f26,plain,(
% 1.45/1.01    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X2)) | ~sP0(X1,X0)))),
% 1.45/1.01    inference(nnf_transformation,[],[f14])).
% 1.45/1.01  
% 1.45/1.01  fof(f27,plain,(
% 1.45/1.01    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_waybel_7(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) & r2_hidden(X0,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) & ~v1_xboole_0(X2))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_waybel_7(X1,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) | v1_xboole_0(X4)) | ~sP0(X0,X1)))),
% 1.45/1.01    inference(rectify,[],[f26])).
% 1.45/1.01  
% 1.45/1.01  fof(f29,plain,(
% 1.45/1.01    ( ! [X2] : (! [X1,X0] : (? [X3] : (~r2_hidden(X3,X0) & r1_waybel_7(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_hidden(sK5(X0,X1),X0) & r1_waybel_7(X1,X2,sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))))) )),
% 1.45/1.01    introduced(choice_axiom,[])).
% 1.45/1.01  
% 1.45/1.01  fof(f28,plain,(
% 1.45/1.01    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X0) & r1_waybel_7(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) & r2_hidden(X0,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) & ~v1_xboole_0(X2)) => (? [X3] : (~r2_hidden(X3,X0) & r1_waybel_7(X1,sK4(X0,X1),X3) & m1_subset_1(X3,u1_struct_0(X1))) & r2_hidden(X0,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) & v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1))) & v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1))) & v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) & ~v1_xboole_0(sK4(X0,X1))))),
% 1.45/1.01    introduced(choice_axiom,[])).
% 1.45/1.01  
% 1.45/1.01  fof(f30,plain,(
% 1.45/1.01    ! [X0,X1] : ((sP0(X0,X1) | ((~r2_hidden(sK5(X0,X1),X0) & r1_waybel_7(X1,sK4(X0,X1),sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))) & r2_hidden(X0,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) & v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1))) & v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1))) & v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) & ~v1_xboole_0(sK4(X0,X1)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X0) | ~r1_waybel_7(X1,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) | v1_xboole_0(X4)) | ~sP0(X0,X1)))),
% 1.45/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f27,f29,f28])).
% 1.45/1.01  
% 1.45/1.01  fof(f57,plain,(
% 1.45/1.01    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X0) | ~r1_waybel_7(X1,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_hidden(X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1))) | ~v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) | v1_xboole_0(X4) | ~sP0(X0,X1)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f30])).
% 1.45/1.01  
% 1.45/1.01  fof(f1,axiom,(
% 1.45/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3))))))),
% 1.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.45/1.01  
% 1.45/1.01  fof(f6,plain,(
% 1.45/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.45/1.01    inference(ennf_transformation,[],[f1])).
% 1.45/1.01  
% 1.45/1.01  fof(f7,plain,(
% 1.45/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/1.01    inference(flattening,[],[f6])).
% 1.45/1.01  
% 1.45/1.01  fof(f17,plain,(
% 1.45/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r1_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X3))) & (? [X3] : (r1_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X3)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/1.01    inference(nnf_transformation,[],[f7])).
% 1.45/1.01  
% 1.45/1.01  fof(f18,plain,(
% 1.45/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r1_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X3))) & (? [X4] : (r1_waybel_7(X0,X4,X2) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X4)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/1.01    inference(rectify,[],[f17])).
% 1.45/1.01  
% 1.45/1.01  fof(f19,plain,(
% 1.45/1.01    ! [X2,X1,X0] : (? [X4] : (r1_waybel_7(X0,X4,X2) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X4)) => (r1_waybel_7(X0,sK2(X0,X1,X2),X2) & r2_hidden(X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK2(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK2(X0,X1,X2))))),
% 1.45/1.01    introduced(choice_axiom,[])).
% 1.45/1.01  
% 1.45/1.01  fof(f20,plain,(
% 1.45/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r1_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X3))) & ((r1_waybel_7(X0,sK2(X0,X1,X2),X2) & r2_hidden(X1,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK2(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK2(X0,X1,X2))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 1.45/1.01  
% 1.45/1.01  fof(f45,plain,(
% 1.45/1.01    ( ! [X2,X0,X1] : (r1_waybel_7(X0,sK2(X0,X1,X2),X2) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f20])).
% 1.45/1.01  
% 1.45/1.01  fof(f39,plain,(
% 1.45/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(sK2(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f20])).
% 1.45/1.01  
% 1.45/1.01  fof(f43,plain,(
% 1.45/1.01    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f20])).
% 1.45/1.01  
% 1.45/1.01  fof(f42,plain,(
% 1.45/1.01    ( ! [X2,X0,X1] : (v13_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f20])).
% 1.45/1.01  
% 1.45/1.01  fof(f41,plain,(
% 1.45/1.01    ( ! [X2,X0,X1] : (v2_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f20])).
% 1.45/1.01  
% 1.45/1.01  fof(f40,plain,(
% 1.45/1.01    ( ! [X2,X0,X1] : (v1_subset_1(sK2(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f20])).
% 1.45/1.01  
% 1.45/1.01  fof(f4,conjecture,(
% 1.45/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 1.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.45/1.01  
% 1.45/1.01  fof(f5,negated_conjecture,(
% 1.45/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 1.45/1.01    inference(negated_conjecture,[],[f4])).
% 1.45/1.01  
% 1.45/1.01  fof(f12,plain,(
% 1.45/1.01    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.45/1.01    inference(ennf_transformation,[],[f5])).
% 1.45/1.01  
% 1.45/1.01  fof(f13,plain,(
% 1.45/1.01    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.45/1.01    inference(flattening,[],[f12])).
% 1.45/1.01  
% 1.45/1.01  fof(f31,plain,(
% 1.45/1.01    ? [X0] : (? [X1] : (((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.45/1.01    inference(nnf_transformation,[],[f13])).
% 1.45/1.01  
% 1.45/1.01  fof(f32,plain,(
% 1.45/1.01    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r2_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X2)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.45/1.01    inference(flattening,[],[f31])).
% 1.45/1.01  
% 1.45/1.01  fof(f33,plain,(
% 1.45/1.01    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.45/1.01    inference(rectify,[],[f32])).
% 1.45/1.01  
% 1.45/1.01  fof(f37,plain,(
% 1.45/1.01    ( ! [X2,X0,X1] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK9,X1) & r2_waybel_7(X0,X2,sK9) & m1_subset_1(sK9,u1_struct_0(X0)))) )),
% 1.45/1.01    introduced(choice_axiom,[])).
% 1.45/1.01  
% 1.45/1.01  fof(f36,plain,(
% 1.45/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) => (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,sK8,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,sK8) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(sK8))) )),
% 1.45/1.01    introduced(choice_axiom,[])).
% 1.45/1.01  
% 1.45/1.01  fof(f35,plain,(
% 1.45/1.01    ( ! [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((? [X2] : (? [X3] : (~r2_hidden(X3,sK7) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(sK7,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(sK7,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK7) | ~r2_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(sK7,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X4)) | v4_pre_topc(sK7,X0)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.45/1.01    introduced(choice_axiom,[])).
% 1.45/1.01  
% 1.45/1.01  fof(f34,plain,(
% 1.45/1.01    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,X0)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X4)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r2_waybel_7(sK6,X2,X3) & m1_subset_1(X3,u1_struct_0(sK6))) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v3_waybel_7(X2,k3_yellow_1(k2_struct_0(sK6))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(sK6))) & ~v1_xboole_0(X2)) | ~v4_pre_topc(X1,sK6)) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r2_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6))) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | v1_xboole_0(X4)) | v4_pre_topc(X1,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 1.45/1.01    introduced(choice_axiom,[])).
% 1.45/1.01  
% 1.45/1.01  fof(f38,plain,(
% 1.45/1.01    ((((~r2_hidden(sK9,sK7) & r2_waybel_7(sK6,sK8,sK9) & m1_subset_1(sK9,u1_struct_0(sK6))) & r2_hidden(sK7,sK8) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) & v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6))) & v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) & v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) & ~v1_xboole_0(sK8)) | ~v4_pre_topc(sK7,sK6)) & (! [X4] : (! [X5] : (r2_hidden(X5,sK7) | ~r2_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6))) | ~r2_hidden(sK7,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | v1_xboole_0(X4)) | v4_pre_topc(sK7,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 1.45/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f33,f37,f36,f35,f34])).
% 1.45/1.01  
% 1.45/1.01  fof(f70,plain,(
% 1.45/1.01    l1_pre_topc(sK6)),
% 1.45/1.01    inference(cnf_transformation,[],[f38])).
% 1.45/1.01  
% 1.45/1.01  fof(f68,plain,(
% 1.45/1.01    ~v2_struct_0(sK6)),
% 1.45/1.01    inference(cnf_transformation,[],[f38])).
% 1.45/1.01  
% 1.45/1.01  fof(f69,plain,(
% 1.45/1.01    v2_pre_topc(sK6)),
% 1.45/1.01    inference(cnf_transformation,[],[f38])).
% 1.45/1.01  
% 1.45/1.01  fof(f2,axiom,(
% 1.45/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3))))))),
% 1.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.45/1.01  
% 1.45/1.01  fof(f8,plain,(
% 1.45/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.45/1.01    inference(ennf_transformation,[],[f2])).
% 1.45/1.01  
% 1.45/1.01  fof(f9,plain,(
% 1.45/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/1.01    inference(flattening,[],[f8])).
% 1.45/1.01  
% 1.45/1.01  fof(f21,plain,(
% 1.45/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3))) & (? [X3] : (r2_waybel_7(X0,X3,X2) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X3)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/1.01    inference(nnf_transformation,[],[f9])).
% 1.45/1.01  
% 1.45/1.01  fof(f22,plain,(
% 1.45/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3))) & (? [X4] : (r2_waybel_7(X0,X4,X2) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X4)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/1.01    inference(rectify,[],[f21])).
% 1.45/1.01  
% 1.45/1.01  fof(f23,plain,(
% 1.45/1.01    ! [X2,X1,X0] : (? [X4] : (r2_waybel_7(X0,X4,X2) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(X4,k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X4)) => (r2_waybel_7(X0,sK3(X0,X1,X2),X2) & r2_hidden(X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(sK3(X0,X1,X2))))),
% 1.45/1.01    introduced(choice_axiom,[])).
% 1.45/1.01  
% 1.45/1.01  fof(f24,plain,(
% 1.45/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ! [X3] : (~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3))) & ((r2_waybel_7(X0,sK3(X0,X1,X2),X2) & r2_hidden(X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v3_waybel_7(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v13_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(sK3(X0,X1,X2))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 1.45/1.01  
% 1.45/1.01  fof(f51,plain,(
% 1.45/1.01    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f24])).
% 1.45/1.01  
% 1.45/1.01  fof(f47,plain,(
% 1.45/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(sK3(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f24])).
% 1.45/1.01  
% 1.45/1.01  fof(f48,plain,(
% 1.45/1.01    ( ! [X2,X0,X1] : (v2_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f24])).
% 1.45/1.01  
% 1.45/1.01  fof(f49,plain,(
% 1.45/1.01    ( ! [X2,X0,X1] : (v13_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f24])).
% 1.45/1.01  
% 1.45/1.01  fof(f50,plain,(
% 1.45/1.01    ( ! [X2,X0,X1] : (v3_waybel_7(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f24])).
% 1.45/1.01  
% 1.45/1.01  fof(f53,plain,(
% 1.45/1.01    ( ! [X2,X0,X1] : (r2_waybel_7(X0,sK3(X0,X1,X2),X2) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f24])).
% 1.45/1.01  
% 1.45/1.01  fof(f72,plain,(
% 1.45/1.01    ( ! [X4,X5] : (r2_hidden(X5,sK7) | ~r2_waybel_7(sK6,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK6)) | ~r2_hidden(sK7,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v3_waybel_7(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v13_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | ~v2_waybel_0(X4,k3_yellow_1(k2_struct_0(sK6))) | v1_xboole_0(X4) | v4_pre_topc(sK7,sK6)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f38])).
% 1.45/1.01  
% 1.45/1.01  fof(f52,plain,(
% 1.45/1.01    ( ! [X2,X0,X1] : (r2_hidden(X1,sK3(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f24])).
% 1.45/1.01  
% 1.45/1.01  fof(f44,plain,(
% 1.45/1.01    ( ! [X2,X0,X1] : (r2_hidden(X1,sK2(X0,X1,X2)) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f20])).
% 1.45/1.01  
% 1.45/1.01  fof(f15,plain,(
% 1.45/1.01    ! [X0,X1] : ((v4_pre_topc(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.45/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.45/1.01  
% 1.45/1.01  fof(f25,plain,(
% 1.45/1.01    ! [X0,X1] : (((v4_pre_topc(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v4_pre_topc(X1,X0))) | ~sP1(X0,X1))),
% 1.45/1.01    inference(nnf_transformation,[],[f15])).
% 1.45/1.01  
% 1.45/1.01  fof(f56,plain,(
% 1.45/1.01    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~sP0(X1,X0) | ~sP1(X0,X1)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f25])).
% 1.45/1.01  
% 1.45/1.01  fof(f3,axiom,(
% 1.45/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X2)) => (r2_hidden(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_waybel_7(X0,X2,X3) => r2_hidden(X3,X1))))))))),
% 1.45/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.45/1.01  
% 1.45/1.01  fof(f10,plain,(
% 1.45/1.01    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : ((! [X3] : ((r2_hidden(X3,X1) | ~r1_waybel_7(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X2)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.45/1.01    inference(ennf_transformation,[],[f3])).
% 1.45/1.01  
% 1.45/1.01  fof(f11,plain,(
% 1.45/1.01    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_waybel_7(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/1.01    inference(flattening,[],[f10])).
% 1.45/1.01  
% 1.45/1.01  fof(f16,plain,(
% 1.45/1.01    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.45/1.01    inference(definition_folding,[],[f11,f15,f14])).
% 1.45/1.01  
% 1.45/1.01  fof(f67,plain,(
% 1.45/1.01    ( ! [X0,X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f16])).
% 1.45/1.01  
% 1.45/1.01  fof(f55,plain,(
% 1.45/1.01    ( ! [X0,X1] : (sP0(X1,X0) | ~v4_pre_topc(X1,X0) | ~sP1(X0,X1)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f25])).
% 1.45/1.01  
% 1.45/1.01  fof(f46,plain,(
% 1.45/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | ~r1_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X3) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f20])).
% 1.45/1.01  
% 1.45/1.01  fof(f65,plain,(
% 1.45/1.01    ( ! [X0,X1] : (sP0(X0,X1) | r1_waybel_7(X1,sK4(X0,X1),sK5(X0,X1))) )),
% 1.45/1.01    inference(cnf_transformation,[],[f30])).
% 1.45/1.01  
% 1.45/1.01  fof(f58,plain,(
% 1.45/1.01    ( ! [X0,X1] : (sP0(X0,X1) | ~v1_xboole_0(sK4(X0,X1))) )),
% 1.45/1.01    inference(cnf_transformation,[],[f30])).
% 1.45/1.01  
% 1.45/1.01  fof(f59,plain,(
% 1.45/1.01    ( ! [X0,X1] : (sP0(X0,X1) | v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )),
% 1.45/1.01    inference(cnf_transformation,[],[f30])).
% 1.45/1.01  
% 1.45/1.01  fof(f60,plain,(
% 1.45/1.01    ( ! [X0,X1] : (sP0(X0,X1) | v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1)))) )),
% 1.45/1.01    inference(cnf_transformation,[],[f30])).
% 1.45/1.01  
% 1.45/1.01  fof(f61,plain,(
% 1.45/1.01    ( ! [X0,X1] : (sP0(X0,X1) | v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1)))) )),
% 1.45/1.01    inference(cnf_transformation,[],[f30])).
% 1.45/1.01  
% 1.45/1.01  fof(f62,plain,(
% 1.45/1.01    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))) )),
% 1.45/1.01    inference(cnf_transformation,[],[f30])).
% 1.45/1.01  
% 1.45/1.01  fof(f64,plain,(
% 1.45/1.01    ( ! [X0,X1] : (sP0(X0,X1) | m1_subset_1(sK5(X0,X1),u1_struct_0(X1))) )),
% 1.45/1.01    inference(cnf_transformation,[],[f30])).
% 1.45/1.01  
% 1.45/1.01  fof(f54,plain,(
% 1.45/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | ~r2_waybel_7(X0,X3,X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v3_waybel_7(X3,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X3) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f24])).
% 1.45/1.01  
% 1.45/1.01  fof(f80,plain,(
% 1.45/1.01    r2_waybel_7(sK6,sK8,sK9) | ~v4_pre_topc(sK7,sK6)),
% 1.45/1.01    inference(cnf_transformation,[],[f38])).
% 1.45/1.01  
% 1.45/1.01  fof(f73,plain,(
% 1.45/1.01    ~v1_xboole_0(sK8) | ~v4_pre_topc(sK7,sK6)),
% 1.45/1.01    inference(cnf_transformation,[],[f38])).
% 1.45/1.01  
% 1.45/1.01  fof(f74,plain,(
% 1.45/1.01    v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~v4_pre_topc(sK7,sK6)),
% 1.45/1.01    inference(cnf_transformation,[],[f38])).
% 1.45/1.01  
% 1.45/1.01  fof(f75,plain,(
% 1.45/1.01    v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~v4_pre_topc(sK7,sK6)),
% 1.45/1.01    inference(cnf_transformation,[],[f38])).
% 1.45/1.01  
% 1.45/1.01  fof(f76,plain,(
% 1.45/1.01    v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6))) | ~v4_pre_topc(sK7,sK6)),
% 1.45/1.01    inference(cnf_transformation,[],[f38])).
% 1.45/1.01  
% 1.45/1.01  fof(f77,plain,(
% 1.45/1.01    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) | ~v4_pre_topc(sK7,sK6)),
% 1.45/1.01    inference(cnf_transformation,[],[f38])).
% 1.45/1.01  
% 1.45/1.01  fof(f79,plain,(
% 1.45/1.01    m1_subset_1(sK9,u1_struct_0(sK6)) | ~v4_pre_topc(sK7,sK6)),
% 1.45/1.01    inference(cnf_transformation,[],[f38])).
% 1.45/1.01  
% 1.45/1.01  fof(f63,plain,(
% 1.45/1.01    ( ! [X0,X1] : (sP0(X0,X1) | r2_hidden(X0,sK4(X0,X1))) )),
% 1.45/1.01    inference(cnf_transformation,[],[f30])).
% 1.45/1.01  
% 1.45/1.01  fof(f66,plain,(
% 1.45/1.01    ( ! [X0,X1] : (sP0(X0,X1) | ~r2_hidden(sK5(X0,X1),X0)) )),
% 1.45/1.01    inference(cnf_transformation,[],[f30])).
% 1.45/1.01  
% 1.45/1.01  fof(f81,plain,(
% 1.45/1.01    ~r2_hidden(sK9,sK7) | ~v4_pre_topc(sK7,sK6)),
% 1.45/1.01    inference(cnf_transformation,[],[f38])).
% 1.45/1.01  
% 1.45/1.01  fof(f71,plain,(
% 1.45/1.01    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 1.45/1.01    inference(cnf_transformation,[],[f38])).
% 1.45/1.01  
% 1.45/1.01  fof(f78,plain,(
% 1.45/1.01    r2_hidden(sK7,sK8) | ~v4_pre_topc(sK7,sK6)),
% 1.45/1.01    inference(cnf_transformation,[],[f38])).
% 1.45/1.01  
% 1.45/1.01  cnf(c_27,plain,
% 1.45/1.01      ( ~ r1_waybel_7(X0,X1,X2)
% 1.45/1.01      | ~ sP0(X3,X0)
% 1.45/1.01      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
% 1.45/1.01      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
% 1.45/1.01      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.45/1.01      | ~ r2_hidden(X3,X1)
% 1.45/1.01      | r2_hidden(X2,X3)
% 1.45/1.01      | v1_xboole_0(X1) ),
% 1.45/1.01      inference(cnf_transformation,[],[f57]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1,plain,
% 1.45/1.01      ( r1_waybel_7(X0,sK2(X0,X1,X2),X2)
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.45/1.01      | v2_struct_0(X0)
% 1.45/1.01      | ~ v2_pre_topc(X0)
% 1.45/1.01      | ~ l1_pre_topc(X0) ),
% 1.45/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_521,plain,
% 1.45/1.01      ( ~ sP0(X0,X1)
% 1.45/1.01      | ~ v1_subset_1(sK2(X1,X2,X3),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
% 1.45/1.01      | ~ v2_waybel_0(sK2(X1,X2,X3),k3_yellow_1(k2_struct_0(X1)))
% 1.45/1.01      | ~ v13_waybel_0(sK2(X1,X2,X3),k3_yellow_1(k2_struct_0(X1)))
% 1.45/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.45/1.01      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.45/1.01      | ~ m1_subset_1(sK2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
% 1.45/1.01      | r2_hidden(X3,X0)
% 1.45/1.01      | ~ r2_hidden(X0,sK2(X1,X2,X3))
% 1.45/1.01      | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
% 1.45/1.01      | v2_struct_0(X1)
% 1.45/1.01      | ~ v2_pre_topc(X1)
% 1.45/1.01      | ~ l1_pre_topc(X1)
% 1.45/1.01      | v1_xboole_0(sK2(X1,X2,X3)) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_27,c_1]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_7,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.45/1.01      | v2_struct_0(X1)
% 1.45/1.01      | ~ v2_pre_topc(X1)
% 1.45/1.01      | ~ l1_pre_topc(X1)
% 1.45/1.01      | ~ v1_xboole_0(sK2(X1,X0,X2)) ),
% 1.45/1.01      inference(cnf_transformation,[],[f39]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_3,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.45/1.01      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.45/1.01      | v2_struct_0(X1)
% 1.45/1.01      | ~ v2_pre_topc(X1)
% 1.45/1.01      | ~ l1_pre_topc(X1) ),
% 1.45/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_4,plain,
% 1.45/1.01      ( v13_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.45/1.01      | v2_struct_0(X0)
% 1.45/1.01      | ~ v2_pre_topc(X0)
% 1.45/1.01      | ~ l1_pre_topc(X0) ),
% 1.45/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_5,plain,
% 1.45/1.01      ( v2_waybel_0(sK2(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.45/1.01      | v2_struct_0(X0)
% 1.45/1.01      | ~ v2_pre_topc(X0)
% 1.45/1.01      | ~ l1_pre_topc(X0) ),
% 1.45/1.01      inference(cnf_transformation,[],[f41]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_6,plain,
% 1.45/1.01      ( v1_subset_1(sK2(X0,X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.45/1.01      | v2_struct_0(X0)
% 1.45/1.01      | ~ v2_pre_topc(X0)
% 1.45/1.01      | ~ l1_pre_topc(X0) ),
% 1.45/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_553,plain,
% 1.45/1.01      ( ~ sP0(X0,X1)
% 1.45/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.45/1.01      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.45/1.01      | r2_hidden(X3,X0)
% 1.45/1.01      | ~ r2_hidden(X0,sK2(X1,X2,X3))
% 1.45/1.01      | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
% 1.45/1.01      | v2_struct_0(X1)
% 1.45/1.01      | ~ v2_pre_topc(X1)
% 1.45/1.01      | ~ l1_pre_topc(X1) ),
% 1.45/1.01      inference(forward_subsumption_resolution,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_521,c_7,c_3,c_4,c_5,c_6]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_40,negated_conjecture,
% 1.45/1.01      ( l1_pre_topc(sK6) ),
% 1.45/1.01      inference(cnf_transformation,[],[f70]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1078,plain,
% 1.45/1.01      ( ~ sP0(X0,sK6)
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 1.45/1.01      | r2_hidden(X2,X0)
% 1.45/1.01      | ~ r2_hidden(X0,sK2(sK6,X1,X2))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(sK6,X1))
% 1.45/1.01      | v2_struct_0(sK6)
% 1.45/1.01      | ~ v2_pre_topc(sK6) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_553,c_40]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_42,negated_conjecture,
% 1.45/1.01      ( ~ v2_struct_0(sK6) ),
% 1.45/1.01      inference(cnf_transformation,[],[f68]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_41,negated_conjecture,
% 1.45/1.01      ( v2_pre_topc(sK6) ),
% 1.45/1.01      inference(cnf_transformation,[],[f69]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1082,plain,
% 1.45/1.01      ( ~ sP0(X0,sK6)
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(sK6))
% 1.45/1.01      | r2_hidden(X2,X0)
% 1.45/1.01      | ~ r2_hidden(X0,sK2(sK6,X1,X2))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(sK6,X1)) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_1078,c_42,c_41]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2268,plain,
% 1.45/1.01      ( ~ sP0(X0_56,sK6)
% 1.45/1.01      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X2_56,u1_struct_0(sK6))
% 1.45/1.01      | r2_hidden(X2_56,X0_56)
% 1.45/1.01      | ~ r2_hidden(X0_56,sK2(sK6,X1_56,X2_56))
% 1.45/1.01      | ~ r2_hidden(X2_56,k2_pre_topc(sK6,X1_56)) ),
% 1.45/1.01      inference(subtyping,[status(esa)],[c_1082]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2450,plain,
% 1.45/1.01      ( ~ sP0(X0_56,sK6)
% 1.45/1.01      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(sK9,u1_struct_0(sK6))
% 1.45/1.01      | ~ r2_hidden(X0_56,sK2(sK6,X1_56,sK9))
% 1.45/1.01      | r2_hidden(sK9,X0_56)
% 1.45/1.01      | ~ r2_hidden(sK9,k2_pre_topc(sK6,X1_56)) ),
% 1.45/1.01      inference(instantiation,[status(thm)],[c_2268]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2452,plain,
% 1.45/1.01      ( ~ sP0(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(sK9,u1_struct_0(sK6))
% 1.45/1.01      | ~ r2_hidden(sK7,sK2(sK6,sK7,sK9))
% 1.45/1.01      | ~ r2_hidden(sK9,k2_pre_topc(sK6,sK7))
% 1.45/1.01      | r2_hidden(sK9,sK7) ),
% 1.45/1.01      inference(instantiation,[status(thm)],[c_2450]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_11,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.45/1.01      | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.45/1.01      | v2_struct_0(X1)
% 1.45/1.01      | ~ v2_pre_topc(X1)
% 1.45/1.01      | ~ l1_pre_topc(X1) ),
% 1.45/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1107,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | v2_struct_0(sK6)
% 1.45/1.01      | ~ v2_pre_topc(sK6) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_11,c_40]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1111,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0)) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_1107,c_42,c_41]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_15,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.45/1.01      | v2_struct_0(X1)
% 1.45/1.01      | ~ v2_pre_topc(X1)
% 1.45/1.01      | ~ l1_pre_topc(X1)
% 1.45/1.01      | ~ v1_xboole_0(sK3(X1,X0,X2)) ),
% 1.45/1.01      inference(cnf_transformation,[],[f47]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_14,plain,
% 1.45/1.01      ( v2_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.45/1.01      | v2_struct_0(X0)
% 1.45/1.01      | ~ v2_pre_topc(X0)
% 1.45/1.01      | ~ l1_pre_topc(X0) ),
% 1.45/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_13,plain,
% 1.45/1.01      ( v13_waybel_0(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.45/1.01      | v2_struct_0(X0)
% 1.45/1.01      | ~ v2_pre_topc(X0)
% 1.45/1.01      | ~ l1_pre_topc(X0) ),
% 1.45/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_12,plain,
% 1.45/1.01      ( v3_waybel_7(sK3(X0,X1,X2),k3_yellow_1(k2_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.45/1.01      | v2_struct_0(X0)
% 1.45/1.01      | ~ v2_pre_topc(X0)
% 1.45/1.01      | ~ l1_pre_topc(X0) ),
% 1.45/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_9,plain,
% 1.45/1.01      ( r2_waybel_7(X0,sK3(X0,X1,X2),X2)
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
% 1.45/1.01      | v2_struct_0(X0)
% 1.45/1.01      | ~ v2_pre_topc(X0)
% 1.45/1.01      | ~ l1_pre_topc(X0) ),
% 1.45/1.01      inference(cnf_transformation,[],[f53]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_38,negated_conjecture,
% 1.45/1.01      ( ~ r2_waybel_7(sK6,X0,X1)
% 1.45/1.01      | v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ v3_waybel_7(X0,k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(sK7,X0)
% 1.45/1.01      | v1_xboole_0(X0) ),
% 1.45/1.01      inference(cnf_transformation,[],[f72]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_760,plain,
% 1.45/1.01      ( v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ v3_waybel_7(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ v13_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
% 1.45/1.01      | v2_struct_0(sK6)
% 1.45/1.01      | ~ v2_pre_topc(sK6)
% 1.45/1.01      | ~ l1_pre_topc(sK6)
% 1.45/1.01      | v1_xboole_0(sK3(sK6,X0,X1)) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_9,c_38]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_764,plain,
% 1.45/1.01      ( ~ r2_hidden(sK7,sK3(sK6,X0,X1))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ v13_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ v3_waybel_7(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | v4_pre_topc(sK7,sK6)
% 1.45/1.01      | v1_xboole_0(sK3(sK6,X0,X1)) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_760,c_42,c_41,c_40]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_765,plain,
% 1.45/1.01      ( v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ v3_waybel_7(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ v13_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
% 1.45/1.01      | v1_xboole_0(sK3(sK6,X0,X1)) ),
% 1.45/1.01      inference(renaming,[status(thm)],[c_764]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_821,plain,
% 1.45/1.01      ( v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ v13_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
% 1.45/1.01      | v2_struct_0(sK6)
% 1.45/1.01      | ~ v2_pre_topc(sK6)
% 1.45/1.01      | ~ l1_pre_topc(sK6)
% 1.45/1.01      | v1_xboole_0(sK3(sK6,X0,X1)) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_12,c_765]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_825,plain,
% 1.45/1.01      ( ~ r2_hidden(sK7,sK3(sK6,X0,X1))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ v13_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | v4_pre_topc(sK7,sK6)
% 1.45/1.01      | v1_xboole_0(sK3(sK6,X0,X1)) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_821,c_42,c_41,c_40]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_826,plain,
% 1.45/1.01      ( v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ v13_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
% 1.45/1.01      | v1_xboole_0(sK3(sK6,X0,X1)) ),
% 1.45/1.01      inference(renaming,[status(thm)],[c_825]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_873,plain,
% 1.45/1.01      ( v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
% 1.45/1.01      | v2_struct_0(sK6)
% 1.45/1.01      | ~ v2_pre_topc(sK6)
% 1.45/1.01      | ~ l1_pre_topc(sK6)
% 1.45/1.01      | v1_xboole_0(sK3(sK6,X0,X1)) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_13,c_826]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_877,plain,
% 1.45/1.01      ( ~ r2_hidden(sK7,sK3(sK6,X0,X1))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | v4_pre_topc(sK7,sK6)
% 1.45/1.01      | v1_xboole_0(sK3(sK6,X0,X1)) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_873,c_42,c_41,c_40]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_878,plain,
% 1.45/1.01      ( v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ v2_waybel_0(sK3(sK6,X0,X1),k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
% 1.45/1.01      | v1_xboole_0(sK3(sK6,X0,X1)) ),
% 1.45/1.01      inference(renaming,[status(thm)],[c_877]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_921,plain,
% 1.45/1.01      ( v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
% 1.45/1.01      | v2_struct_0(sK6)
% 1.45/1.01      | ~ v2_pre_topc(sK6)
% 1.45/1.01      | ~ l1_pre_topc(sK6)
% 1.45/1.01      | v1_xboole_0(sK3(sK6,X0,X1)) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_14,c_878]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_925,plain,
% 1.45/1.01      ( ~ r2_hidden(sK7,sK3(sK6,X0,X1))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | v4_pre_topc(sK7,sK6)
% 1.45/1.01      | v1_xboole_0(sK3(sK6,X0,X1)) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_921,c_42,c_41,c_40]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_926,plain,
% 1.45/1.01      ( v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
% 1.45/1.01      | v1_xboole_0(sK3(sK6,X0,X1)) ),
% 1.45/1.01      inference(renaming,[status(thm)],[c_925]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_965,plain,
% 1.45/1.01      ( v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(sK7,sK3(sK6,X0,X1))
% 1.45/1.01      | v2_struct_0(sK6)
% 1.45/1.01      | ~ v2_pre_topc(sK6)
% 1.45/1.01      | ~ l1_pre_topc(sK6) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_15,c_926]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_969,plain,
% 1.45/1.01      ( ~ r2_hidden(sK7,sK3(sK6,X0,X1))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | v4_pre_topc(sK7,sK6) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_965,c_42,c_41,c_40]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_970,plain,
% 1.45/1.01      ( v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(sK3(sK6,X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(sK7,sK3(sK6,X0,X1)) ),
% 1.45/1.01      inference(renaming,[status(thm)],[c_969]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1245,plain,
% 1.45/1.01      ( v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | r2_hidden(X1,sK7)
% 1.45/1.01      | ~ r2_hidden(sK7,sK3(sK6,X0,X1)) ),
% 1.45/1.01      inference(backward_subsumption_resolution,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_1111,c_970]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2265,plain,
% 1.45/1.01      ( v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
% 1.45/1.01      | ~ r2_hidden(X1_56,k2_pre_topc(sK6,X0_56))
% 1.45/1.01      | r2_hidden(X1_56,sK7)
% 1.45/1.01      | ~ r2_hidden(sK7,sK3(sK6,X0_56,X1_56)) ),
% 1.45/1.01      inference(subtyping,[status(esa)],[c_1245]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2397,plain,
% 1.45/1.01      ( v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(sK5(X1_56,sK6),u1_struct_0(sK6))
% 1.45/1.01      | ~ r2_hidden(sK5(X1_56,sK6),k2_pre_topc(sK6,X0_56))
% 1.45/1.01      | r2_hidden(sK5(X1_56,sK6),sK7)
% 1.45/1.01      | ~ r2_hidden(sK7,sK3(sK6,X0_56,sK5(X1_56,sK6))) ),
% 1.45/1.01      inference(instantiation,[status(thm)],[c_2265]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2411,plain,
% 1.45/1.01      ( v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(sK5(sK7,sK6),u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ r2_hidden(sK5(sK7,sK6),k2_pre_topc(sK6,sK7))
% 1.45/1.01      | r2_hidden(sK5(sK7,sK6),sK7)
% 1.45/1.01      | ~ r2_hidden(sK7,sK3(sK6,sK7,sK5(sK7,sK6))) ),
% 1.45/1.01      inference(instantiation,[status(thm)],[c_2397]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_10,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.45/1.01      | r2_hidden(X0,sK3(X1,X0,X2))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.45/1.01      | v2_struct_0(X1)
% 1.45/1.01      | ~ v2_pre_topc(X1)
% 1.45/1.01      | ~ l1_pre_topc(X1) ),
% 1.45/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1130,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | r2_hidden(X0,sK3(sK6,X0,X1))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | v2_struct_0(sK6)
% 1.45/1.01      | ~ v2_pre_topc(sK6) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_10,c_40]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1134,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | r2_hidden(X0,sK3(sK6,X0,X1))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0)) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_1130,c_42,c_41]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2267,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
% 1.45/1.01      | r2_hidden(X0_56,sK3(sK6,X0_56,X1_56))
% 1.45/1.01      | ~ r2_hidden(X1_56,k2_pre_topc(sK6,X0_56)) ),
% 1.45/1.01      inference(subtyping,[status(esa)],[c_1134]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2398,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(sK5(X1_56,sK6),u1_struct_0(sK6))
% 1.45/1.01      | r2_hidden(X0_56,sK3(sK6,X0_56,sK5(X1_56,sK6)))
% 1.45/1.01      | ~ r2_hidden(sK5(X1_56,sK6),k2_pre_topc(sK6,X0_56)) ),
% 1.45/1.01      inference(instantiation,[status(thm)],[c_2267]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2407,plain,
% 1.45/1.01      ( ~ m1_subset_1(sK5(sK7,sK6),u1_struct_0(sK6))
% 1.45/1.01      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ r2_hidden(sK5(sK7,sK6),k2_pre_topc(sK6,sK7))
% 1.45/1.01      | r2_hidden(sK7,sK3(sK6,sK7,sK5(sK7,sK6))) ),
% 1.45/1.01      inference(instantiation,[status(thm)],[c_2398]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.45/1.01      | r2_hidden(X0,sK2(X1,X0,X2))
% 1.45/1.01      | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
% 1.45/1.01      | v2_struct_0(X1)
% 1.45/1.01      | ~ v2_pre_topc(X1)
% 1.45/1.01      | ~ l1_pre_topc(X1) ),
% 1.45/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1176,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | r2_hidden(X0,sK2(sK6,X0,X1))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0))
% 1.45/1.01      | v2_struct_0(sK6)
% 1.45/1.01      | ~ v2_pre_topc(sK6) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_2,c_40]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1180,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 1.45/1.01      | r2_hidden(X0,sK2(sK6,X0,X1))
% 1.45/1.01      | ~ r2_hidden(X1,k2_pre_topc(sK6,X0)) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_1176,c_42,c_41]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2266,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X1_56,u1_struct_0(sK6))
% 1.45/1.01      | r2_hidden(X0_56,sK2(sK6,X0_56,X1_56))
% 1.45/1.01      | ~ r2_hidden(X1_56,k2_pre_topc(sK6,X0_56)) ),
% 1.45/1.01      inference(subtyping,[status(esa)],[c_1180]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2375,plain,
% 1.45/1.01      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(sK9,u1_struct_0(sK6))
% 1.45/1.01      | r2_hidden(X0_56,sK2(sK6,X0_56,sK9))
% 1.45/1.01      | ~ r2_hidden(sK9,k2_pre_topc(sK6,X0_56)) ),
% 1.45/1.01      inference(instantiation,[status(thm)],[c_2266]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2377,plain,
% 1.45/1.01      ( ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(sK9,u1_struct_0(sK6))
% 1.45/1.01      | r2_hidden(sK7,sK2(sK6,sK7,sK9))
% 1.45/1.01      | ~ r2_hidden(sK9,k2_pre_topc(sK6,sK7)) ),
% 1.45/1.01      inference(instantiation,[status(thm)],[c_2375]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_16,plain,
% 1.45/1.01      ( ~ sP1(X0,X1) | ~ sP0(X1,X0) | v4_pre_topc(X1,X0) ),
% 1.45/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_28,plain,
% 1.45/1.01      ( sP1(X0,X1)
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.45/1.01      | v2_struct_0(X0)
% 1.45/1.01      | ~ v2_pre_topc(X0)
% 1.45/1.01      | ~ l1_pre_topc(X0) ),
% 1.45/1.01      inference(cnf_transformation,[],[f67]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1199,plain,
% 1.45/1.01      ( sP1(sK6,X0)
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | v2_struct_0(sK6)
% 1.45/1.01      | ~ v2_pre_topc(sK6) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_28,c_40]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1203,plain,
% 1.45/1.01      ( sP1(sK6,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_1199,c_42,c_41]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1283,plain,
% 1.45/1.01      ( ~ sP0(X0,sK6)
% 1.45/1.01      | v4_pre_topc(X0,sK6)
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_16,c_1203]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2263,plain,
% 1.45/1.01      ( ~ sP0(X0_56,sK6)
% 1.45/1.01      | v4_pre_topc(X0_56,sK6)
% 1.45/1.01      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.45/1.01      inference(subtyping,[status(esa)],[c_1283]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2319,plain,
% 1.45/1.01      ( ~ sP0(sK7,sK6)
% 1.45/1.01      | v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.45/1.01      inference(instantiation,[status(thm)],[c_2263]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_17,plain,
% 1.45/1.01      ( ~ sP1(X0,X1) | sP0(X1,X0) | ~ v4_pre_topc(X1,X0) ),
% 1.45/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1269,plain,
% 1.45/1.01      ( sP0(X0,sK6)
% 1.45/1.01      | ~ v4_pre_topc(X0,sK6)
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_17,c_1203]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2264,plain,
% 1.45/1.01      ( sP0(X0_56,sK6)
% 1.45/1.01      | ~ v4_pre_topc(X0_56,sK6)
% 1.45/1.01      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.45/1.01      inference(subtyping,[status(esa)],[c_1269]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2316,plain,
% 1.45/1.01      ( sP0(sK7,sK6)
% 1.45/1.01      | ~ v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.45/1.01      inference(instantiation,[status(thm)],[c_2264]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_0,plain,
% 1.45/1.01      ( ~ r1_waybel_7(X0,X1,X2)
% 1.45/1.01      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
% 1.45/1.01      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
% 1.45/1.01      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.45/1.01      | ~ r2_hidden(X3,X1)
% 1.45/1.01      | r2_hidden(X2,k2_pre_topc(X0,X3))
% 1.45/1.01      | v2_struct_0(X0)
% 1.45/1.01      | ~ v2_pre_topc(X0)
% 1.45/1.01      | ~ l1_pre_topc(X0)
% 1.45/1.01      | v1_xboole_0(X1) ),
% 1.45/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_19,plain,
% 1.45/1.01      ( r1_waybel_7(X0,sK4(X1,X0),sK5(X1,X0)) | sP0(X1,X0) ),
% 1.45/1.01      inference(cnf_transformation,[],[f65]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_633,plain,
% 1.45/1.01      ( sP0(X0,X1)
% 1.45/1.01      | ~ v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
% 1.45/1.01      | ~ v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1)))
% 1.45/1.01      | ~ v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1)))
% 1.45/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.45/1.01      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
% 1.45/1.01      | ~ m1_subset_1(sK5(X0,X1),u1_struct_0(X1))
% 1.45/1.01      | ~ r2_hidden(X2,sK4(X0,X1))
% 1.45/1.01      | r2_hidden(sK5(X0,X1),k2_pre_topc(X1,X2))
% 1.45/1.01      | v2_struct_0(X1)
% 1.45/1.01      | ~ v2_pre_topc(X1)
% 1.45/1.01      | ~ l1_pre_topc(X1)
% 1.45/1.01      | v1_xboole_0(sK4(X0,X1)) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_0,c_19]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_26,plain,
% 1.45/1.01      ( sP0(X0,X1) | ~ v1_xboole_0(sK4(X0,X1)) ),
% 1.45/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_25,plain,
% 1.45/1.01      ( sP0(X0,X1)
% 1.45/1.01      | v1_subset_1(sK4(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X1)))) ),
% 1.45/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_24,plain,
% 1.45/1.01      ( sP0(X0,X1)
% 1.45/1.01      | v2_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1))) ),
% 1.45/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_23,plain,
% 1.45/1.01      ( sP0(X0,X1)
% 1.45/1.01      | v13_waybel_0(sK4(X0,X1),k3_yellow_1(k2_struct_0(X1))) ),
% 1.45/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_22,plain,
% 1.45/1.01      ( sP0(X0,X1)
% 1.45/1.01      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
% 1.45/1.01      inference(cnf_transformation,[],[f62]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_20,plain,
% 1.45/1.01      ( sP0(X0,X1) | m1_subset_1(sK5(X0,X1),u1_struct_0(X1)) ),
% 1.45/1.01      inference(cnf_transformation,[],[f64]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_637,plain,
% 1.45/1.01      ( ~ l1_pre_topc(X1)
% 1.45/1.01      | ~ v2_pre_topc(X1)
% 1.45/1.01      | v2_struct_0(X1)
% 1.45/1.01      | r2_hidden(sK5(X0,X1),k2_pre_topc(X1,X2))
% 1.45/1.01      | ~ r2_hidden(X2,sK4(X0,X1))
% 1.45/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.45/1.01      | sP0(X0,X1) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_633,c_26,c_25,c_24,c_23,c_22,c_20]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_638,plain,
% 1.45/1.01      ( sP0(X0,X1)
% 1.45/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.45/1.01      | ~ r2_hidden(X2,sK4(X0,X1))
% 1.45/1.01      | r2_hidden(sK5(X0,X1),k2_pre_topc(X1,X2))
% 1.45/1.01      | v2_struct_0(X1)
% 1.45/1.01      | ~ v2_pre_topc(X1)
% 1.45/1.01      | ~ l1_pre_topc(X1) ),
% 1.45/1.01      inference(renaming,[status(thm)],[c_637]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1030,plain,
% 1.45/1.01      ( sP0(X0,sK6)
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ r2_hidden(X1,sK4(X0,sK6))
% 1.45/1.01      | r2_hidden(sK5(X0,sK6),k2_pre_topc(sK6,X1))
% 1.45/1.01      | v2_struct_0(sK6)
% 1.45/1.01      | ~ v2_pre_topc(sK6) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_638,c_40]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1034,plain,
% 1.45/1.01      ( sP0(X0,sK6)
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ r2_hidden(X1,sK4(X0,sK6))
% 1.45/1.01      | r2_hidden(sK5(X0,sK6),k2_pre_topc(sK6,X1)) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_1030,c_42,c_41]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2270,plain,
% 1.45/1.01      ( sP0(X0_56,sK6)
% 1.45/1.01      | ~ m1_subset_1(X1_56,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ r2_hidden(X1_56,sK4(X0_56,sK6))
% 1.45/1.01      | r2_hidden(sK5(X0_56,sK6),k2_pre_topc(sK6,X1_56)) ),
% 1.45/1.01      inference(subtyping,[status(esa)],[c_1034]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2300,plain,
% 1.45/1.01      ( sP0(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | r2_hidden(sK5(sK7,sK6),k2_pre_topc(sK6,sK7))
% 1.45/1.01      | ~ r2_hidden(sK7,sK4(sK7,sK6)) ),
% 1.45/1.01      inference(instantiation,[status(thm)],[c_2270]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_8,plain,
% 1.45/1.01      ( ~ r2_waybel_7(X0,X1,X2)
% 1.45/1.01      | ~ v3_waybel_7(X1,k3_yellow_1(k2_struct_0(X0)))
% 1.45/1.01      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
% 1.45/1.01      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 1.45/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
% 1.45/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.45/1.01      | ~ r2_hidden(X3,X1)
% 1.45/1.01      | r2_hidden(X2,k2_pre_topc(X0,X3))
% 1.45/1.01      | v2_struct_0(X0)
% 1.45/1.01      | ~ v2_pre_topc(X0)
% 1.45/1.01      | ~ l1_pre_topc(X0)
% 1.45/1.01      | v1_xboole_0(X1) ),
% 1.45/1.01      inference(cnf_transformation,[],[f54]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_30,negated_conjecture,
% 1.45/1.01      ( r2_waybel_7(sK6,sK8,sK9) | ~ v4_pre_topc(sK7,sK6) ),
% 1.45/1.01      inference(cnf_transformation,[],[f80]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_737,plain,
% 1.45/1.01      ( ~ v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6)))))
% 1.45/1.01      | ~ m1_subset_1(sK9,u1_struct_0(sK6))
% 1.45/1.01      | ~ r2_hidden(X0,sK8)
% 1.45/1.01      | r2_hidden(sK9,k2_pre_topc(sK6,X0))
% 1.45/1.01      | v2_struct_0(sK6)
% 1.45/1.01      | ~ v2_pre_topc(sK6)
% 1.45/1.01      | ~ l1_pre_topc(sK6)
% 1.45/1.01      | v1_xboole_0(sK8) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_8,c_30]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_37,negated_conjecture,
% 1.45/1.01      ( ~ v4_pre_topc(sK7,sK6) | ~ v1_xboole_0(sK8) ),
% 1.45/1.01      inference(cnf_transformation,[],[f73]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_36,negated_conjecture,
% 1.45/1.01      ( ~ v4_pre_topc(sK7,sK6)
% 1.45/1.01      | v2_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) ),
% 1.45/1.01      inference(cnf_transformation,[],[f74]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_35,negated_conjecture,
% 1.45/1.01      ( ~ v4_pre_topc(sK7,sK6)
% 1.45/1.01      | v13_waybel_0(sK8,k3_yellow_1(k2_struct_0(sK6))) ),
% 1.45/1.01      inference(cnf_transformation,[],[f75]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_34,negated_conjecture,
% 1.45/1.01      ( ~ v4_pre_topc(sK7,sK6)
% 1.45/1.01      | v3_waybel_7(sK8,k3_yellow_1(k2_struct_0(sK6))) ),
% 1.45/1.01      inference(cnf_transformation,[],[f76]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_33,negated_conjecture,
% 1.45/1.01      ( ~ v4_pre_topc(sK7,sK6)
% 1.45/1.01      | m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK6))))) ),
% 1.45/1.01      inference(cnf_transformation,[],[f77]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_31,negated_conjecture,
% 1.45/1.01      ( ~ v4_pre_topc(sK7,sK6) | m1_subset_1(sK9,u1_struct_0(sK6)) ),
% 1.45/1.01      inference(cnf_transformation,[],[f79]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_741,plain,
% 1.45/1.01      ( ~ v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ r2_hidden(X0,sK8)
% 1.45/1.01      | r2_hidden(sK9,k2_pre_topc(sK6,X0)) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_737,c_42,c_41,c_40,c_37,c_36,c_35,c_34,c_33,c_31]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2272,plain,
% 1.45/1.01      ( ~ v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ r2_hidden(X0_56,sK8)
% 1.45/1.01      | r2_hidden(sK9,k2_pre_topc(sK6,X0_56)) ),
% 1.45/1.01      inference(subtyping,[status(esa)],[c_741]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2296,plain,
% 1.45/1.01      ( ~ v4_pre_topc(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ r2_hidden(sK7,sK8)
% 1.45/1.01      | r2_hidden(sK9,k2_pre_topc(sK6,sK7)) ),
% 1.45/1.01      inference(instantiation,[status(thm)],[c_2272]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_21,plain,
% 1.45/1.01      ( sP0(X0,X1) | r2_hidden(X0,sK4(X0,X1)) ),
% 1.45/1.01      inference(cnf_transformation,[],[f63]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2278,plain,
% 1.45/1.01      ( sP0(X0_56,X0_57) | r2_hidden(X0_56,sK4(X0_56,X0_57)) ),
% 1.45/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2288,plain,
% 1.45/1.01      ( sP0(sK7,sK6) | r2_hidden(sK7,sK4(sK7,sK6)) ),
% 1.45/1.01      inference(instantiation,[status(thm)],[c_2278]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2279,plain,
% 1.45/1.01      ( sP0(X0_56,X0_57)
% 1.45/1.01      | m1_subset_1(sK5(X0_56,X0_57),u1_struct_0(X0_57)) ),
% 1.45/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2285,plain,
% 1.45/1.01      ( sP0(sK7,sK6) | m1_subset_1(sK5(sK7,sK6),u1_struct_0(sK6)) ),
% 1.45/1.01      inference(instantiation,[status(thm)],[c_2279]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_18,plain,
% 1.45/1.01      ( sP0(X0,X1) | ~ r2_hidden(sK5(X0,X1),X0) ),
% 1.45/1.01      inference(cnf_transformation,[],[f66]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2280,plain,
% 1.45/1.01      ( sP0(X0_56,X0_57) | ~ r2_hidden(sK5(X0_56,X0_57),X0_56) ),
% 1.45/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_2282,plain,
% 1.45/1.01      ( sP0(sK7,sK6) | ~ r2_hidden(sK5(sK7,sK6),sK7) ),
% 1.45/1.01      inference(instantiation,[status(thm)],[c_2280]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_29,negated_conjecture,
% 1.45/1.01      ( ~ v4_pre_topc(sK7,sK6) | ~ r2_hidden(sK9,sK7) ),
% 1.45/1.01      inference(cnf_transformation,[],[f81]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1518,plain,
% 1.45/1.01      ( ~ sP0(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | ~ r2_hidden(sK9,sK7) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_29,c_1283]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_39,negated_conjecture,
% 1.45/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 1.45/1.01      inference(cnf_transformation,[],[f71]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1520,plain,
% 1.45/1.01      ( ~ sP0(sK7,sK6) | ~ r2_hidden(sK9,sK7) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_1518,c_39]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1505,plain,
% 1.45/1.01      ( ~ sP0(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | m1_subset_1(sK9,u1_struct_0(sK6)) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_31,c_1283]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1507,plain,
% 1.45/1.01      ( ~ sP0(sK7,sK6) | m1_subset_1(sK9,u1_struct_0(sK6)) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_1505,c_39]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_32,negated_conjecture,
% 1.45/1.01      ( ~ v4_pre_topc(sK7,sK6) | r2_hidden(sK7,sK8) ),
% 1.45/1.01      inference(cnf_transformation,[],[f78]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1492,plain,
% 1.45/1.01      ( ~ sP0(sK7,sK6)
% 1.45/1.01      | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
% 1.45/1.01      | r2_hidden(sK7,sK8) ),
% 1.45/1.01      inference(resolution,[status(thm)],[c_32,c_1283]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(c_1494,plain,
% 1.45/1.01      ( ~ sP0(sK7,sK6) | r2_hidden(sK7,sK8) ),
% 1.45/1.01      inference(global_propositional_subsumption,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_1492,c_39]) ).
% 1.45/1.01  
% 1.45/1.01  cnf(contradiction,plain,
% 1.45/1.01      ( $false ),
% 1.45/1.01      inference(minisat,
% 1.45/1.01                [status(thm)],
% 1.45/1.01                [c_2452,c_2411,c_2407,c_2377,c_2319,c_2316,c_2300,c_2296,
% 1.45/1.01                 c_2288,c_2285,c_2282,c_1520,c_1507,c_1494,c_39]) ).
% 1.45/1.01  
% 1.45/1.01  
% 1.45/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.45/1.01  
% 1.45/1.01  ------                               Statistics
% 1.45/1.01  
% 1.45/1.01  ------ General
% 1.45/1.01  
% 1.45/1.01  abstr_ref_over_cycles:                  0
% 1.45/1.01  abstr_ref_under_cycles:                 0
% 1.45/1.01  gc_basic_clause_elim:                   0
% 1.45/1.01  forced_gc_time:                         0
% 1.45/1.01  parsing_time:                           0.013
% 1.45/1.01  unif_index_cands_time:                  0.
% 1.45/1.01  unif_index_add_time:                    0.
% 1.45/1.01  orderings_time:                         0.
% 1.45/1.01  out_proof_time:                         0.014
% 1.45/1.01  total_time:                             0.086
% 1.45/1.01  num_of_symbols:                         59
% 1.45/1.01  num_of_terms:                           1603
% 1.45/1.01  
% 1.45/1.01  ------ Preprocessing
% 1.45/1.01  
% 1.45/1.01  num_of_splits:                          0
% 1.45/1.01  num_of_split_atoms:                     0
% 1.45/1.01  num_of_reused_defs:                     0
% 1.45/1.01  num_eq_ax_congr_red:                    0
% 1.45/1.01  num_of_sem_filtered_clauses:            4
% 1.45/1.01  num_of_subtypes:                        3
% 1.45/1.01  monotx_restored_types:                  0
% 1.45/1.01  sat_num_of_epr_types:                   0
% 1.45/1.01  sat_num_of_non_cyclic_types:            0
% 1.45/1.01  sat_guarded_non_collapsed_types:        0
% 1.45/1.01  num_pure_diseq_elim:                    0
% 1.45/1.01  simp_replaced_by:                       0
% 1.45/1.01  res_preprocessed:                       83
% 1.45/1.01  prep_upred:                             0
% 1.45/1.01  prep_unflattend:                        0
% 1.45/1.01  smt_new_axioms:                         0
% 1.45/1.01  pred_elim_cands:                        4
% 1.45/1.01  pred_elim:                              11
% 1.45/1.01  pred_elim_cl:                           21
% 1.45/1.01  pred_elim_cycles:                       15
% 1.45/1.01  merged_defs:                            0
% 1.45/1.01  merged_defs_ncl:                        0
% 1.45/1.01  bin_hyper_res:                          0
% 1.45/1.01  prep_cycles:                            3
% 1.45/1.01  pred_elim_time:                         0.023
% 1.45/1.01  splitting_time:                         0.
% 1.45/1.01  sem_filter_time:                        0.
% 1.45/1.01  monotx_time:                            0.
% 1.45/1.01  subtype_inf_time:                       0.
% 1.45/1.01  
% 1.45/1.01  ------ Problem properties
% 1.45/1.01  
% 1.45/1.01  clauses:                                18
% 1.45/1.01  conjectures:                            4
% 1.45/1.01  epr:                                    2
% 1.45/1.01  horn:                                   13
% 1.45/1.01  ground:                                 4
% 1.45/1.01  unary:                                  1
% 1.45/1.01  binary:                                 6
% 1.45/1.01  lits:                                   63
% 1.45/1.01  lits_eq:                                0
% 1.45/1.01  fd_pure:                                0
% 1.45/1.01  fd_pseudo:                              0
% 1.45/1.01  fd_cond:                                0
% 1.45/1.01  fd_pseudo_cond:                         0
% 1.45/1.01  ac_symbols:                             0
% 1.45/1.01  
% 1.45/1.01  ------ Propositional Solver
% 1.45/1.01  
% 1.45/1.01  prop_solver_calls:                      17
% 1.45/1.01  prop_fast_solver_calls:                 1198
% 1.45/1.01  smt_solver_calls:                       0
% 1.45/1.01  smt_fast_solver_calls:                  0
% 1.45/1.01  prop_num_of_clauses:                    463
% 1.45/1.01  prop_preprocess_simplified:             2732
% 1.45/1.01  prop_fo_subsumed:                       70
% 1.45/1.01  prop_solver_time:                       0.
% 1.45/1.01  smt_solver_time:                        0.
% 1.45/1.01  smt_fast_solver_time:                   0.
% 1.45/1.01  prop_fast_solver_time:                  0.
% 1.45/1.01  prop_unsat_core_time:                   0.
% 1.45/1.01  
% 1.45/1.01  ------ QBF
% 1.45/1.01  
% 1.45/1.01  qbf_q_res:                              0
% 1.45/1.01  qbf_num_tautologies:                    0
% 1.45/1.01  qbf_prep_cycles:                        0
% 1.45/1.01  
% 1.45/1.01  ------ BMC1
% 1.45/1.01  
% 1.45/1.01  bmc1_current_bound:                     -1
% 1.45/1.01  bmc1_last_solved_bound:                 -1
% 1.45/1.01  bmc1_unsat_core_size:                   -1
% 1.45/1.01  bmc1_unsat_core_parents_size:           -1
% 1.45/1.01  bmc1_merge_next_fun:                    0
% 1.45/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.45/1.01  
% 1.45/1.01  ------ Instantiation
% 1.45/1.01  
% 1.45/1.01  inst_num_of_clauses:                    34
% 1.45/1.01  inst_num_in_passive:                    2
% 1.45/1.01  inst_num_in_active:                     26
% 1.45/1.01  inst_num_in_unprocessed:                5
% 1.45/1.01  inst_num_of_loops:                      37
% 1.45/1.01  inst_num_of_learning_restarts:          0
% 1.45/1.01  inst_num_moves_active_passive:          9
% 1.45/1.01  inst_lit_activity:                      0
% 1.45/1.01  inst_lit_activity_moves:                0
% 1.45/1.01  inst_num_tautologies:                   0
% 1.45/1.01  inst_num_prop_implied:                  0
% 1.45/1.01  inst_num_existing_simplified:           0
% 1.45/1.01  inst_num_eq_res_simplified:             0
% 1.45/1.01  inst_num_child_elim:                    0
% 1.45/1.01  inst_num_of_dismatching_blockings:      0
% 1.45/1.01  inst_num_of_non_proper_insts:           12
% 1.45/1.01  inst_num_of_duplicates:                 0
% 1.45/1.01  inst_inst_num_from_inst_to_res:         0
% 1.45/1.01  inst_dismatching_checking_time:         0.
% 1.45/1.01  
% 1.45/1.01  ------ Resolution
% 1.45/1.01  
% 1.45/1.01  res_num_of_clauses:                     0
% 1.45/1.01  res_num_in_passive:                     0
% 1.45/1.01  res_num_in_active:                      0
% 1.45/1.01  res_num_of_loops:                       86
% 1.45/1.01  res_forward_subset_subsumed:            0
% 1.45/1.01  res_backward_subset_subsumed:           0
% 1.45/1.01  res_forward_subsumed:                   0
% 1.45/1.01  res_backward_subsumed:                  0
% 1.45/1.01  res_forward_subsumption_resolution:     15
% 1.45/1.01  res_backward_subsumption_resolution:    1
% 1.45/1.01  res_clause_to_clause_subsumption:       107
% 1.45/1.01  res_orphan_elimination:                 0
% 1.45/1.01  res_tautology_del:                      4
% 1.45/1.01  res_num_eq_res_simplified:              0
% 1.45/1.01  res_num_sel_changes:                    0
% 1.45/1.01  res_moves_from_active_to_pass:          0
% 1.45/1.01  
% 1.45/1.01  ------ Superposition
% 1.45/1.01  
% 1.45/1.01  sup_time_total:                         0.
% 1.45/1.01  sup_time_generating:                    0.
% 1.45/1.01  sup_time_sim_full:                      0.
% 1.45/1.01  sup_time_sim_immed:                     0.
% 1.45/1.01  
% 1.45/1.01  sup_num_of_clauses:                     0
% 1.45/1.01  sup_num_in_active:                      0
% 1.45/1.01  sup_num_in_passive:                     0
% 1.45/1.01  sup_num_of_loops:                       0
% 1.45/1.01  sup_fw_superposition:                   0
% 1.45/1.01  sup_bw_superposition:                   0
% 1.45/1.01  sup_immediate_simplified:               0
% 1.45/1.01  sup_given_eliminated:                   0
% 1.45/1.01  comparisons_done:                       0
% 1.45/1.01  comparisons_avoided:                    0
% 1.45/1.01  
% 1.45/1.01  ------ Simplifications
% 1.45/1.01  
% 1.45/1.01  
% 1.45/1.01  sim_fw_subset_subsumed:                 0
% 1.45/1.01  sim_bw_subset_subsumed:                 0
% 1.45/1.01  sim_fw_subsumed:                        0
% 1.45/1.01  sim_bw_subsumed:                        0
% 1.45/1.01  sim_fw_subsumption_res:                 0
% 1.45/1.01  sim_bw_subsumption_res:                 0
% 1.45/1.01  sim_tautology_del:                      0
% 1.45/1.01  sim_eq_tautology_del:                   0
% 1.45/1.01  sim_eq_res_simp:                        0
% 1.45/1.01  sim_fw_demodulated:                     0
% 1.45/1.01  sim_bw_demodulated:                     0
% 1.45/1.01  sim_light_normalised:                   0
% 1.45/1.01  sim_joinable_taut:                      0
% 1.45/1.01  sim_joinable_simp:                      0
% 1.45/1.01  sim_ac_normalised:                      0
% 1.45/1.01  sim_smt_subsumption:                    0
% 1.45/1.01  
%------------------------------------------------------------------------------
