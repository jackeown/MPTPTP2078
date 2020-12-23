%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:35 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 566 expanded)
%              Number of clauses        :   41 (  86 expanded)
%              Number of leaves         :   11 ( 225 expanded)
%              Depth                    :   16
%              Number of atoms          :  602 (7674 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   30 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
             => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                      & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                      & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                      & ~ v1_xboole_0(X3) )
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r2_waybel_7(X0,X3,X4)
                                & r2_hidden(X4,X2) ) )
                        & r2_hidden(X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
               => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                        & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                        & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                        & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ~ ( r2_waybel_7(X0,X3,X4)
                                  & r2_hidden(X4,X2) ) )
                          & r2_hidden(X1,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_waybel_7(X0,X3,X4)
                      | ~ r2_hidden(X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                  & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                  & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_waybel_7(X0,X3,X4)
                      | ~ r2_hidden(X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                  & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                  & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_waybel_7(X0,X3,X4)
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
          & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
          & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
          & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X3) )
     => ( ! [X4] :
            ( ~ r2_waybel_7(X0,sK5,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(X1,sK5)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
        & v3_waybel_7(sK5,k3_yellow_1(u1_struct_0(X0)))
        & v13_waybel_0(sK5,k3_yellow_1(u1_struct_0(X0)))
        & v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r2_waybel_7(X0,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X1,X3)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
              & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
              & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
              & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X3) )
          & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r2_waybel_7(X0,X3,X4)
                | ~ r2_hidden(X4,sK4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X1,X3)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
            & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
            & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
            & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X3) )
        & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,sK4)
        & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_waybel_7(X0,X3,X4)
                      | ~ r2_hidden(X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                  & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                  & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r2_waybel_7(X0,X3,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(sK3,X3)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(X3) )
            & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),sK3,X2)
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
        & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_waybel_7(X0,X3,X4)
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                    & ~ v1_xboole_0(X3) )
                & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_waybel_7(sK2,X3,X4)
                      | ~ r2_hidden(X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2)))))
                  & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(sK2)))
                  & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(sK2)))
                  & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(sK2)))
                  & ~ v1_xboole_0(X3) )
              & r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X1,X2)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ! [X4] :
        ( ~ r2_waybel_7(sK2,sK5,X4)
        | ~ r2_hidden(X4,sK4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
    & r2_hidden(sK3,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2)))))
    & v3_waybel_7(sK5,k3_yellow_1(u1_struct_0(sK2)))
    & v13_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
    & v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
    & ~ v1_xboole_0(sK5)
    & r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),sK3,sK4)
    & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f29,f28,f27,f26])).

fof(f52,plain,(
    r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),sK3,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
             => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                      & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                      & v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
                      & ~ v1_xboole_0(X3) )
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_waybel_7(X0,X3,X4)
                                & r2_hidden(X4,X2) ) )
                        & r2_hidden(X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( r1_waybel_7(X0,X3,X4)
                      & r2_hidden(X4,X2)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                  | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
                  | v1_xboole_0(X3) )
              | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( r1_waybel_7(X0,X3,X4)
                      & r2_hidden(X4,X2)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                  | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
                  | v1_xboole_0(X3) )
              | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f24,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( r1_waybel_7(X0,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r1_waybel_7(X0,X3,sK1(X0,X2,X3))
        & r2_hidden(sK1(X0,X2,X3),X2)
        & m1_subset_1(sK1(X0,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_waybel_7(X0,X3,sK1(X0,X2,X3))
                    & r2_hidden(sK1(X0,X2,X3),X2)
                    & m1_subset_1(sK1(X0,X2,X3),u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                  | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
                  | v1_xboole_0(X3) )
              | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f24])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK1(X0,X2,X3),X2)
      | ~ r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | v1_xboole_0(X3)
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    v13_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2))))) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    v3_waybel_7(sK5,k3_yellow_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f33,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_waybel_7(X1,X0)
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | ~ v3_waybel_7(X1,X0)
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | ~ v3_waybel_7(X1,X0)
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_waybel_7(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f37,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK1(X0,X2,X3),u1_struct_0(X0))
      | ~ r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | v1_xboole_0(X3)
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_7(X0,X3,sK1(X0,X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | v1_xboole_0(X3)
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
            & v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( r1_waybel_7(X0,X1,X2)
            <=> r2_waybel_7(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_7(X0,X1,X2)
            <=> r2_waybel_7(X0,X1,X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
          | ~ v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_7(X0,X1,X2)
            <=> r2_waybel_7(X0,X1,X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
          | ~ v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_7(X0,X1,X2)
                | ~ r2_waybel_7(X0,X1,X2) )
              & ( r2_waybel_7(X0,X1,X2)
                | ~ r1_waybel_7(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
          | ~ v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | ~ r1_waybel_7(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
      | ~ v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X4] :
      ( ~ r2_waybel_7(sK2,sK5,X4)
      | ~ r2_hidden(X4,sK4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    r2_hidden(sK3,sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    m1_subset_1(sK4,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_23,negated_conjecture,
    ( r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),sK3,sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_14,plain,
    ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
    | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
    | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | r2_hidden(sK1(X0,X2,X3),X2)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_xboole_0(X3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,negated_conjecture,
    ( v13_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_450,plain,
    ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
    | ~ v1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2)))))
    | ~ v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,sK5)
    | r2_hidden(sK1(sK2,X1,sK5),X1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_14,c_20])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,negated_conjecture,
    ( v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2))))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_19,negated_conjecture,
    ( v3_waybel_7(sK5,k3_yellow_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2,plain,
    ( l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,plain,
    ( v1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X0,X1)
    | ~ v3_waybel_7(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_276,plain,
    ( v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v3_waybel_7(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | v2_struct_0(k3_yellow_1(X1))
    | ~ v3_orders_2(k3_yellow_1(X1))
    | ~ v4_orders_2(k3_yellow_1(X1))
    | ~ v5_orders_2(k3_yellow_1(X1))
    | v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_2,c_9])).

cnf(c_3,plain,
    ( v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4,plain,
    ( v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_5,plain,
    ( v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_6,plain,
    ( ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_300,plain,
    ( v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v3_waybel_7(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | v1_xboole_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_276,c_3,c_4,c_5,c_6])).

cnf(c_351,plain,
    ( v1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2)))))
    | ~ v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
    | ~ v13_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_19,c_300])).

cnf(c_454,plain,
    ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ r2_hidden(X0,sK5)
    | r2_hidden(sK1(sK2,X1,sK5),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_28,c_27,c_26,c_22,c_21,c_20,c_18,c_351])).

cnf(c_524,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | r2_hidden(sK1(sK2,sK4,sK5),sK4)
    | ~ r2_hidden(sK3,sK5) ),
    inference(resolution,[status(thm)],[c_23,c_454])).

cnf(c_15,plain,
    ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
    | m1_subset_1(sK1(X0,X2,X3),u1_struct_0(X0))
    | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
    | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_xboole_0(X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_424,plain,
    ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
    | ~ v1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | m1_subset_1(sK1(sK2,X1,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2)))))
    | ~ v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,sK5)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_15,c_20])).

cnf(c_428,plain,
    ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | m1_subset_1(sK1(sK2,X1,sK5),u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_424,c_28,c_27,c_26,c_22,c_21,c_20,c_18,c_351])).

cnf(c_13,plain,
    ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
    | r1_waybel_7(X0,X3,sK1(X0,X2,X3))
    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
    | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
    | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
    | ~ r2_hidden(X1,X3)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_xboole_0(X3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_12,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ r1_waybel_7(X0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
    | ~ v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
    | ~ v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
    | ~ v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_317,plain,
    ( r2_waybel_7(sK2,sK5,X0)
    | ~ r1_waybel_7(sK2,sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2)))))
    | ~ v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
    | ~ v13_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_12,c_19])).

cnf(c_321,plain,
    ( ~ r1_waybel_7(sK2,sK5,X0)
    | r2_waybel_7(sK2,sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_317,c_28,c_27,c_26,c_22,c_21,c_20,c_18])).

cnf(c_322,plain,
    ( r2_waybel_7(sK2,sK5,X0)
    | ~ r1_waybel_7(sK2,sK5,X0) ),
    inference(renaming,[status(thm)],[c_321])).

cnf(c_16,negated_conjecture,
    ( ~ r2_waybel_7(sK2,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_370,plain,
    ( ~ r1_waybel_7(sK2,sK5,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK4) ),
    inference(resolution,[status(thm)],[c_322,c_16])).

cnf(c_388,plain,
    ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
    | ~ v1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ m1_subset_1(sK1(sK2,X1,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2)))))
    | ~ v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
    | ~ v13_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(sK1(sK2,X1,sK5),sK4)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v1_xboole_0(sK5) ),
    inference(resolution,[status(thm)],[c_13,c_370])).

cnf(c_392,plain,
    ( ~ m1_subset_1(sK1(sK2,X1,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(sK1(sK2,X1,sK5),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_28,c_27,c_26,c_22,c_21,c_20,c_18,c_351])).

cnf(c_393,plain,
    ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ m1_subset_1(sK1(sK2,X1,sK5),u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(sK1(sK2,X1,sK5),sK4) ),
    inference(renaming,[status(thm)],[c_392])).

cnf(c_480,plain,
    ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(sK1(sK2,X1,sK5),sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_428,c_393])).

cnf(c_514,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
    | ~ r2_hidden(sK1(sK2,sK4,sK5),sK4)
    | ~ r2_hidden(sK3,sK5) ),
    inference(resolution,[status(thm)],[c_23,c_480])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK3,sK5) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))) ),
    inference(cnf_transformation,[],[f50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_524,c_514,c_17,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:39:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 0.36/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.36/1.03  
% 0.36/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.36/1.03  
% 0.36/1.03  ------  iProver source info
% 0.36/1.03  
% 0.36/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.36/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.36/1.03  git: non_committed_changes: false
% 0.36/1.03  git: last_make_outside_of_git: false
% 0.36/1.03  
% 0.36/1.03  ------ 
% 0.36/1.03  
% 0.36/1.03  ------ Input Options
% 0.36/1.03  
% 0.36/1.03  --out_options                           all
% 0.36/1.03  --tptp_safe_out                         true
% 0.36/1.03  --problem_path                          ""
% 0.36/1.03  --include_path                          ""
% 0.36/1.03  --clausifier                            res/vclausify_rel
% 0.36/1.03  --clausifier_options                    --mode clausify
% 0.36/1.03  --stdin                                 false
% 0.36/1.03  --stats_out                             all
% 0.36/1.03  
% 0.36/1.03  ------ General Options
% 0.36/1.03  
% 0.36/1.03  --fof                                   false
% 0.36/1.03  --time_out_real                         305.
% 0.36/1.03  --time_out_virtual                      -1.
% 0.36/1.03  --symbol_type_check                     false
% 0.36/1.03  --clausify_out                          false
% 0.36/1.03  --sig_cnt_out                           false
% 0.36/1.03  --trig_cnt_out                          false
% 0.36/1.03  --trig_cnt_out_tolerance                1.
% 0.36/1.03  --trig_cnt_out_sk_spl                   false
% 0.36/1.03  --abstr_cl_out                          false
% 0.36/1.03  
% 0.36/1.03  ------ Global Options
% 0.36/1.03  
% 0.36/1.03  --schedule                              default
% 0.36/1.03  --add_important_lit                     false
% 0.36/1.03  --prop_solver_per_cl                    1000
% 0.36/1.03  --min_unsat_core                        false
% 0.36/1.03  --soft_assumptions                      false
% 0.36/1.03  --soft_lemma_size                       3
% 0.36/1.03  --prop_impl_unit_size                   0
% 0.36/1.03  --prop_impl_unit                        []
% 0.36/1.03  --share_sel_clauses                     true
% 0.36/1.03  --reset_solvers                         false
% 0.36/1.03  --bc_imp_inh                            [conj_cone]
% 0.36/1.03  --conj_cone_tolerance                   3.
% 0.36/1.03  --extra_neg_conj                        none
% 0.36/1.03  --large_theory_mode                     true
% 0.36/1.03  --prolific_symb_bound                   200
% 0.36/1.03  --lt_threshold                          2000
% 0.36/1.03  --clause_weak_htbl                      true
% 0.36/1.03  --gc_record_bc_elim                     false
% 0.36/1.03  
% 0.36/1.03  ------ Preprocessing Options
% 0.36/1.03  
% 0.36/1.03  --preprocessing_flag                    true
% 0.36/1.03  --time_out_prep_mult                    0.1
% 0.36/1.03  --splitting_mode                        input
% 0.36/1.03  --splitting_grd                         true
% 0.36/1.03  --splitting_cvd                         false
% 0.36/1.03  --splitting_cvd_svl                     false
% 0.36/1.03  --splitting_nvd                         32
% 0.36/1.03  --sub_typing                            true
% 0.36/1.03  --prep_gs_sim                           true
% 0.36/1.03  --prep_unflatten                        true
% 0.36/1.03  --prep_res_sim                          true
% 0.36/1.03  --prep_upred                            true
% 0.36/1.03  --prep_sem_filter                       exhaustive
% 0.36/1.03  --prep_sem_filter_out                   false
% 0.36/1.03  --pred_elim                             true
% 0.36/1.03  --res_sim_input                         true
% 0.36/1.03  --eq_ax_congr_red                       true
% 0.36/1.03  --pure_diseq_elim                       true
% 0.36/1.03  --brand_transform                       false
% 0.36/1.03  --non_eq_to_eq                          false
% 0.36/1.03  --prep_def_merge                        true
% 0.36/1.03  --prep_def_merge_prop_impl              false
% 0.36/1.03  --prep_def_merge_mbd                    true
% 0.36/1.03  --prep_def_merge_tr_red                 false
% 0.36/1.03  --prep_def_merge_tr_cl                  false
% 0.36/1.03  --smt_preprocessing                     true
% 0.36/1.03  --smt_ac_axioms                         fast
% 0.36/1.03  --preprocessed_out                      false
% 0.36/1.03  --preprocessed_stats                    false
% 0.36/1.03  
% 0.36/1.03  ------ Abstraction refinement Options
% 0.36/1.03  
% 0.36/1.03  --abstr_ref                             []
% 0.36/1.03  --abstr_ref_prep                        false
% 0.36/1.03  --abstr_ref_until_sat                   false
% 0.36/1.03  --abstr_ref_sig_restrict                funpre
% 0.36/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.36/1.03  --abstr_ref_under                       []
% 0.36/1.03  
% 0.36/1.03  ------ SAT Options
% 0.36/1.03  
% 0.36/1.03  --sat_mode                              false
% 0.36/1.03  --sat_fm_restart_options                ""
% 0.36/1.03  --sat_gr_def                            false
% 0.36/1.03  --sat_epr_types                         true
% 0.36/1.03  --sat_non_cyclic_types                  false
% 0.36/1.03  --sat_finite_models                     false
% 0.36/1.03  --sat_fm_lemmas                         false
% 0.36/1.03  --sat_fm_prep                           false
% 0.36/1.03  --sat_fm_uc_incr                        true
% 0.36/1.03  --sat_out_model                         small
% 0.36/1.03  --sat_out_clauses                       false
% 0.36/1.03  
% 0.36/1.03  ------ QBF Options
% 0.36/1.03  
% 0.36/1.03  --qbf_mode                              false
% 0.36/1.03  --qbf_elim_univ                         false
% 0.36/1.03  --qbf_dom_inst                          none
% 0.36/1.03  --qbf_dom_pre_inst                      false
% 0.36/1.03  --qbf_sk_in                             false
% 0.36/1.03  --qbf_pred_elim                         true
% 0.36/1.03  --qbf_split                             512
% 0.36/1.03  
% 0.36/1.03  ------ BMC1 Options
% 0.36/1.03  
% 0.36/1.03  --bmc1_incremental                      false
% 0.36/1.03  --bmc1_axioms                           reachable_all
% 0.36/1.03  --bmc1_min_bound                        0
% 0.36/1.03  --bmc1_max_bound                        -1
% 0.36/1.03  --bmc1_max_bound_default                -1
% 0.36/1.03  --bmc1_symbol_reachability              true
% 0.36/1.03  --bmc1_property_lemmas                  false
% 0.36/1.03  --bmc1_k_induction                      false
% 0.36/1.03  --bmc1_non_equiv_states                 false
% 0.36/1.03  --bmc1_deadlock                         false
% 0.36/1.03  --bmc1_ucm                              false
% 0.36/1.03  --bmc1_add_unsat_core                   none
% 0.36/1.03  --bmc1_unsat_core_children              false
% 0.36/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.36/1.03  --bmc1_out_stat                         full
% 0.36/1.03  --bmc1_ground_init                      false
% 0.36/1.03  --bmc1_pre_inst_next_state              false
% 0.36/1.03  --bmc1_pre_inst_state                   false
% 0.36/1.03  --bmc1_pre_inst_reach_state             false
% 0.36/1.03  --bmc1_out_unsat_core                   false
% 0.36/1.03  --bmc1_aig_witness_out                  false
% 0.36/1.03  --bmc1_verbose                          false
% 0.36/1.03  --bmc1_dump_clauses_tptp                false
% 0.36/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.36/1.03  --bmc1_dump_file                        -
% 0.36/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.36/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.36/1.03  --bmc1_ucm_extend_mode                  1
% 0.36/1.03  --bmc1_ucm_init_mode                    2
% 0.36/1.03  --bmc1_ucm_cone_mode                    none
% 0.36/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.36/1.03  --bmc1_ucm_relax_model                  4
% 0.36/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.36/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.36/1.03  --bmc1_ucm_layered_model                none
% 0.36/1.03  --bmc1_ucm_max_lemma_size               10
% 0.36/1.03  
% 0.36/1.03  ------ AIG Options
% 0.36/1.03  
% 0.36/1.03  --aig_mode                              false
% 0.36/1.03  
% 0.36/1.03  ------ Instantiation Options
% 0.36/1.03  
% 0.36/1.03  --instantiation_flag                    true
% 0.36/1.03  --inst_sos_flag                         false
% 0.36/1.03  --inst_sos_phase                        true
% 0.36/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.36/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.36/1.03  --inst_lit_sel_side                     num_symb
% 0.36/1.03  --inst_solver_per_active                1400
% 0.36/1.03  --inst_solver_calls_frac                1.
% 0.36/1.03  --inst_passive_queue_type               priority_queues
% 0.36/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.36/1.03  --inst_passive_queues_freq              [25;2]
% 0.36/1.03  --inst_dismatching                      true
% 0.36/1.03  --inst_eager_unprocessed_to_passive     true
% 0.36/1.03  --inst_prop_sim_given                   true
% 0.36/1.03  --inst_prop_sim_new                     false
% 0.36/1.03  --inst_subs_new                         false
% 0.36/1.03  --inst_eq_res_simp                      false
% 0.36/1.03  --inst_subs_given                       false
% 0.36/1.03  --inst_orphan_elimination               true
% 0.36/1.03  --inst_learning_loop_flag               true
% 0.36/1.03  --inst_learning_start                   3000
% 0.36/1.03  --inst_learning_factor                  2
% 0.36/1.03  --inst_start_prop_sim_after_learn       3
% 0.36/1.03  --inst_sel_renew                        solver
% 0.36/1.03  --inst_lit_activity_flag                true
% 0.36/1.03  --inst_restr_to_given                   false
% 0.36/1.03  --inst_activity_threshold               500
% 0.36/1.03  --inst_out_proof                        true
% 0.36/1.03  
% 0.36/1.03  ------ Resolution Options
% 0.36/1.03  
% 0.36/1.03  --resolution_flag                       true
% 0.36/1.03  --res_lit_sel                           adaptive
% 0.36/1.03  --res_lit_sel_side                      none
% 0.36/1.03  --res_ordering                          kbo
% 0.36/1.03  --res_to_prop_solver                    active
% 0.36/1.03  --res_prop_simpl_new                    false
% 0.36/1.03  --res_prop_simpl_given                  true
% 0.36/1.03  --res_passive_queue_type                priority_queues
% 0.36/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.36/1.03  --res_passive_queues_freq               [15;5]
% 0.36/1.03  --res_forward_subs                      full
% 0.36/1.03  --res_backward_subs                     full
% 0.36/1.03  --res_forward_subs_resolution           true
% 0.36/1.03  --res_backward_subs_resolution          true
% 0.36/1.03  --res_orphan_elimination                true
% 0.36/1.03  --res_time_limit                        2.
% 0.36/1.03  --res_out_proof                         true
% 0.36/1.03  
% 0.36/1.03  ------ Superposition Options
% 0.36/1.03  
% 0.36/1.03  --superposition_flag                    true
% 0.36/1.03  --sup_passive_queue_type                priority_queues
% 0.36/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.36/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.36/1.03  --demod_completeness_check              fast
% 0.36/1.03  --demod_use_ground                      true
% 0.36/1.03  --sup_to_prop_solver                    passive
% 0.36/1.03  --sup_prop_simpl_new                    true
% 0.36/1.03  --sup_prop_simpl_given                  true
% 0.36/1.03  --sup_fun_splitting                     false
% 0.36/1.03  --sup_smt_interval                      50000
% 0.36/1.03  
% 0.36/1.03  ------ Superposition Simplification Setup
% 0.36/1.03  
% 0.36/1.03  --sup_indices_passive                   []
% 0.36/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.36/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.03  --sup_full_bw                           [BwDemod]
% 0.36/1.03  --sup_immed_triv                        [TrivRules]
% 0.36/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.03  --sup_immed_bw_main                     []
% 0.36/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.36/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.03  
% 0.36/1.03  ------ Combination Options
% 0.36/1.03  
% 0.36/1.03  --comb_res_mult                         3
% 0.36/1.03  --comb_sup_mult                         2
% 0.36/1.03  --comb_inst_mult                        10
% 0.36/1.03  
% 0.36/1.03  ------ Debug Options
% 0.36/1.03  
% 0.36/1.03  --dbg_backtrace                         false
% 0.36/1.03  --dbg_dump_prop_clauses                 false
% 0.36/1.03  --dbg_dump_prop_clauses_file            -
% 0.36/1.03  --dbg_out_stat                          false
% 0.36/1.03  ------ Parsing...
% 0.36/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.36/1.03  
% 0.36/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s
% 0.36/1.03  
% 0.36/1.03  % SZS status Theorem for theBenchmark.p
% 0.36/1.03  
% 0.36/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.36/1.03  
% 0.36/1.03  fof(f7,conjecture,(
% 0.36/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) => (r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_waybel_7(X0,X3,X4) & r2_hidden(X4,X2))) & r2_hidden(X1,X3)))))))),
% 0.36/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.03  
% 0.36/1.03  fof(f8,negated_conjecture,(
% 0.36/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) => (r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_waybel_7(X0,X3,X4) & r2_hidden(X4,X2))) & r2_hidden(X1,X3)))))))),
% 0.36/1.03    inference(negated_conjecture,[],[f7])).
% 0.36/1.03  
% 0.36/1.03  fof(f17,plain,(
% 0.36/1.03    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : ((~r2_waybel_7(X0,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X3))) & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.36/1.03    inference(ennf_transformation,[],[f8])).
% 0.36/1.03  
% 0.36/1.03  fof(f18,plain,(
% 0.36/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r2_waybel_7(X0,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.36/1.03    inference(flattening,[],[f17])).
% 0.36/1.03  
% 0.36/1.03  fof(f29,plain,(
% 0.36/1.03    ( ! [X2,X0,X1] : (? [X3] : (! [X4] : (~r2_waybel_7(X0,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => (! [X4] : (~r2_waybel_7(X0,sK5,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X1,sK5) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(sK5,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(sK5,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(sK5))) )),
% 0.36/1.03    introduced(choice_axiom,[])).
% 0.36/1.03  
% 0.36/1.03  fof(f28,plain,(
% 0.36/1.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (! [X4] : (~r2_waybel_7(X0,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) => (? [X3] : (! [X4] : (~r2_waybel_7(X0,X3,X4) | ~r2_hidden(X4,sK4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,sK4) & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))) )),
% 0.36/1.03    introduced(choice_axiom,[])).
% 0.36/1.03  
% 0.36/1.03  fof(f27,plain,(
% 0.36/1.03    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r2_waybel_7(X0,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) => (? [X2] : (? [X3] : (! [X4] : (~r2_waybel_7(X0,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK3,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),sK3,X2) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))) )),
% 0.36/1.03    introduced(choice_axiom,[])).
% 0.36/1.03  
% 0.36/1.03  fof(f26,plain,(
% 0.36/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r2_waybel_7(X0,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (! [X4] : (~r2_waybel_7(sK2,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(sK2))) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2))))) & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(sK2))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(sK2))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(sK2))) & ~v1_xboole_0(X3)) & r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X1,X2) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.36/1.03    introduced(choice_axiom,[])).
% 0.36/1.03  
% 0.36/1.03  fof(f30,plain,(
% 0.36/1.03    (((! [X4] : (~r2_waybel_7(sK2,sK5,X4) | ~r2_hidden(X4,sK4) | ~m1_subset_1(X4,u1_struct_0(sK2))) & r2_hidden(sK3,sK5) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2))))) & v3_waybel_7(sK5,k3_yellow_1(u1_struct_0(sK2))) & v13_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2))) & v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK5)) & r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),sK3,sK4) & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.36/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f29,f28,f27,f26])).
% 0.36/1.03  
% 0.36/1.03  fof(f52,plain,(
% 0.36/1.03    r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),sK3,sK4)),
% 0.36/1.03    inference(cnf_transformation,[],[f30])).
% 0.36/1.03  
% 0.36/1.03  fof(f6,axiom,(
% 0.36/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) => (r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) & v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) & ~v1_xboole_0(X3)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r1_waybel_7(X0,X3,X4) & r2_hidden(X4,X2))) & r2_hidden(X1,X3)))))))),
% 0.36/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.03  
% 0.36/1.03  fof(f15,plain,(
% 0.36/1.03    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((? [X4] : ((r1_waybel_7(X0,X3,X4) & r2_hidden(X4,X2)) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X1,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | v1_xboole_0(X3))) | ~r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.36/1.03    inference(ennf_transformation,[],[f6])).
% 0.36/1.03  
% 0.36/1.03  fof(f16,plain,(
% 0.36/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (? [X4] : (r1_waybel_7(X0,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | v1_xboole_0(X3)) | ~r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.36/1.03    inference(flattening,[],[f15])).
% 0.36/1.03  
% 0.36/1.03  fof(f24,plain,(
% 0.36/1.03    ! [X3,X2,X0] : (? [X4] : (r1_waybel_7(X0,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X0))) => (r1_waybel_7(X0,X3,sK1(X0,X2,X3)) & r2_hidden(sK1(X0,X2,X3),X2) & m1_subset_1(sK1(X0,X2,X3),u1_struct_0(X0))))),
% 0.36/1.03    introduced(choice_axiom,[])).
% 0.36/1.03  
% 0.36/1.03  fof(f25,plain,(
% 0.36/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_waybel_7(X0,X3,sK1(X0,X2,X3)) & r2_hidden(sK1(X0,X2,X3),X2) & m1_subset_1(sK1(X0,X2,X3),u1_struct_0(X0))) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | v1_xboole_0(X3)) | ~r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.36/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f24])).
% 0.36/1.03  
% 0.36/1.03  fof(f45,plain,(
% 0.36/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(sK1(X0,X2,X3),X2) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | v1_xboole_0(X3) | ~r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.03    inference(cnf_transformation,[],[f25])).
% 0.36/1.03  
% 0.36/1.03  fof(f55,plain,(
% 0.36/1.03    v13_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))),
% 0.36/1.03    inference(cnf_transformation,[],[f30])).
% 0.36/1.03  
% 0.36/1.03  fof(f47,plain,(
% 0.36/1.03    ~v2_struct_0(sK2)),
% 0.36/1.03    inference(cnf_transformation,[],[f30])).
% 0.36/1.03  
% 0.36/1.03  fof(f48,plain,(
% 0.36/1.03    v2_pre_topc(sK2)),
% 0.36/1.03    inference(cnf_transformation,[],[f30])).
% 0.36/1.03  
% 0.36/1.03  fof(f49,plain,(
% 0.36/1.03    l1_pre_topc(sK2)),
% 0.36/1.03    inference(cnf_transformation,[],[f30])).
% 0.36/1.03  
% 0.36/1.03  fof(f53,plain,(
% 0.36/1.03    ~v1_xboole_0(sK5)),
% 0.36/1.03    inference(cnf_transformation,[],[f30])).
% 0.36/1.03  
% 0.36/1.03  fof(f54,plain,(
% 0.36/1.03    v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))),
% 0.36/1.03    inference(cnf_transformation,[],[f30])).
% 0.36/1.03  
% 0.36/1.03  fof(f57,plain,(
% 0.36/1.03    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2)))))),
% 0.36/1.03    inference(cnf_transformation,[],[f30])).
% 0.36/1.03  
% 0.36/1.03  fof(f56,plain,(
% 0.36/1.03    v3_waybel_7(sK5,k3_yellow_1(u1_struct_0(sK2)))),
% 0.36/1.03    inference(cnf_transformation,[],[f30])).
% 0.36/1.03  
% 0.36/1.03  fof(f2,axiom,(
% 0.36/1.03    ! [X0] : (l1_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)))),
% 0.36/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.03  
% 0.36/1.03  fof(f9,plain,(
% 0.36/1.03    ! [X0] : l1_orders_2(k3_yellow_1(X0))),
% 0.36/1.03    inference(pure_predicate_removal,[],[f2])).
% 0.36/1.03  
% 0.36/1.03  fof(f33,plain,(
% 0.36/1.03    ( ! [X0] : (l1_orders_2(k3_yellow_1(X0))) )),
% 0.36/1.03    inference(cnf_transformation,[],[f9])).
% 0.36/1.03  
% 0.36/1.03  fof(f4,axiom,(
% 0.36/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_waybel_7(X1,X0) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)))))),
% 0.36/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.03  
% 0.36/1.03  fof(f11,plain,(
% 0.36/1.03    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | (~v3_waybel_7(X1,X0) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.36/1.03    inference(ennf_transformation,[],[f4])).
% 0.36/1.03  
% 0.36/1.03  fof(f12,plain,(
% 0.36/1.03    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | ~v3_waybel_7(X1,X0) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.36/1.03    inference(flattening,[],[f11])).
% 0.36/1.03  
% 0.36/1.03  fof(f39,plain,(
% 0.36/1.03    ( ! [X0,X1] : (v1_subset_1(X1,u1_struct_0(X0)) | ~v3_waybel_7(X1,X0) | ~v13_waybel_0(X1,X0) | ~v2_waybel_0(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.36/1.03    inference(cnf_transformation,[],[f12])).
% 0.36/1.03  
% 0.36/1.03  fof(f3,axiom,(
% 0.36/1.03    ! [X0] : (v5_orders_2(k3_yellow_1(X0)) & v4_orders_2(k3_yellow_1(X0)) & v3_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)) & ~v2_struct_0(k3_yellow_1(X0)))),
% 0.36/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.03  
% 0.36/1.03  fof(f10,plain,(
% 0.36/1.03    ! [X0] : (v5_orders_2(k3_yellow_1(X0)) & v4_orders_2(k3_yellow_1(X0)) & v3_orders_2(k3_yellow_1(X0)) & ~v2_struct_0(k3_yellow_1(X0)))),
% 0.36/1.03    inference(pure_predicate_removal,[],[f3])).
% 0.36/1.03  
% 0.36/1.03  fof(f37,plain,(
% 0.36/1.03    ( ! [X0] : (v5_orders_2(k3_yellow_1(X0))) )),
% 0.36/1.03    inference(cnf_transformation,[],[f10])).
% 0.36/1.03  
% 0.36/1.03  fof(f36,plain,(
% 0.36/1.03    ( ! [X0] : (v4_orders_2(k3_yellow_1(X0))) )),
% 0.36/1.03    inference(cnf_transformation,[],[f10])).
% 0.36/1.03  
% 0.36/1.03  fof(f35,plain,(
% 0.36/1.03    ( ! [X0] : (v3_orders_2(k3_yellow_1(X0))) )),
% 0.36/1.03    inference(cnf_transformation,[],[f10])).
% 0.36/1.03  
% 0.36/1.03  fof(f34,plain,(
% 0.36/1.03    ( ! [X0] : (~v2_struct_0(k3_yellow_1(X0))) )),
% 0.36/1.03    inference(cnf_transformation,[],[f10])).
% 0.36/1.03  
% 0.36/1.03  fof(f44,plain,(
% 0.36/1.03    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK1(X0,X2,X3),u1_struct_0(X0)) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | v1_xboole_0(X3) | ~r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.03    inference(cnf_transformation,[],[f25])).
% 0.36/1.03  
% 0.36/1.03  fof(f46,plain,(
% 0.36/1.03    ( ! [X2,X0,X3,X1] : (r1_waybel_7(X0,X3,sK1(X0,X2,X3)) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0))) | ~v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0)))) | v1_xboole_0(X3) | ~r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.03    inference(cnf_transformation,[],[f25])).
% 0.36/1.03  
% 0.36/1.03  fof(f5,axiom,(
% 0.36/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) & v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0))) & v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ! [X2] : (r1_waybel_7(X0,X1,X2) <=> r2_waybel_7(X0,X1,X2))))),
% 0.36/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.03  
% 0.36/1.03  fof(f13,plain,(
% 0.36/1.03    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_7(X0,X1,X2) <=> r2_waybel_7(X0,X1,X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.36/1.03    inference(ennf_transformation,[],[f5])).
% 0.36/1.03  
% 0.36/1.03  fof(f14,plain,(
% 0.36/1.03    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_7(X0,X1,X2) <=> r2_waybel_7(X0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.36/1.03    inference(flattening,[],[f13])).
% 0.36/1.03  
% 0.36/1.03  fof(f23,plain,(
% 0.36/1.03    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_7(X0,X1,X2) | ~r2_waybel_7(X0,X1,X2)) & (r2_waybel_7(X0,X1,X2) | ~r1_waybel_7(X0,X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.36/1.03    inference(nnf_transformation,[],[f14])).
% 0.36/1.03  
% 0.36/1.03  fof(f42,plain,(
% 0.36/1.03    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | ~r1_waybel_7(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0))))) | ~v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.36/1.03    inference(cnf_transformation,[],[f23])).
% 0.36/1.03  
% 0.36/1.03  fof(f59,plain,(
% 0.36/1.03    ( ! [X4] : (~r2_waybel_7(sK2,sK5,X4) | ~r2_hidden(X4,sK4) | ~m1_subset_1(X4,u1_struct_0(sK2))) )),
% 0.36/1.03    inference(cnf_transformation,[],[f30])).
% 0.36/1.03  
% 0.36/1.03  fof(f58,plain,(
% 0.36/1.03    r2_hidden(sK3,sK5)),
% 0.36/1.03    inference(cnf_transformation,[],[f30])).
% 0.36/1.03  
% 0.36/1.03  fof(f51,plain,(
% 0.36/1.03    m1_subset_1(sK4,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))),
% 0.36/1.03    inference(cnf_transformation,[],[f30])).
% 0.36/1.03  
% 0.36/1.03  fof(f50,plain,(
% 0.36/1.03    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))),
% 0.36/1.03    inference(cnf_transformation,[],[f30])).
% 0.36/1.03  
% 0.36/1.03  cnf(c_23,negated_conjecture,
% 0.36/1.03      ( r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),sK3,sK4) ),
% 0.36/1.03      inference(cnf_transformation,[],[f52]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_14,plain,
% 0.36/1.03      ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
% 0.36/1.03      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
% 0.36/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
% 0.36/1.03      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
% 0.36/1.03      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
% 0.36/1.03      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
% 0.36/1.03      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
% 0.36/1.03      | ~ r2_hidden(X1,X3)
% 0.36/1.03      | r2_hidden(sK1(X0,X2,X3),X2)
% 0.36/1.03      | ~ v2_pre_topc(X0)
% 0.36/1.03      | ~ l1_pre_topc(X0)
% 0.36/1.03      | v2_struct_0(X0)
% 0.36/1.03      | v1_xboole_0(X3) ),
% 0.36/1.03      inference(cnf_transformation,[],[f45]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_20,negated_conjecture,
% 0.36/1.03      ( v13_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2))) ),
% 0.36/1.03      inference(cnf_transformation,[],[f55]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_450,plain,
% 0.36/1.03      ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
% 0.36/1.03      | ~ v1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK2))))
% 0.36/1.03      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2)))))
% 0.36/1.03      | ~ v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
% 0.36/1.03      | ~ r2_hidden(X0,sK5)
% 0.36/1.03      | r2_hidden(sK1(sK2,X1,sK5),X1)
% 0.36/1.03      | ~ v2_pre_topc(sK2)
% 0.36/1.03      | ~ l1_pre_topc(sK2)
% 0.36/1.03      | v2_struct_0(sK2)
% 0.36/1.03      | v1_xboole_0(sK5) ),
% 0.36/1.03      inference(resolution,[status(thm)],[c_14,c_20]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_28,negated_conjecture,
% 0.36/1.03      ( ~ v2_struct_0(sK2) ),
% 0.36/1.03      inference(cnf_transformation,[],[f47]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_27,negated_conjecture,
% 0.36/1.03      ( v2_pre_topc(sK2) ),
% 0.36/1.03      inference(cnf_transformation,[],[f48]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_26,negated_conjecture,
% 0.36/1.03      ( l1_pre_topc(sK2) ),
% 0.36/1.03      inference(cnf_transformation,[],[f49]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_22,negated_conjecture,
% 0.36/1.03      ( ~ v1_xboole_0(sK5) ),
% 0.36/1.03      inference(cnf_transformation,[],[f53]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_21,negated_conjecture,
% 0.36/1.03      ( v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2))) ),
% 0.36/1.03      inference(cnf_transformation,[],[f54]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_18,negated_conjecture,
% 0.36/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2))))) ),
% 0.36/1.03      inference(cnf_transformation,[],[f57]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_19,negated_conjecture,
% 0.36/1.03      ( v3_waybel_7(sK5,k3_yellow_1(u1_struct_0(sK2))) ),
% 0.36/1.03      inference(cnf_transformation,[],[f56]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_2,plain,
% 0.36/1.03      ( l1_orders_2(k3_yellow_1(X0)) ),
% 0.36/1.03      inference(cnf_transformation,[],[f33]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_9,plain,
% 0.36/1.03      ( v1_subset_1(X0,u1_struct_0(X1))
% 0.36/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.36/1.03      | ~ v2_waybel_0(X0,X1)
% 0.36/1.03      | ~ v3_waybel_7(X0,X1)
% 0.36/1.03      | ~ v13_waybel_0(X0,X1)
% 0.36/1.03      | v2_struct_0(X1)
% 0.36/1.03      | ~ v3_orders_2(X1)
% 0.36/1.03      | ~ v4_orders_2(X1)
% 0.36/1.03      | ~ v5_orders_2(X1)
% 0.36/1.03      | ~ l1_orders_2(X1)
% 0.36/1.03      | v1_xboole_0(X0) ),
% 0.36/1.03      inference(cnf_transformation,[],[f39]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_276,plain,
% 0.36/1.03      ( v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
% 0.36/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
% 0.36/1.03      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
% 0.36/1.03      | ~ v3_waybel_7(X0,k3_yellow_1(X1))
% 0.36/1.03      | ~ v13_waybel_0(X0,k3_yellow_1(X1))
% 0.36/1.03      | v2_struct_0(k3_yellow_1(X1))
% 0.36/1.03      | ~ v3_orders_2(k3_yellow_1(X1))
% 0.36/1.03      | ~ v4_orders_2(k3_yellow_1(X1))
% 0.36/1.03      | ~ v5_orders_2(k3_yellow_1(X1))
% 0.36/1.03      | v1_xboole_0(X0) ),
% 0.36/1.03      inference(resolution,[status(thm)],[c_2,c_9]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_3,plain,
% 0.36/1.03      ( v5_orders_2(k3_yellow_1(X0)) ),
% 0.36/1.03      inference(cnf_transformation,[],[f37]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_4,plain,
% 0.36/1.03      ( v4_orders_2(k3_yellow_1(X0)) ),
% 0.36/1.03      inference(cnf_transformation,[],[f36]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_5,plain,
% 0.36/1.03      ( v3_orders_2(k3_yellow_1(X0)) ),
% 0.36/1.03      inference(cnf_transformation,[],[f35]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_6,plain,
% 0.36/1.03      ( ~ v2_struct_0(k3_yellow_1(X0)) ),
% 0.36/1.03      inference(cnf_transformation,[],[f34]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_300,plain,
% 0.36/1.03      ( v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
% 0.36/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
% 0.36/1.03      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
% 0.36/1.03      | ~ v3_waybel_7(X0,k3_yellow_1(X1))
% 0.36/1.03      | ~ v13_waybel_0(X0,k3_yellow_1(X1))
% 0.36/1.03      | v1_xboole_0(X0) ),
% 0.36/1.03      inference(forward_subsumption_resolution,
% 0.36/1.03                [status(thm)],
% 0.36/1.03                [c_276,c_3,c_4,c_5,c_6]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_351,plain,
% 0.36/1.03      ( v1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK2))))
% 0.36/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2)))))
% 0.36/1.03      | ~ v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
% 0.36/1.03      | ~ v13_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
% 0.36/1.03      | v1_xboole_0(sK5) ),
% 0.36/1.03      inference(resolution,[status(thm)],[c_19,c_300]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_454,plain,
% 0.36/1.03      ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
% 0.36/1.03      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ r2_hidden(X0,sK5)
% 0.36/1.03      | r2_hidden(sK1(sK2,X1,sK5),X1) ),
% 0.36/1.03      inference(global_propositional_subsumption,
% 0.36/1.03                [status(thm)],
% 0.36/1.03                [c_450,c_28,c_27,c_26,c_22,c_21,c_20,c_18,c_351]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_524,plain,
% 0.36/1.03      ( ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | r2_hidden(sK1(sK2,sK4,sK5),sK4)
% 0.36/1.03      | ~ r2_hidden(sK3,sK5) ),
% 0.36/1.03      inference(resolution,[status(thm)],[c_23,c_454]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_15,plain,
% 0.36/1.03      ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
% 0.36/1.03      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
% 0.36/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
% 0.36/1.03      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
% 0.36/1.03      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
% 0.36/1.03      | m1_subset_1(sK1(X0,X2,X3),u1_struct_0(X0))
% 0.36/1.03      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
% 0.36/1.03      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
% 0.36/1.03      | ~ r2_hidden(X1,X3)
% 0.36/1.03      | ~ v2_pre_topc(X0)
% 0.36/1.03      | ~ l1_pre_topc(X0)
% 0.36/1.03      | v2_struct_0(X0)
% 0.36/1.03      | v1_xboole_0(X3) ),
% 0.36/1.03      inference(cnf_transformation,[],[f44]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_424,plain,
% 0.36/1.03      ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
% 0.36/1.03      | ~ v1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK2))))
% 0.36/1.03      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | m1_subset_1(sK1(sK2,X1,sK5),u1_struct_0(sK2))
% 0.36/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2)))))
% 0.36/1.03      | ~ v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
% 0.36/1.03      | ~ r2_hidden(X0,sK5)
% 0.36/1.03      | ~ v2_pre_topc(sK2)
% 0.36/1.03      | ~ l1_pre_topc(sK2)
% 0.36/1.03      | v2_struct_0(sK2)
% 0.36/1.03      | v1_xboole_0(sK5) ),
% 0.36/1.03      inference(resolution,[status(thm)],[c_15,c_20]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_428,plain,
% 0.36/1.03      ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
% 0.36/1.03      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | m1_subset_1(sK1(sK2,X1,sK5),u1_struct_0(sK2))
% 0.36/1.03      | ~ r2_hidden(X0,sK5) ),
% 0.36/1.03      inference(global_propositional_subsumption,
% 0.36/1.03                [status(thm)],
% 0.36/1.03                [c_424,c_28,c_27,c_26,c_22,c_21,c_20,c_18,c_351]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_13,plain,
% 0.36/1.03      ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
% 0.36/1.03      | r1_waybel_7(X0,X3,sK1(X0,X2,X3))
% 0.36/1.03      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
% 0.36/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
% 0.36/1.03      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
% 0.36/1.03      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
% 0.36/1.03      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
% 0.36/1.03      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
% 0.36/1.03      | ~ r2_hidden(X1,X3)
% 0.36/1.03      | ~ v2_pre_topc(X0)
% 0.36/1.03      | ~ l1_pre_topc(X0)
% 0.36/1.03      | v2_struct_0(X0)
% 0.36/1.03      | v1_xboole_0(X3) ),
% 0.36/1.03      inference(cnf_transformation,[],[f46]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_12,plain,
% 0.36/1.03      ( r2_waybel_7(X0,X1,X2)
% 0.36/1.03      | ~ r1_waybel_7(X0,X1,X2)
% 0.36/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
% 0.36/1.03      | ~ v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
% 0.36/1.03      | ~ v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
% 0.36/1.03      | ~ v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
% 0.36/1.03      | ~ v2_pre_topc(X0)
% 0.36/1.03      | ~ l1_pre_topc(X0)
% 0.36/1.03      | v2_struct_0(X0)
% 0.36/1.03      | v1_xboole_0(X1) ),
% 0.36/1.03      inference(cnf_transformation,[],[f42]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_317,plain,
% 0.36/1.03      ( r2_waybel_7(sK2,sK5,X0)
% 0.36/1.03      | ~ r1_waybel_7(sK2,sK5,X0)
% 0.36/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2)))))
% 0.36/1.03      | ~ v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
% 0.36/1.03      | ~ v13_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
% 0.36/1.03      | ~ v2_pre_topc(sK2)
% 0.36/1.03      | ~ l1_pre_topc(sK2)
% 0.36/1.03      | v2_struct_0(sK2)
% 0.36/1.03      | v1_xboole_0(sK5) ),
% 0.36/1.03      inference(resolution,[status(thm)],[c_12,c_19]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_321,plain,
% 0.36/1.03      ( ~ r1_waybel_7(sK2,sK5,X0) | r2_waybel_7(sK2,sK5,X0) ),
% 0.36/1.03      inference(global_propositional_subsumption,
% 0.36/1.03                [status(thm)],
% 0.36/1.03                [c_317,c_28,c_27,c_26,c_22,c_21,c_20,c_18]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_322,plain,
% 0.36/1.03      ( r2_waybel_7(sK2,sK5,X0) | ~ r1_waybel_7(sK2,sK5,X0) ),
% 0.36/1.03      inference(renaming,[status(thm)],[c_321]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_16,negated_conjecture,
% 0.36/1.03      ( ~ r2_waybel_7(sK2,sK5,X0)
% 0.36/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 0.36/1.03      | ~ r2_hidden(X0,sK4) ),
% 0.36/1.03      inference(cnf_transformation,[],[f59]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_370,plain,
% 0.36/1.03      ( ~ r1_waybel_7(sK2,sK5,X0)
% 0.36/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 0.36/1.03      | ~ r2_hidden(X0,sK4) ),
% 0.36/1.03      inference(resolution,[status(thm)],[c_322,c_16]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_388,plain,
% 0.36/1.03      ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
% 0.36/1.03      | ~ v1_subset_1(sK5,u1_struct_0(k3_yellow_1(u1_struct_0(sK2))))
% 0.36/1.03      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ m1_subset_1(sK1(sK2,X1,sK5),u1_struct_0(sK2))
% 0.36/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK2)))))
% 0.36/1.03      | ~ v2_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
% 0.36/1.03      | ~ v13_waybel_0(sK5,k3_yellow_1(u1_struct_0(sK2)))
% 0.36/1.03      | ~ r2_hidden(X0,sK5)
% 0.36/1.03      | ~ r2_hidden(sK1(sK2,X1,sK5),sK4)
% 0.36/1.03      | ~ v2_pre_topc(sK2)
% 0.36/1.03      | ~ l1_pre_topc(sK2)
% 0.36/1.03      | v2_struct_0(sK2)
% 0.36/1.03      | v1_xboole_0(sK5) ),
% 0.36/1.03      inference(resolution,[status(thm)],[c_13,c_370]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_392,plain,
% 0.36/1.03      ( ~ m1_subset_1(sK1(sK2,X1,sK5),u1_struct_0(sK2))
% 0.36/1.03      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
% 0.36/1.03      | ~ r2_hidden(X0,sK5)
% 0.36/1.03      | ~ r2_hidden(sK1(sK2,X1,sK5),sK4) ),
% 0.36/1.03      inference(global_propositional_subsumption,
% 0.36/1.03                [status(thm)],
% 0.36/1.03                [c_388,c_28,c_27,c_26,c_22,c_21,c_20,c_18,c_351]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_393,plain,
% 0.36/1.03      ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
% 0.36/1.03      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ m1_subset_1(sK1(sK2,X1,sK5),u1_struct_0(sK2))
% 0.36/1.03      | ~ r2_hidden(X0,sK5)
% 0.36/1.03      | ~ r2_hidden(sK1(sK2,X1,sK5),sK4) ),
% 0.36/1.03      inference(renaming,[status(thm)],[c_392]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_480,plain,
% 0.36/1.03      ( ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(sK2)),X0,X1)
% 0.36/1.03      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ r2_hidden(X0,sK5)
% 0.36/1.03      | ~ r2_hidden(sK1(sK2,X1,sK5),sK4) ),
% 0.36/1.03      inference(backward_subsumption_resolution,
% 0.36/1.03                [status(thm)],
% 0.36/1.03                [c_428,c_393]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_514,plain,
% 0.36/1.03      ( ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2))))
% 0.36/1.03      | ~ r2_hidden(sK1(sK2,sK4,sK5),sK4)
% 0.36/1.03      | ~ r2_hidden(sK3,sK5) ),
% 0.36/1.03      inference(resolution,[status(thm)],[c_23,c_480]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_17,negated_conjecture,
% 0.36/1.03      ( r2_hidden(sK3,sK5) ),
% 0.36/1.03      inference(cnf_transformation,[],[f58]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_24,negated_conjecture,
% 0.36/1.03      ( m1_subset_1(sK4,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))) ),
% 0.36/1.03      inference(cnf_transformation,[],[f51]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(c_25,negated_conjecture,
% 0.36/1.03      ( m1_subset_1(sK3,u1_struct_0(k2_yellow_1(u1_pre_topc(sK2)))) ),
% 0.36/1.03      inference(cnf_transformation,[],[f50]) ).
% 0.36/1.03  
% 0.36/1.03  cnf(contradiction,plain,
% 0.36/1.03      ( $false ),
% 0.36/1.03      inference(minisat,[status(thm)],[c_524,c_514,c_17,c_24,c_25]) ).
% 0.36/1.03  
% 0.36/1.03  
% 0.36/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.36/1.03  
% 0.36/1.03  ------                               Statistics
% 0.36/1.03  
% 0.36/1.03  ------ General
% 0.36/1.03  
% 0.36/1.03  abstr_ref_over_cycles:                  0
% 0.36/1.03  abstr_ref_under_cycles:                 0
% 0.36/1.03  gc_basic_clause_elim:                   0
% 0.36/1.03  forced_gc_time:                         0
% 0.36/1.03  parsing_time:                           0.009
% 0.36/1.03  unif_index_cands_time:                  0.
% 0.36/1.03  unif_index_add_time:                    0.
% 0.36/1.03  orderings_time:                         0.
% 0.36/1.03  out_proof_time:                         0.011
% 0.36/1.03  total_time:                             0.041
% 0.36/1.03  num_of_symbols:                         56
% 0.36/1.03  num_of_terms:                           575
% 0.36/1.03  
% 0.36/1.03  ------ Preprocessing
% 0.36/1.03  
% 0.36/1.03  num_of_splits:                          0
% 0.36/1.03  num_of_split_atoms:                     0
% 0.36/1.03  num_of_reused_defs:                     0
% 0.36/1.03  num_eq_ax_congr_red:                    0
% 0.36/1.03  num_of_sem_filtered_clauses:            0
% 0.36/1.03  num_of_subtypes:                        0
% 0.36/1.03  monotx_restored_types:                  0
% 0.36/1.03  sat_num_of_epr_types:                   0
% 0.36/1.03  sat_num_of_non_cyclic_types:            0
% 0.36/1.03  sat_guarded_non_collapsed_types:        0
% 0.36/1.03  num_pure_diseq_elim:                    0
% 0.36/1.03  simp_replaced_by:                       0
% 0.36/1.03  res_preprocessed:                       26
% 0.36/1.03  prep_upred:                             0
% 0.36/1.03  prep_unflattend:                        0
% 0.36/1.03  smt_new_axioms:                         0
% 0.36/1.03  pred_elim_cands:                        17
% 0.36/1.03  pred_elim:                              14
% 0.36/1.03  pred_elim_cl:                           0
% 0.36/1.03  pred_elim_cycles:                       14
% 0.36/1.03  merged_defs:                            0
% 0.36/1.03  merged_defs_ncl:                        0
% 0.36/1.03  bin_hyper_res:                          0
% 0.36/1.03  prep_cycles:                            1
% 0.36/1.03  pred_elim_time:                         0.
% 0.36/1.03  splitting_time:                         0.
% 0.36/1.03  sem_filter_time:                        0.
% 0.36/1.03  monotx_time:                            0.
% 0.36/1.03  subtype_inf_time:                       0.
% 0.36/1.03  
% 0.36/1.03  ------ Problem properties
% 0.36/1.03  
% 0.36/1.03  clauses:                                0
% 0.36/1.03  conjectures:                            0
% 0.36/1.03  epr:                                    0
% 0.36/1.03  horn:                                   0
% 0.36/1.03  ground:                                 0
% 0.36/1.03  unary:                                  0
% 0.36/1.03  binary:                                 0
% 0.36/1.03  lits:                                   0
% 0.36/1.03  lits_eq:                                0
% 0.36/1.03  fd_pure:                                0
% 0.36/1.03  fd_pseudo:                              0
% 0.36/1.03  fd_cond:                                0
% 0.36/1.03  fd_pseudo_cond:                         0
% 0.36/1.03  ac_symbols:                             undef
% 0.36/1.03  
% 0.36/1.03  ------ Propositional Solver
% 0.36/1.03  
% 0.36/1.03  prop_solver_calls:                      6
% 0.36/1.03  prop_fast_solver_calls:                 291
% 0.36/1.03  smt_solver_calls:                       0
% 0.36/1.03  smt_fast_solver_calls:                  0
% 0.36/1.03  prop_num_of_clauses:                    150
% 0.36/1.03  prop_preprocess_simplified:             698
% 0.36/1.03  prop_fo_subsumed:                       43
% 0.36/1.03  prop_solver_time:                       0.
% 0.36/1.03  smt_solver_time:                        0.
% 0.36/1.03  smt_fast_solver_time:                   0.
% 0.36/1.03  prop_fast_solver_time:                  0.
% 0.36/1.03  prop_unsat_core_time:                   0.
% 0.36/1.03  
% 0.36/1.03  ------ QBF
% 0.36/1.03  
% 0.36/1.03  qbf_q_res:                              0
% 0.36/1.03  qbf_num_tautologies:                    0
% 0.36/1.03  qbf_prep_cycles:                        0
% 0.36/1.03  
% 0.36/1.03  ------ BMC1
% 0.36/1.03  
% 0.36/1.03  bmc1_current_bound:                     -1
% 0.36/1.03  bmc1_last_solved_bound:                 -1
% 0.36/1.03  bmc1_unsat_core_size:                   -1
% 0.36/1.03  bmc1_unsat_core_parents_size:           -1
% 0.36/1.03  bmc1_merge_next_fun:                    0
% 0.36/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.36/1.03  
% 0.36/1.03  ------ Instantiation
% 0.36/1.03  
% 0.36/1.03  inst_num_of_clauses:                    undef
% 0.36/1.03  inst_num_in_passive:                    undef
% 0.36/1.03  inst_num_in_active:                     0
% 0.36/1.03  inst_num_in_unprocessed:                0
% 0.36/1.03  inst_num_of_loops:                      0
% 0.36/1.03  inst_num_of_learning_restarts:          0
% 0.36/1.03  inst_num_moves_active_passive:          0
% 0.36/1.03  inst_lit_activity:                      0
% 0.36/1.03  inst_lit_activity_moves:                0
% 0.36/1.03  inst_num_tautologies:                   0
% 0.36/1.03  inst_num_prop_implied:                  0
% 0.36/1.03  inst_num_existing_simplified:           0
% 0.36/1.03  inst_num_eq_res_simplified:             0
% 0.36/1.03  inst_num_child_elim:                    0
% 0.36/1.03  inst_num_of_dismatching_blockings:      0
% 0.36/1.03  inst_num_of_non_proper_insts:           0
% 0.36/1.03  inst_num_of_duplicates:                 0
% 0.36/1.03  inst_inst_num_from_inst_to_res:         0
% 0.36/1.03  inst_dismatching_checking_time:         0.
% 0.36/1.03  
% 0.36/1.03  ------ Resolution
% 0.36/1.03  
% 0.36/1.03  res_num_of_clauses:                     26
% 0.36/1.03  res_num_in_passive:                     0
% 0.36/1.03  res_num_in_active:                      0
% 0.36/1.03  res_num_of_loops:                       27
% 0.36/1.03  res_forward_subset_subsumed:            0
% 0.36/1.03  res_backward_subset_subsumed:           0
% 0.36/1.03  res_forward_subsumed:                   0
% 0.36/1.03  res_backward_subsumed:                  0
% 0.36/1.03  res_forward_subsumption_resolution:     4
% 0.36/1.03  res_backward_subsumption_resolution:    1
% 0.36/1.03  res_clause_to_clause_subsumption:       6
% 0.36/1.03  res_orphan_elimination:                 0
% 0.36/1.03  res_tautology_del:                      4
% 0.36/1.03  res_num_eq_res_simplified:              0
% 0.36/1.03  res_num_sel_changes:                    0
% 0.36/1.03  res_moves_from_active_to_pass:          0
% 0.36/1.03  
% 0.36/1.03  ------ Superposition
% 0.36/1.03  
% 0.36/1.03  sup_time_total:                         0.
% 0.36/1.03  sup_time_generating:                    0.
% 0.36/1.03  sup_time_sim_full:                      0.
% 0.36/1.03  sup_time_sim_immed:                     0.
% 0.36/1.03  
% 0.36/1.03  sup_num_of_clauses:                     undef
% 0.36/1.03  sup_num_in_active:                      undef
% 0.36/1.03  sup_num_in_passive:                     undef
% 0.36/1.03  sup_num_of_loops:                       0
% 0.36/1.03  sup_fw_superposition:                   0
% 0.36/1.03  sup_bw_superposition:                   0
% 0.36/1.03  sup_immediate_simplified:               0
% 0.36/1.03  sup_given_eliminated:                   0
% 0.36/1.03  comparisons_done:                       0
% 0.36/1.03  comparisons_avoided:                    0
% 0.36/1.03  
% 0.36/1.03  ------ Simplifications
% 0.36/1.03  
% 0.36/1.03  
% 0.36/1.03  sim_fw_subset_subsumed:                 0
% 0.36/1.03  sim_bw_subset_subsumed:                 0
% 0.36/1.03  sim_fw_subsumed:                        0
% 0.36/1.03  sim_bw_subsumed:                        0
% 0.36/1.03  sim_fw_subsumption_res:                 0
% 0.36/1.03  sim_bw_subsumption_res:                 0
% 0.36/1.03  sim_tautology_del:                      0
% 0.36/1.03  sim_eq_tautology_del:                   0
% 0.36/1.03  sim_eq_res_simp:                        0
% 0.36/1.03  sim_fw_demodulated:                     0
% 0.36/1.03  sim_bw_demodulated:                     0
% 0.36/1.03  sim_light_normalised:                   0
% 0.36/1.03  sim_joinable_taut:                      0
% 0.36/1.03  sim_joinable_simp:                      0
% 0.36/1.03  sim_ac_normalised:                      0
% 0.36/1.03  sim_smt_subsumption:                    0
% 0.36/1.03  
%------------------------------------------------------------------------------
