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
% DateTime   : Thu Dec  3 12:18:38 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 290 expanded)
%              Number of clauses        :   52 (  68 expanded)
%              Number of leaves         :   17 (  76 expanded)
%              Depth                    :   19
%              Number of atoms          :  499 (2825 expanded)
%              Number of equality atoms :   54 ( 231 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ v3_pre_topc(X3,X0) )
                & ( ( r2_hidden(X1,X3)
                    & v4_pre_topc(X3,X0)
                    & v3_pre_topc(X3,X0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k1_xboole_0 = sK6
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK6)
                | ~ r2_hidden(X1,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ v3_pre_topc(X3,X0) )
              & ( ( r2_hidden(X1,X3)
                  & v4_pre_topc(X3,X0)
                  & v3_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK6) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(sK5,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0) )
                  & ( ( r2_hidden(sK5,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK4)
                      | ~ v3_pre_topc(X3,sK4) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK4)
                        & v3_pre_topc(X3,sK4) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( k1_xboole_0 = sK6
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK6)
            | ~ r2_hidden(sK5,X3)
            | ~ v4_pre_topc(X3,sK4)
            | ~ v3_pre_topc(X3,sK4) )
          & ( ( r2_hidden(sK5,X3)
              & v4_pre_topc(X3,sK4)
              & v3_pre_topc(X3,sK4) )
            | ~ r2_hidden(X3,sK6) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
    & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f43,f46,f45,f44])).

fof(f74,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f69,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK6)
      | ~ r2_hidden(sK5,X3)
      | ~ v4_pre_topc(X3,sK4)
      | ~ v3_pre_topc(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    k1_xboole_0 = sK6 ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f29,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f19,f29])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
            & r1_tarski(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f59,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1436,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_352,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_353,plain,
    ( ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(k2_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_51,plain,
    ( v2_struct_0(sK4)
    | ~ l1_struct_0(sK4)
    | ~ v1_xboole_0(k2_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_20,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_57,plain,
    ( l1_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_355,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_353,c_32,c_30,c_51,c_57])).

cnf(c_365,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | k2_struct_0(sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_355])).

cnf(c_366,plain,
    ( r2_hidden(X0,k2_struct_0(sK4))
    | ~ m1_subset_1(X0,k2_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_1435,plain,
    ( r2_hidden(X0,k2_struct_0(sK4)) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_17,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_380,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_20,c_17])).

cnf(c_569,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_380,c_30])).

cnf(c_570,plain,
    ( k2_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_1482,plain,
    ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1435,c_570])).

cnf(c_1900,plain,
    ( r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1436,c_1482])).

cnf(c_18,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_21,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_24,negated_conjecture,
    ( ~ v4_pre_topc(X0,sK4)
    | ~ v3_pre_topc(X0,sK4)
    | r2_hidden(X0,sK6)
    | ~ r2_hidden(sK5,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_395,plain,
    ( ~ v3_pre_topc(X0,sK4)
    | r2_hidden(X0,sK6)
    | ~ r2_hidden(sK5,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_struct_0(X1) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_24])).

cnf(c_396,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK4),sK4)
    | r2_hidden(k2_struct_0(sK4),sK6)
    | ~ r2_hidden(sK5,k2_struct_0(sK4))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_398,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK4),sK4)
    | r2_hidden(k2_struct_0(sK4),sK6)
    | ~ r2_hidden(sK5,k2_struct_0(sK4))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_31,c_30])).

cnf(c_538,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k2_struct_0(sK4),sK6)
    | ~ r2_hidden(sK5,k2_struct_0(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(sK4) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_398])).

cnf(c_539,plain,
    ( ~ r2_hidden(k2_struct_0(sK4),u1_pre_topc(sK4))
    | r2_hidden(k2_struct_0(sK4),sK6)
    | ~ r2_hidden(sK5,k2_struct_0(sK4))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_541,plain,
    ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK5,k2_struct_0(sK4))
    | r2_hidden(k2_struct_0(sK4),sK6)
    | ~ r2_hidden(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_30])).

cnf(c_542,plain,
    ( ~ r2_hidden(k2_struct_0(sK4),u1_pre_topc(sK4))
    | r2_hidden(k2_struct_0(sK4),sK6)
    | ~ r2_hidden(sK5,k2_struct_0(sK4))
    | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_541])).

cnf(c_1432,plain,
    ( r2_hidden(k2_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(k2_struct_0(sK4),sK6) = iProver_top
    | r2_hidden(sK5,k2_struct_0(sK4)) != iProver_top
    | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 = sK6 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1497,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(u1_struct_0(sK4),k1_xboole_0) = iProver_top
    | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1432,c_23,c_570])).

cnf(c_2,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1445,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1460,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1445,c_1])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_632,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_633,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_1434,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_16,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_574,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_30])).

cnf(c_575,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_69,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_577,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_575,c_31,c_30,c_69])).

cnf(c_1431,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_1502,plain,
    ( r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1497,c_1460,c_1434,c_1431])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1900,c_1502])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.52/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/0.99  
% 1.52/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.52/0.99  
% 1.52/0.99  ------  iProver source info
% 1.52/0.99  
% 1.52/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.52/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.52/0.99  git: non_committed_changes: false
% 1.52/0.99  git: last_make_outside_of_git: false
% 1.52/0.99  
% 1.52/0.99  ------ 
% 1.52/0.99  
% 1.52/0.99  ------ Input Options
% 1.52/0.99  
% 1.52/0.99  --out_options                           all
% 1.52/0.99  --tptp_safe_out                         true
% 1.52/0.99  --problem_path                          ""
% 1.52/0.99  --include_path                          ""
% 1.52/0.99  --clausifier                            res/vclausify_rel
% 1.52/0.99  --clausifier_options                    --mode clausify
% 1.52/0.99  --stdin                                 false
% 1.52/0.99  --stats_out                             all
% 1.52/0.99  
% 1.52/0.99  ------ General Options
% 1.52/0.99  
% 1.52/0.99  --fof                                   false
% 1.52/0.99  --time_out_real                         305.
% 1.52/0.99  --time_out_virtual                      -1.
% 1.52/0.99  --symbol_type_check                     false
% 1.52/0.99  --clausify_out                          false
% 1.52/0.99  --sig_cnt_out                           false
% 1.52/0.99  --trig_cnt_out                          false
% 1.52/0.99  --trig_cnt_out_tolerance                1.
% 1.52/0.99  --trig_cnt_out_sk_spl                   false
% 1.52/0.99  --abstr_cl_out                          false
% 1.52/0.99  
% 1.52/0.99  ------ Global Options
% 1.52/0.99  
% 1.52/0.99  --schedule                              default
% 1.52/0.99  --add_important_lit                     false
% 1.52/0.99  --prop_solver_per_cl                    1000
% 1.52/0.99  --min_unsat_core                        false
% 1.52/0.99  --soft_assumptions                      false
% 1.52/0.99  --soft_lemma_size                       3
% 1.52/0.99  --prop_impl_unit_size                   0
% 1.52/0.99  --prop_impl_unit                        []
% 1.52/0.99  --share_sel_clauses                     true
% 1.52/0.99  --reset_solvers                         false
% 1.52/0.99  --bc_imp_inh                            [conj_cone]
% 1.52/0.99  --conj_cone_tolerance                   3.
% 1.52/0.99  --extra_neg_conj                        none
% 1.52/0.99  --large_theory_mode                     true
% 1.52/0.99  --prolific_symb_bound                   200
% 1.52/0.99  --lt_threshold                          2000
% 1.52/0.99  --clause_weak_htbl                      true
% 1.52/0.99  --gc_record_bc_elim                     false
% 1.52/0.99  
% 1.52/0.99  ------ Preprocessing Options
% 1.52/0.99  
% 1.52/0.99  --preprocessing_flag                    true
% 1.52/0.99  --time_out_prep_mult                    0.1
% 1.52/0.99  --splitting_mode                        input
% 1.52/0.99  --splitting_grd                         true
% 1.52/0.99  --splitting_cvd                         false
% 1.52/0.99  --splitting_cvd_svl                     false
% 1.52/0.99  --splitting_nvd                         32
% 1.52/0.99  --sub_typing                            true
% 1.52/0.99  --prep_gs_sim                           true
% 1.52/0.99  --prep_unflatten                        true
% 1.52/0.99  --prep_res_sim                          true
% 1.52/0.99  --prep_upred                            true
% 1.52/0.99  --prep_sem_filter                       exhaustive
% 1.52/0.99  --prep_sem_filter_out                   false
% 1.52/0.99  --pred_elim                             true
% 1.52/0.99  --res_sim_input                         true
% 1.52/0.99  --eq_ax_congr_red                       true
% 1.52/0.99  --pure_diseq_elim                       true
% 1.52/0.99  --brand_transform                       false
% 1.52/0.99  --non_eq_to_eq                          false
% 1.52/0.99  --prep_def_merge                        true
% 1.52/0.99  --prep_def_merge_prop_impl              false
% 1.52/0.99  --prep_def_merge_mbd                    true
% 1.52/0.99  --prep_def_merge_tr_red                 false
% 1.52/0.99  --prep_def_merge_tr_cl                  false
% 1.52/0.99  --smt_preprocessing                     true
% 1.52/0.99  --smt_ac_axioms                         fast
% 1.52/0.99  --preprocessed_out                      false
% 1.52/0.99  --preprocessed_stats                    false
% 1.52/0.99  
% 1.52/0.99  ------ Abstraction refinement Options
% 1.52/0.99  
% 1.52/0.99  --abstr_ref                             []
% 1.52/0.99  --abstr_ref_prep                        false
% 1.52/0.99  --abstr_ref_until_sat                   false
% 1.52/0.99  --abstr_ref_sig_restrict                funpre
% 1.52/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.52/0.99  --abstr_ref_under                       []
% 1.52/0.99  
% 1.52/0.99  ------ SAT Options
% 1.52/0.99  
% 1.52/0.99  --sat_mode                              false
% 1.52/0.99  --sat_fm_restart_options                ""
% 1.52/0.99  --sat_gr_def                            false
% 1.52/0.99  --sat_epr_types                         true
% 1.52/0.99  --sat_non_cyclic_types                  false
% 1.52/0.99  --sat_finite_models                     false
% 1.52/0.99  --sat_fm_lemmas                         false
% 1.52/0.99  --sat_fm_prep                           false
% 1.52/0.99  --sat_fm_uc_incr                        true
% 1.52/0.99  --sat_out_model                         small
% 1.52/0.99  --sat_out_clauses                       false
% 1.52/0.99  
% 1.52/0.99  ------ QBF Options
% 1.52/0.99  
% 1.52/0.99  --qbf_mode                              false
% 1.52/0.99  --qbf_elim_univ                         false
% 1.52/0.99  --qbf_dom_inst                          none
% 1.52/0.99  --qbf_dom_pre_inst                      false
% 1.52/0.99  --qbf_sk_in                             false
% 1.52/0.99  --qbf_pred_elim                         true
% 1.52/0.99  --qbf_split                             512
% 1.52/0.99  
% 1.52/0.99  ------ BMC1 Options
% 1.52/0.99  
% 1.52/0.99  --bmc1_incremental                      false
% 1.52/0.99  --bmc1_axioms                           reachable_all
% 1.52/0.99  --bmc1_min_bound                        0
% 1.52/0.99  --bmc1_max_bound                        -1
% 1.52/0.99  --bmc1_max_bound_default                -1
% 1.52/0.99  --bmc1_symbol_reachability              true
% 1.52/0.99  --bmc1_property_lemmas                  false
% 1.52/0.99  --bmc1_k_induction                      false
% 1.52/0.99  --bmc1_non_equiv_states                 false
% 1.52/0.99  --bmc1_deadlock                         false
% 1.52/0.99  --bmc1_ucm                              false
% 1.52/0.99  --bmc1_add_unsat_core                   none
% 1.52/0.99  --bmc1_unsat_core_children              false
% 1.52/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.52/0.99  --bmc1_out_stat                         full
% 1.52/0.99  --bmc1_ground_init                      false
% 1.52/0.99  --bmc1_pre_inst_next_state              false
% 1.52/0.99  --bmc1_pre_inst_state                   false
% 1.52/0.99  --bmc1_pre_inst_reach_state             false
% 1.52/0.99  --bmc1_out_unsat_core                   false
% 1.52/0.99  --bmc1_aig_witness_out                  false
% 1.52/0.99  --bmc1_verbose                          false
% 1.52/0.99  --bmc1_dump_clauses_tptp                false
% 1.52/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.52/0.99  --bmc1_dump_file                        -
% 1.52/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.52/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.52/0.99  --bmc1_ucm_extend_mode                  1
% 1.52/0.99  --bmc1_ucm_init_mode                    2
% 1.52/0.99  --bmc1_ucm_cone_mode                    none
% 1.52/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.52/0.99  --bmc1_ucm_relax_model                  4
% 1.52/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.52/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.52/0.99  --bmc1_ucm_layered_model                none
% 1.52/0.99  --bmc1_ucm_max_lemma_size               10
% 1.52/0.99  
% 1.52/0.99  ------ AIG Options
% 1.52/0.99  
% 1.52/0.99  --aig_mode                              false
% 1.52/0.99  
% 1.52/0.99  ------ Instantiation Options
% 1.52/0.99  
% 1.52/0.99  --instantiation_flag                    true
% 1.52/0.99  --inst_sos_flag                         false
% 1.52/0.99  --inst_sos_phase                        true
% 1.52/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.52/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.52/0.99  --inst_lit_sel_side                     num_symb
% 1.52/0.99  --inst_solver_per_active                1400
% 1.52/0.99  --inst_solver_calls_frac                1.
% 1.52/0.99  --inst_passive_queue_type               priority_queues
% 1.52/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.52/0.99  --inst_passive_queues_freq              [25;2]
% 1.52/0.99  --inst_dismatching                      true
% 1.52/0.99  --inst_eager_unprocessed_to_passive     true
% 1.52/0.99  --inst_prop_sim_given                   true
% 1.52/0.99  --inst_prop_sim_new                     false
% 1.52/0.99  --inst_subs_new                         false
% 1.52/0.99  --inst_eq_res_simp                      false
% 1.52/0.99  --inst_subs_given                       false
% 1.52/0.99  --inst_orphan_elimination               true
% 1.52/0.99  --inst_learning_loop_flag               true
% 1.52/0.99  --inst_learning_start                   3000
% 1.52/0.99  --inst_learning_factor                  2
% 1.52/0.99  --inst_start_prop_sim_after_learn       3
% 1.52/0.99  --inst_sel_renew                        solver
% 1.52/0.99  --inst_lit_activity_flag                true
% 1.52/0.99  --inst_restr_to_given                   false
% 1.52/0.99  --inst_activity_threshold               500
% 1.52/0.99  --inst_out_proof                        true
% 1.52/0.99  
% 1.52/0.99  ------ Resolution Options
% 1.52/0.99  
% 1.52/0.99  --resolution_flag                       true
% 1.52/0.99  --res_lit_sel                           adaptive
% 1.52/0.99  --res_lit_sel_side                      none
% 1.52/0.99  --res_ordering                          kbo
% 1.52/0.99  --res_to_prop_solver                    active
% 1.52/0.99  --res_prop_simpl_new                    false
% 1.52/0.99  --res_prop_simpl_given                  true
% 1.52/0.99  --res_passive_queue_type                priority_queues
% 1.52/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.52/0.99  --res_passive_queues_freq               [15;5]
% 1.52/0.99  --res_forward_subs                      full
% 1.52/0.99  --res_backward_subs                     full
% 1.52/0.99  --res_forward_subs_resolution           true
% 1.52/0.99  --res_backward_subs_resolution          true
% 1.52/0.99  --res_orphan_elimination                true
% 1.52/0.99  --res_time_limit                        2.
% 1.52/0.99  --res_out_proof                         true
% 1.52/0.99  
% 1.52/0.99  ------ Superposition Options
% 1.52/0.99  
% 1.52/0.99  --superposition_flag                    true
% 1.52/0.99  --sup_passive_queue_type                priority_queues
% 1.52/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.52/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.52/0.99  --demod_completeness_check              fast
% 1.52/0.99  --demod_use_ground                      true
% 1.52/0.99  --sup_to_prop_solver                    passive
% 1.52/0.99  --sup_prop_simpl_new                    true
% 1.52/0.99  --sup_prop_simpl_given                  true
% 1.52/0.99  --sup_fun_splitting                     false
% 1.52/0.99  --sup_smt_interval                      50000
% 1.52/0.99  
% 1.52/0.99  ------ Superposition Simplification Setup
% 1.52/0.99  
% 1.52/0.99  --sup_indices_passive                   []
% 1.52/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.99  --sup_full_bw                           [BwDemod]
% 1.52/0.99  --sup_immed_triv                        [TrivRules]
% 1.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.99  --sup_immed_bw_main                     []
% 1.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.99  
% 1.52/0.99  ------ Combination Options
% 1.52/0.99  
% 1.52/0.99  --comb_res_mult                         3
% 1.52/0.99  --comb_sup_mult                         2
% 1.52/0.99  --comb_inst_mult                        10
% 1.52/0.99  
% 1.52/0.99  ------ Debug Options
% 1.52/0.99  
% 1.52/0.99  --dbg_backtrace                         false
% 1.52/0.99  --dbg_dump_prop_clauses                 false
% 1.52/0.99  --dbg_dump_prop_clauses_file            -
% 1.52/0.99  --dbg_out_stat                          false
% 1.52/0.99  ------ Parsing...
% 1.52/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.52/0.99  
% 1.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.52/0.99  
% 1.52/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.52/0.99  
% 1.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.52/0.99  ------ Proving...
% 1.52/0.99  ------ Problem Properties 
% 1.52/0.99  
% 1.52/0.99  
% 1.52/0.99  clauses                                 20
% 1.52/0.99  conjectures                             4
% 1.52/0.99  EPR                                     3
% 1.52/0.99  Horn                                    16
% 1.52/0.99  unary                                   9
% 1.52/0.99  binary                                  7
% 1.52/0.99  lits                                    39
% 1.52/0.99  lits eq                                 3
% 1.52/0.99  fd_pure                                 0
% 1.52/0.99  fd_pseudo                               0
% 1.52/0.99  fd_cond                                 0
% 1.52/0.99  fd_pseudo_cond                          0
% 1.52/0.99  AC symbols                              0
% 1.52/0.99  
% 1.52/0.99  ------ Schedule dynamic 5 is on 
% 1.52/0.99  
% 1.52/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.52/0.99  
% 1.52/0.99  
% 1.52/0.99  ------ 
% 1.52/0.99  Current options:
% 1.52/0.99  ------ 
% 1.52/0.99  
% 1.52/0.99  ------ Input Options
% 1.52/0.99  
% 1.52/0.99  --out_options                           all
% 1.52/0.99  --tptp_safe_out                         true
% 1.52/0.99  --problem_path                          ""
% 1.52/0.99  --include_path                          ""
% 1.52/0.99  --clausifier                            res/vclausify_rel
% 1.52/0.99  --clausifier_options                    --mode clausify
% 1.52/0.99  --stdin                                 false
% 1.52/0.99  --stats_out                             all
% 1.52/1.00  
% 1.52/1.00  ------ General Options
% 1.52/1.00  
% 1.52/1.00  --fof                                   false
% 1.52/1.00  --time_out_real                         305.
% 1.52/1.00  --time_out_virtual                      -1.
% 1.52/1.00  --symbol_type_check                     false
% 1.52/1.00  --clausify_out                          false
% 1.52/1.00  --sig_cnt_out                           false
% 1.52/1.00  --trig_cnt_out                          false
% 1.52/1.00  --trig_cnt_out_tolerance                1.
% 1.52/1.00  --trig_cnt_out_sk_spl                   false
% 1.52/1.00  --abstr_cl_out                          false
% 1.52/1.00  
% 1.52/1.00  ------ Global Options
% 1.52/1.00  
% 1.52/1.00  --schedule                              default
% 1.52/1.00  --add_important_lit                     false
% 1.52/1.00  --prop_solver_per_cl                    1000
% 1.52/1.00  --min_unsat_core                        false
% 1.52/1.00  --soft_assumptions                      false
% 1.52/1.00  --soft_lemma_size                       3
% 1.52/1.00  --prop_impl_unit_size                   0
% 1.52/1.00  --prop_impl_unit                        []
% 1.52/1.00  --share_sel_clauses                     true
% 1.52/1.00  --reset_solvers                         false
% 1.52/1.00  --bc_imp_inh                            [conj_cone]
% 1.52/1.00  --conj_cone_tolerance                   3.
% 1.52/1.00  --extra_neg_conj                        none
% 1.52/1.00  --large_theory_mode                     true
% 1.52/1.00  --prolific_symb_bound                   200
% 1.52/1.00  --lt_threshold                          2000
% 1.52/1.00  --clause_weak_htbl                      true
% 1.52/1.00  --gc_record_bc_elim                     false
% 1.52/1.00  
% 1.52/1.00  ------ Preprocessing Options
% 1.52/1.00  
% 1.52/1.00  --preprocessing_flag                    true
% 1.52/1.00  --time_out_prep_mult                    0.1
% 1.52/1.00  --splitting_mode                        input
% 1.52/1.00  --splitting_grd                         true
% 1.52/1.00  --splitting_cvd                         false
% 1.52/1.00  --splitting_cvd_svl                     false
% 1.52/1.00  --splitting_nvd                         32
% 1.52/1.00  --sub_typing                            true
% 1.52/1.00  --prep_gs_sim                           true
% 1.52/1.00  --prep_unflatten                        true
% 1.52/1.00  --prep_res_sim                          true
% 1.52/1.00  --prep_upred                            true
% 1.52/1.00  --prep_sem_filter                       exhaustive
% 1.52/1.00  --prep_sem_filter_out                   false
% 1.52/1.00  --pred_elim                             true
% 1.52/1.00  --res_sim_input                         true
% 1.52/1.00  --eq_ax_congr_red                       true
% 1.52/1.00  --pure_diseq_elim                       true
% 1.52/1.00  --brand_transform                       false
% 1.52/1.00  --non_eq_to_eq                          false
% 1.52/1.00  --prep_def_merge                        true
% 1.52/1.00  --prep_def_merge_prop_impl              false
% 1.52/1.00  --prep_def_merge_mbd                    true
% 1.52/1.00  --prep_def_merge_tr_red                 false
% 1.52/1.00  --prep_def_merge_tr_cl                  false
% 1.52/1.00  --smt_preprocessing                     true
% 1.52/1.00  --smt_ac_axioms                         fast
% 1.52/1.00  --preprocessed_out                      false
% 1.52/1.00  --preprocessed_stats                    false
% 1.52/1.00  
% 1.52/1.00  ------ Abstraction refinement Options
% 1.52/1.00  
% 1.52/1.00  --abstr_ref                             []
% 1.52/1.00  --abstr_ref_prep                        false
% 1.52/1.00  --abstr_ref_until_sat                   false
% 1.52/1.00  --abstr_ref_sig_restrict                funpre
% 1.52/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.52/1.00  --abstr_ref_under                       []
% 1.52/1.00  
% 1.52/1.00  ------ SAT Options
% 1.52/1.00  
% 1.52/1.00  --sat_mode                              false
% 1.52/1.00  --sat_fm_restart_options                ""
% 1.52/1.00  --sat_gr_def                            false
% 1.52/1.00  --sat_epr_types                         true
% 1.52/1.00  --sat_non_cyclic_types                  false
% 1.52/1.00  --sat_finite_models                     false
% 1.52/1.00  --sat_fm_lemmas                         false
% 1.52/1.00  --sat_fm_prep                           false
% 1.52/1.00  --sat_fm_uc_incr                        true
% 1.52/1.00  --sat_out_model                         small
% 1.52/1.00  --sat_out_clauses                       false
% 1.52/1.00  
% 1.52/1.00  ------ QBF Options
% 1.52/1.00  
% 1.52/1.00  --qbf_mode                              false
% 1.52/1.00  --qbf_elim_univ                         false
% 1.52/1.00  --qbf_dom_inst                          none
% 1.52/1.00  --qbf_dom_pre_inst                      false
% 1.52/1.00  --qbf_sk_in                             false
% 1.52/1.00  --qbf_pred_elim                         true
% 1.52/1.00  --qbf_split                             512
% 1.52/1.00  
% 1.52/1.00  ------ BMC1 Options
% 1.52/1.00  
% 1.52/1.00  --bmc1_incremental                      false
% 1.52/1.00  --bmc1_axioms                           reachable_all
% 1.52/1.00  --bmc1_min_bound                        0
% 1.52/1.00  --bmc1_max_bound                        -1
% 1.52/1.00  --bmc1_max_bound_default                -1
% 1.52/1.00  --bmc1_symbol_reachability              true
% 1.52/1.00  --bmc1_property_lemmas                  false
% 1.52/1.00  --bmc1_k_induction                      false
% 1.52/1.00  --bmc1_non_equiv_states                 false
% 1.52/1.00  --bmc1_deadlock                         false
% 1.52/1.00  --bmc1_ucm                              false
% 1.52/1.00  --bmc1_add_unsat_core                   none
% 1.52/1.00  --bmc1_unsat_core_children              false
% 1.52/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.52/1.00  --bmc1_out_stat                         full
% 1.52/1.00  --bmc1_ground_init                      false
% 1.52/1.00  --bmc1_pre_inst_next_state              false
% 1.52/1.00  --bmc1_pre_inst_state                   false
% 1.52/1.00  --bmc1_pre_inst_reach_state             false
% 1.52/1.00  --bmc1_out_unsat_core                   false
% 1.52/1.00  --bmc1_aig_witness_out                  false
% 1.52/1.00  --bmc1_verbose                          false
% 1.52/1.00  --bmc1_dump_clauses_tptp                false
% 1.52/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.52/1.00  --bmc1_dump_file                        -
% 1.52/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.52/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.52/1.00  --bmc1_ucm_extend_mode                  1
% 1.52/1.00  --bmc1_ucm_init_mode                    2
% 1.52/1.00  --bmc1_ucm_cone_mode                    none
% 1.52/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.52/1.00  --bmc1_ucm_relax_model                  4
% 1.52/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.52/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.52/1.00  --bmc1_ucm_layered_model                none
% 1.52/1.00  --bmc1_ucm_max_lemma_size               10
% 1.52/1.00  
% 1.52/1.00  ------ AIG Options
% 1.52/1.00  
% 1.52/1.00  --aig_mode                              false
% 1.52/1.00  
% 1.52/1.00  ------ Instantiation Options
% 1.52/1.00  
% 1.52/1.00  --instantiation_flag                    true
% 1.52/1.00  --inst_sos_flag                         false
% 1.52/1.00  --inst_sos_phase                        true
% 1.52/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.52/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.52/1.00  --inst_lit_sel_side                     none
% 1.52/1.00  --inst_solver_per_active                1400
% 1.52/1.00  --inst_solver_calls_frac                1.
% 1.52/1.00  --inst_passive_queue_type               priority_queues
% 1.52/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.52/1.00  --inst_passive_queues_freq              [25;2]
% 1.52/1.00  --inst_dismatching                      true
% 1.52/1.00  --inst_eager_unprocessed_to_passive     true
% 1.52/1.00  --inst_prop_sim_given                   true
% 1.52/1.00  --inst_prop_sim_new                     false
% 1.52/1.00  --inst_subs_new                         false
% 1.52/1.00  --inst_eq_res_simp                      false
% 1.52/1.00  --inst_subs_given                       false
% 1.52/1.00  --inst_orphan_elimination               true
% 1.52/1.00  --inst_learning_loop_flag               true
% 1.52/1.00  --inst_learning_start                   3000
% 1.52/1.00  --inst_learning_factor                  2
% 1.52/1.00  --inst_start_prop_sim_after_learn       3
% 1.52/1.00  --inst_sel_renew                        solver
% 1.52/1.00  --inst_lit_activity_flag                true
% 1.52/1.00  --inst_restr_to_given                   false
% 1.52/1.00  --inst_activity_threshold               500
% 1.52/1.00  --inst_out_proof                        true
% 1.52/1.00  
% 1.52/1.00  ------ Resolution Options
% 1.52/1.00  
% 1.52/1.00  --resolution_flag                       false
% 1.52/1.00  --res_lit_sel                           adaptive
% 1.52/1.00  --res_lit_sel_side                      none
% 1.52/1.00  --res_ordering                          kbo
% 1.52/1.00  --res_to_prop_solver                    active
% 1.52/1.00  --res_prop_simpl_new                    false
% 1.52/1.00  --res_prop_simpl_given                  true
% 1.52/1.00  --res_passive_queue_type                priority_queues
% 1.52/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.52/1.00  --res_passive_queues_freq               [15;5]
% 1.52/1.00  --res_forward_subs                      full
% 1.52/1.00  --res_backward_subs                     full
% 1.52/1.00  --res_forward_subs_resolution           true
% 1.52/1.00  --res_backward_subs_resolution          true
% 1.52/1.00  --res_orphan_elimination                true
% 1.52/1.00  --res_time_limit                        2.
% 1.52/1.00  --res_out_proof                         true
% 1.52/1.00  
% 1.52/1.00  ------ Superposition Options
% 1.52/1.00  
% 1.52/1.00  --superposition_flag                    true
% 1.52/1.00  --sup_passive_queue_type                priority_queues
% 1.52/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.52/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.52/1.00  --demod_completeness_check              fast
% 1.52/1.00  --demod_use_ground                      true
% 1.52/1.00  --sup_to_prop_solver                    passive
% 1.52/1.00  --sup_prop_simpl_new                    true
% 1.52/1.00  --sup_prop_simpl_given                  true
% 1.52/1.00  --sup_fun_splitting                     false
% 1.52/1.00  --sup_smt_interval                      50000
% 1.52/1.00  
% 1.52/1.00  ------ Superposition Simplification Setup
% 1.52/1.00  
% 1.52/1.00  --sup_indices_passive                   []
% 1.52/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.52/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/1.00  --sup_full_bw                           [BwDemod]
% 1.52/1.00  --sup_immed_triv                        [TrivRules]
% 1.52/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.52/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/1.00  --sup_immed_bw_main                     []
% 1.52/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.52/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/1.00  
% 1.52/1.00  ------ Combination Options
% 1.52/1.00  
% 1.52/1.00  --comb_res_mult                         3
% 1.52/1.00  --comb_sup_mult                         2
% 1.52/1.00  --comb_inst_mult                        10
% 1.52/1.00  
% 1.52/1.00  ------ Debug Options
% 1.52/1.00  
% 1.52/1.00  --dbg_backtrace                         false
% 1.52/1.00  --dbg_dump_prop_clauses                 false
% 1.52/1.00  --dbg_dump_prop_clauses_file            -
% 1.52/1.00  --dbg_out_stat                          false
% 1.52/1.00  
% 1.52/1.00  
% 1.52/1.00  
% 1.52/1.00  
% 1.52/1.00  ------ Proving...
% 1.52/1.00  
% 1.52/1.00  
% 1.52/1.00  % SZS status Theorem for theBenchmark.p
% 1.52/1.00  
% 1.52/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.52/1.00  
% 1.52/1.00  fof(f12,conjecture,(
% 1.52/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.00  
% 1.52/1.00  fof(f13,negated_conjecture,(
% 1.52/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 1.52/1.00    inference(negated_conjecture,[],[f12])).
% 1.52/1.00  
% 1.52/1.00  fof(f27,plain,(
% 1.52/1.00    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.52/1.00    inference(ennf_transformation,[],[f13])).
% 1.52/1.00  
% 1.52/1.00  fof(f28,plain,(
% 1.52/1.00    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.52/1.00    inference(flattening,[],[f27])).
% 1.52/1.00  
% 1.52/1.00  fof(f42,plain,(
% 1.52/1.00    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.52/1.00    inference(nnf_transformation,[],[f28])).
% 1.52/1.00  
% 1.52/1.00  fof(f43,plain,(
% 1.52/1.00    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.52/1.00    inference(flattening,[],[f42])).
% 1.52/1.00  
% 1.52/1.00  fof(f46,plain,(
% 1.52/1.00    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k1_xboole_0 = sK6 & ! [X3] : (((r2_hidden(X3,sK6) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,sK6))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 1.52/1.00    introduced(choice_axiom,[])).
% 1.52/1.00  
% 1.52/1.00  fof(f45,plain,(
% 1.52/1.00    ( ! [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK5,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(sK5,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 1.52/1.00    introduced(choice_axiom,[])).
% 1.52/1.00  
% 1.52/1.00  fof(f44,plain,(
% 1.52/1.00    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK4) | ~v3_pre_topc(X3,sK4)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK4) & v3_pre_topc(X3,sK4)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 1.52/1.00    introduced(choice_axiom,[])).
% 1.52/1.00  
% 1.52/1.00  fof(f47,plain,(
% 1.52/1.00    ((k1_xboole_0 = sK6 & ! [X3] : (((r2_hidden(X3,sK6) | ~r2_hidden(sK5,X3) | ~v4_pre_topc(X3,sK4) | ~v3_pre_topc(X3,sK4)) & ((r2_hidden(sK5,X3) & v4_pre_topc(X3,sK4) & v3_pre_topc(X3,sK4)) | ~r2_hidden(X3,sK6))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(sK6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 1.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f43,f46,f45,f44])).
% 1.52/1.00  
% 1.52/1.00  fof(f74,plain,(
% 1.52/1.00    m1_subset_1(sK5,u1_struct_0(sK4))),
% 1.52/1.00    inference(cnf_transformation,[],[f47])).
% 1.52/1.00  
% 1.52/1.00  fof(f4,axiom,(
% 1.52/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.00  
% 1.52/1.00  fof(f15,plain,(
% 1.52/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.52/1.00    inference(ennf_transformation,[],[f4])).
% 1.52/1.00  
% 1.52/1.00  fof(f16,plain,(
% 1.52/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.52/1.00    inference(flattening,[],[f15])).
% 1.52/1.00  
% 1.52/1.00  fof(f51,plain,(
% 1.52/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.52/1.00    inference(cnf_transformation,[],[f16])).
% 1.52/1.00  
% 1.52/1.00  fof(f11,axiom,(
% 1.52/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.00  
% 1.52/1.00  fof(f25,plain,(
% 1.52/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.52/1.00    inference(ennf_transformation,[],[f11])).
% 1.52/1.00  
% 1.52/1.00  fof(f26,plain,(
% 1.52/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.52/1.00    inference(flattening,[],[f25])).
% 1.52/1.00  
% 1.52/1.00  fof(f70,plain,(
% 1.52/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.52/1.00    inference(cnf_transformation,[],[f26])).
% 1.52/1.00  
% 1.52/1.00  fof(f71,plain,(
% 1.52/1.00    ~v2_struct_0(sK4)),
% 1.52/1.00    inference(cnf_transformation,[],[f47])).
% 1.52/1.00  
% 1.52/1.00  fof(f73,plain,(
% 1.52/1.00    l1_pre_topc(sK4)),
% 1.52/1.00    inference(cnf_transformation,[],[f47])).
% 1.52/1.00  
% 1.52/1.00  fof(f9,axiom,(
% 1.52/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.00  
% 1.52/1.00  fof(f22,plain,(
% 1.52/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.52/1.00    inference(ennf_transformation,[],[f9])).
% 1.52/1.00  
% 1.52/1.00  fof(f68,plain,(
% 1.52/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.52/1.00    inference(cnf_transformation,[],[f22])).
% 1.52/1.00  
% 1.52/1.00  fof(f7,axiom,(
% 1.52/1.00    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.00  
% 1.52/1.00  fof(f20,plain,(
% 1.52/1.00    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.52/1.00    inference(ennf_transformation,[],[f7])).
% 1.52/1.00  
% 1.52/1.00  fof(f65,plain,(
% 1.52/1.00    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.52/1.00    inference(cnf_transformation,[],[f20])).
% 1.52/1.00  
% 1.52/1.00  fof(f8,axiom,(
% 1.52/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.00  
% 1.52/1.00  fof(f21,plain,(
% 1.52/1.00    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.52/1.00    inference(ennf_transformation,[],[f8])).
% 1.52/1.00  
% 1.52/1.00  fof(f41,plain,(
% 1.52/1.00    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.52/1.00    inference(nnf_transformation,[],[f21])).
% 1.52/1.00  
% 1.52/1.00  fof(f67,plain,(
% 1.52/1.00    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.52/1.00    inference(cnf_transformation,[],[f41])).
% 1.52/1.00  
% 1.52/1.00  fof(f10,axiom,(
% 1.52/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 1.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.00  
% 1.52/1.00  fof(f23,plain,(
% 1.52/1.00    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.52/1.00    inference(ennf_transformation,[],[f10])).
% 1.52/1.00  
% 1.52/1.00  fof(f24,plain,(
% 1.52/1.00    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.52/1.00    inference(flattening,[],[f23])).
% 1.52/1.00  
% 1.52/1.00  fof(f69,plain,(
% 1.52/1.00    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.52/1.00    inference(cnf_transformation,[],[f24])).
% 1.52/1.00  
% 1.52/1.00  fof(f79,plain,(
% 1.52/1.00    ( ! [X3] : (r2_hidden(X3,sK6) | ~r2_hidden(sK5,X3) | ~v4_pre_topc(X3,sK4) | ~v3_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) )),
% 1.52/1.00    inference(cnf_transformation,[],[f47])).
% 1.52/1.00  
% 1.52/1.00  fof(f72,plain,(
% 1.52/1.00    v2_pre_topc(sK4)),
% 1.52/1.00    inference(cnf_transformation,[],[f47])).
% 1.52/1.00  
% 1.52/1.00  fof(f80,plain,(
% 1.52/1.00    k1_xboole_0 = sK6),
% 1.52/1.00    inference(cnf_transformation,[],[f47])).
% 1.52/1.00  
% 1.52/1.00  fof(f3,axiom,(
% 1.52/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.00  
% 1.52/1.00  fof(f50,plain,(
% 1.52/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.52/1.00    inference(cnf_transformation,[],[f3])).
% 1.52/1.00  
% 1.52/1.00  fof(f2,axiom,(
% 1.52/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 1.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.00  
% 1.52/1.00  fof(f49,plain,(
% 1.52/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.52/1.00    inference(cnf_transformation,[],[f2])).
% 1.52/1.00  
% 1.52/1.00  fof(f1,axiom,(
% 1.52/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.00  
% 1.52/1.00  fof(f48,plain,(
% 1.52/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.52/1.00    inference(cnf_transformation,[],[f1])).
% 1.52/1.00  
% 1.52/1.00  fof(f5,axiom,(
% 1.52/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.00  
% 1.52/1.00  fof(f17,plain,(
% 1.52/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.52/1.00    inference(ennf_transformation,[],[f5])).
% 1.52/1.00  
% 1.52/1.00  fof(f52,plain,(
% 1.52/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.52/1.00    inference(cnf_transformation,[],[f17])).
% 1.52/1.00  
% 1.52/1.00  fof(f6,axiom,(
% 1.52/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/1.00  
% 1.52/1.00  fof(f14,plain,(
% 1.52/1.00    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.52/1.00    inference(rectify,[],[f6])).
% 1.52/1.00  
% 1.52/1.00  fof(f18,plain,(
% 1.52/1.00    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.52/1.00    inference(ennf_transformation,[],[f14])).
% 1.52/1.00  
% 1.52/1.00  fof(f19,plain,(
% 1.52/1.00    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.52/1.00    inference(flattening,[],[f18])).
% 1.52/1.00  
% 1.52/1.00  fof(f29,plain,(
% 1.52/1.00    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.52/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.52/1.00  
% 1.52/1.00  fof(f30,plain,(
% 1.52/1.00    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.52/1.00    inference(definition_folding,[],[f19,f29])).
% 1.52/1.00  
% 1.52/1.00  fof(f36,plain,(
% 1.52/1.00    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.52/1.00    inference(nnf_transformation,[],[f30])).
% 1.52/1.00  
% 1.52/1.00  fof(f37,plain,(
% 1.52/1.00    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.52/1.00    inference(flattening,[],[f36])).
% 1.52/1.00  
% 1.52/1.00  fof(f38,plain,(
% 1.52/1.00    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.52/1.00    inference(rectify,[],[f37])).
% 1.52/1.00  
% 1.52/1.00  fof(f39,plain,(
% 1.52/1.00    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.52/1.00    introduced(choice_axiom,[])).
% 1.52/1.00  
% 1.52/1.00  fof(f40,plain,(
% 1.52/1.00    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 1.52/1.00  
% 1.52/1.00  fof(f59,plain,(
% 1.52/1.00    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.52/1.00    inference(cnf_transformation,[],[f40])).
% 1.52/1.00  
% 1.52/1.00  cnf(c_29,negated_conjecture,
% 1.52/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) ),
% 1.52/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_1436,plain,
% 1.52/1.00      ( m1_subset_1(sK5,u1_struct_0(sK4)) = iProver_top ),
% 1.52/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_3,plain,
% 1.52/1.00      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 1.52/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_22,plain,
% 1.52/1.00      ( v2_struct_0(X0)
% 1.52/1.00      | ~ l1_struct_0(X0)
% 1.52/1.00      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 1.52/1.00      inference(cnf_transformation,[],[f70]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_32,negated_conjecture,
% 1.52/1.00      ( ~ v2_struct_0(sK4) ),
% 1.52/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_352,plain,
% 1.52/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK4 != X0 ),
% 1.52/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_353,plain,
% 1.52/1.00      ( ~ l1_struct_0(sK4) | ~ v1_xboole_0(k2_struct_0(sK4)) ),
% 1.52/1.00      inference(unflattening,[status(thm)],[c_352]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_30,negated_conjecture,
% 1.52/1.00      ( l1_pre_topc(sK4) ),
% 1.52/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_51,plain,
% 1.52/1.00      ( v2_struct_0(sK4)
% 1.52/1.00      | ~ l1_struct_0(sK4)
% 1.52/1.00      | ~ v1_xboole_0(k2_struct_0(sK4)) ),
% 1.52/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_20,plain,
% 1.52/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 1.52/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_57,plain,
% 1.52/1.00      ( l1_struct_0(sK4) | ~ l1_pre_topc(sK4) ),
% 1.52/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_355,plain,
% 1.52/1.00      ( ~ v1_xboole_0(k2_struct_0(sK4)) ),
% 1.52/1.00      inference(global_propositional_subsumption,
% 1.52/1.00                [status(thm)],
% 1.52/1.00                [c_353,c_32,c_30,c_51,c_57]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_365,plain,
% 1.52/1.00      ( r2_hidden(X0,X1)
% 1.52/1.00      | ~ m1_subset_1(X0,X1)
% 1.52/1.00      | k2_struct_0(sK4) != X1 ),
% 1.52/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_355]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_366,plain,
% 1.52/1.00      ( r2_hidden(X0,k2_struct_0(sK4))
% 1.52/1.00      | ~ m1_subset_1(X0,k2_struct_0(sK4)) ),
% 1.52/1.00      inference(unflattening,[status(thm)],[c_365]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_1435,plain,
% 1.52/1.00      ( r2_hidden(X0,k2_struct_0(sK4)) = iProver_top
% 1.52/1.00      | m1_subset_1(X0,k2_struct_0(sK4)) != iProver_top ),
% 1.52/1.00      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_17,plain,
% 1.52/1.00      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 1.52/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_380,plain,
% 1.52/1.00      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 1.52/1.00      inference(resolution,[status(thm)],[c_20,c_17]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_569,plain,
% 1.52/1.00      ( k2_struct_0(X0) = u1_struct_0(X0) | sK4 != X0 ),
% 1.52/1.00      inference(resolution_lifted,[status(thm)],[c_380,c_30]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_570,plain,
% 1.52/1.00      ( k2_struct_0(sK4) = u1_struct_0(sK4) ),
% 1.52/1.00      inference(unflattening,[status(thm)],[c_569]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_1482,plain,
% 1.52/1.00      ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
% 1.52/1.00      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 1.52/1.00      inference(light_normalisation,[status(thm)],[c_1435,c_570]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_1900,plain,
% 1.52/1.00      ( r2_hidden(sK5,u1_struct_0(sK4)) = iProver_top ),
% 1.52/1.00      inference(superposition,[status(thm)],[c_1436,c_1482]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_18,plain,
% 1.52/1.00      ( v3_pre_topc(X0,X1)
% 1.52/1.00      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 1.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/1.00      | ~ l1_pre_topc(X1) ),
% 1.52/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_21,plain,
% 1.52/1.00      ( v4_pre_topc(k2_struct_0(X0),X0)
% 1.52/1.00      | ~ l1_pre_topc(X0)
% 1.52/1.00      | ~ v2_pre_topc(X0) ),
% 1.52/1.00      inference(cnf_transformation,[],[f69]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_24,negated_conjecture,
% 1.52/1.00      ( ~ v4_pre_topc(X0,sK4)
% 1.52/1.00      | ~ v3_pre_topc(X0,sK4)
% 1.52/1.00      | r2_hidden(X0,sK6)
% 1.52/1.00      | ~ r2_hidden(sK5,X0)
% 1.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.52/1.00      inference(cnf_transformation,[],[f79]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_395,plain,
% 1.52/1.00      ( ~ v3_pre_topc(X0,sK4)
% 1.52/1.00      | r2_hidden(X0,sK6)
% 1.52/1.00      | ~ r2_hidden(sK5,X0)
% 1.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.52/1.00      | ~ l1_pre_topc(X1)
% 1.52/1.00      | ~ v2_pre_topc(X1)
% 1.52/1.00      | k2_struct_0(X1) != X0
% 1.52/1.00      | sK4 != X1 ),
% 1.52/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_24]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_396,plain,
% 1.52/1.00      ( ~ v3_pre_topc(k2_struct_0(sK4),sK4)
% 1.52/1.00      | r2_hidden(k2_struct_0(sK4),sK6)
% 1.52/1.00      | ~ r2_hidden(sK5,k2_struct_0(sK4))
% 1.52/1.00      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.52/1.00      | ~ l1_pre_topc(sK4)
% 1.52/1.00      | ~ v2_pre_topc(sK4) ),
% 1.52/1.00      inference(unflattening,[status(thm)],[c_395]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_31,negated_conjecture,
% 1.52/1.00      ( v2_pre_topc(sK4) ),
% 1.52/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_398,plain,
% 1.52/1.00      ( ~ v3_pre_topc(k2_struct_0(sK4),sK4)
% 1.52/1.00      | r2_hidden(k2_struct_0(sK4),sK6)
% 1.52/1.00      | ~ r2_hidden(sK5,k2_struct_0(sK4))
% 1.52/1.00      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.52/1.00      inference(global_propositional_subsumption,
% 1.52/1.00                [status(thm)],
% 1.52/1.00                [c_396,c_31,c_30]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_538,plain,
% 1.52/1.00      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 1.52/1.00      | r2_hidden(k2_struct_0(sK4),sK6)
% 1.52/1.00      | ~ r2_hidden(sK5,k2_struct_0(sK4))
% 1.52/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/1.00      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.52/1.00      | ~ l1_pre_topc(X1)
% 1.52/1.00      | k2_struct_0(sK4) != X0
% 1.52/1.00      | sK4 != X1 ),
% 1.52/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_398]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_539,plain,
% 1.52/1.00      ( ~ r2_hidden(k2_struct_0(sK4),u1_pre_topc(sK4))
% 1.52/1.00      | r2_hidden(k2_struct_0(sK4),sK6)
% 1.52/1.00      | ~ r2_hidden(sK5,k2_struct_0(sK4))
% 1.52/1.00      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.52/1.00      | ~ l1_pre_topc(sK4) ),
% 1.52/1.00      inference(unflattening,[status(thm)],[c_538]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_541,plain,
% 1.52/1.00      ( ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.52/1.00      | ~ r2_hidden(sK5,k2_struct_0(sK4))
% 1.52/1.00      | r2_hidden(k2_struct_0(sK4),sK6)
% 1.52/1.00      | ~ r2_hidden(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
% 1.52/1.00      inference(global_propositional_subsumption,
% 1.52/1.00                [status(thm)],
% 1.52/1.00                [c_539,c_30]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_542,plain,
% 1.52/1.00      ( ~ r2_hidden(k2_struct_0(sK4),u1_pre_topc(sK4))
% 1.52/1.00      | r2_hidden(k2_struct_0(sK4),sK6)
% 1.52/1.00      | ~ r2_hidden(sK5,k2_struct_0(sK4))
% 1.52/1.00      | ~ m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.52/1.00      inference(renaming,[status(thm)],[c_541]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_1432,plain,
% 1.52/1.00      ( r2_hidden(k2_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top
% 1.52/1.00      | r2_hidden(k2_struct_0(sK4),sK6) = iProver_top
% 1.52/1.00      | r2_hidden(sK5,k2_struct_0(sK4)) != iProver_top
% 1.52/1.00      | m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.52/1.00      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_23,negated_conjecture,
% 1.52/1.00      ( k1_xboole_0 = sK6 ),
% 1.52/1.00      inference(cnf_transformation,[],[f80]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_1497,plain,
% 1.52/1.00      ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top
% 1.52/1.00      | r2_hidden(u1_struct_0(sK4),k1_xboole_0) = iProver_top
% 1.52/1.00      | r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top
% 1.52/1.00      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.52/1.00      inference(light_normalisation,[status(thm)],[c_1432,c_23,c_570]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_2,plain,
% 1.52/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.52/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_1445,plain,
% 1.52/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.52/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_1,plain,
% 1.52/1.00      ( k2_subset_1(X0) = X0 ),
% 1.52/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_1460,plain,
% 1.52/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.52/1.00      inference(light_normalisation,[status(thm)],[c_1445,c_1]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_0,plain,
% 1.52/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 1.52/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_4,plain,
% 1.52/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 1.52/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_632,plain,
% 1.52/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 1.52/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_633,plain,
% 1.52/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 1.52/1.00      inference(unflattening,[status(thm)],[c_632]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_1434,plain,
% 1.52/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.52/1.00      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_16,plain,
% 1.52/1.00      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 1.52/1.00      | ~ l1_pre_topc(X0)
% 1.52/1.00      | ~ v2_pre_topc(X0) ),
% 1.52/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_574,plain,
% 1.52/1.00      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 1.52/1.00      | ~ v2_pre_topc(X0)
% 1.52/1.00      | sK4 != X0 ),
% 1.52/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_30]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_575,plain,
% 1.52/1.00      ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
% 1.52/1.00      | ~ v2_pre_topc(sK4) ),
% 1.52/1.00      inference(unflattening,[status(thm)],[c_574]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_69,plain,
% 1.52/1.00      ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
% 1.52/1.00      | ~ l1_pre_topc(sK4)
% 1.52/1.00      | ~ v2_pre_topc(sK4) ),
% 1.52/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_577,plain,
% 1.52/1.00      ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 1.52/1.00      inference(global_propositional_subsumption,
% 1.52/1.00                [status(thm)],
% 1.52/1.00                [c_575,c_31,c_30,c_69]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_1431,plain,
% 1.52/1.00      ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) = iProver_top ),
% 1.52/1.00      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(c_1502,plain,
% 1.52/1.00      ( r2_hidden(sK5,u1_struct_0(sK4)) != iProver_top ),
% 1.52/1.00      inference(forward_subsumption_resolution,
% 1.52/1.00                [status(thm)],
% 1.52/1.00                [c_1497,c_1460,c_1434,c_1431]) ).
% 1.52/1.00  
% 1.52/1.00  cnf(contradiction,plain,
% 1.52/1.00      ( $false ),
% 1.52/1.00      inference(minisat,[status(thm)],[c_1900,c_1502]) ).
% 1.52/1.00  
% 1.52/1.00  
% 1.52/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.52/1.00  
% 1.52/1.00  ------                               Statistics
% 1.52/1.00  
% 1.52/1.00  ------ General
% 1.52/1.00  
% 1.52/1.00  abstr_ref_over_cycles:                  0
% 1.52/1.00  abstr_ref_under_cycles:                 0
% 1.52/1.00  gc_basic_clause_elim:                   0
% 1.52/1.00  forced_gc_time:                         0
% 1.52/1.00  parsing_time:                           0.009
% 1.52/1.00  unif_index_cands_time:                  0.
% 1.52/1.00  unif_index_add_time:                    0.
% 1.52/1.00  orderings_time:                         0.
% 1.52/1.00  out_proof_time:                         0.01
% 1.52/1.00  total_time:                             0.085
% 1.52/1.00  num_of_symbols:                         56
% 1.52/1.00  num_of_terms:                           1245
% 1.52/1.00  
% 1.52/1.00  ------ Preprocessing
% 1.52/1.00  
% 1.52/1.00  num_of_splits:                          0
% 1.52/1.00  num_of_split_atoms:                     0
% 1.52/1.00  num_of_reused_defs:                     0
% 1.52/1.00  num_eq_ax_congr_red:                    15
% 1.52/1.00  num_of_sem_filtered_clauses:            1
% 1.52/1.00  num_of_subtypes:                        0
% 1.52/1.00  monotx_restored_types:                  0
% 1.52/1.00  sat_num_of_epr_types:                   0
% 1.52/1.00  sat_num_of_non_cyclic_types:            0
% 1.52/1.00  sat_guarded_non_collapsed_types:        0
% 1.52/1.00  num_pure_diseq_elim:                    0
% 1.52/1.00  simp_replaced_by:                       0
% 1.52/1.00  res_preprocessed:                       116
% 1.52/1.00  prep_upred:                             0
% 1.52/1.00  prep_unflattend:                        39
% 1.52/1.00  smt_new_axioms:                         0
% 1.52/1.00  pred_elim_cands:                        3
% 1.52/1.00  pred_elim:                              8
% 1.52/1.00  pred_elim_cl:                           13
% 1.52/1.00  pred_elim_cycles:                       11
% 1.52/1.00  merged_defs:                            0
% 1.52/1.00  merged_defs_ncl:                        0
% 1.52/1.00  bin_hyper_res:                          0
% 1.52/1.00  prep_cycles:                            4
% 1.52/1.00  pred_elim_time:                         0.011
% 1.52/1.00  splitting_time:                         0.
% 1.52/1.00  sem_filter_time:                        0.
% 1.52/1.00  monotx_time:                            0.
% 1.52/1.00  subtype_inf_time:                       0.
% 1.52/1.00  
% 1.52/1.00  ------ Problem properties
% 1.52/1.00  
% 1.52/1.00  clauses:                                20
% 1.52/1.00  conjectures:                            4
% 1.52/1.00  epr:                                    3
% 1.52/1.00  horn:                                   16
% 1.52/1.00  ground:                                 8
% 1.52/1.00  unary:                                  9
% 1.52/1.00  binary:                                 7
% 1.52/1.00  lits:                                   39
% 1.52/1.00  lits_eq:                                3
% 1.52/1.00  fd_pure:                                0
% 1.52/1.00  fd_pseudo:                              0
% 1.52/1.00  fd_cond:                                0
% 1.52/1.00  fd_pseudo_cond:                         0
% 1.52/1.00  ac_symbols:                             0
% 1.52/1.00  
% 1.52/1.00  ------ Propositional Solver
% 1.52/1.00  
% 1.52/1.00  prop_solver_calls:                      24
% 1.52/1.00  prop_fast_solver_calls:                 688
% 1.52/1.00  smt_solver_calls:                       0
% 1.52/1.00  smt_fast_solver_calls:                  0
% 1.52/1.00  prop_num_of_clauses:                    422
% 1.52/1.00  prop_preprocess_simplified:             3115
% 1.52/1.00  prop_fo_subsumed:                       8
% 1.52/1.00  prop_solver_time:                       0.
% 1.52/1.00  smt_solver_time:                        0.
% 1.52/1.00  smt_fast_solver_time:                   0.
% 1.52/1.00  prop_fast_solver_time:                  0.
% 1.52/1.00  prop_unsat_core_time:                   0.
% 1.52/1.00  
% 1.52/1.00  ------ QBF
% 1.52/1.00  
% 1.52/1.00  qbf_q_res:                              0
% 1.52/1.00  qbf_num_tautologies:                    0
% 1.52/1.00  qbf_prep_cycles:                        0
% 1.52/1.00  
% 1.52/1.00  ------ BMC1
% 1.52/1.00  
% 1.52/1.00  bmc1_current_bound:                     -1
% 1.52/1.00  bmc1_last_solved_bound:                 -1
% 1.52/1.00  bmc1_unsat_core_size:                   -1
% 1.52/1.00  bmc1_unsat_core_parents_size:           -1
% 1.52/1.00  bmc1_merge_next_fun:                    0
% 1.52/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.52/1.00  
% 1.52/1.00  ------ Instantiation
% 1.52/1.00  
% 1.52/1.00  inst_num_of_clauses:                    109
% 1.52/1.00  inst_num_in_passive:                    41
% 1.52/1.00  inst_num_in_active:                     66
% 1.52/1.00  inst_num_in_unprocessed:                2
% 1.52/1.00  inst_num_of_loops:                      70
% 1.52/1.00  inst_num_of_learning_restarts:          0
% 1.52/1.00  inst_num_moves_active_passive:          1
% 1.52/1.00  inst_lit_activity:                      0
% 1.52/1.00  inst_lit_activity_moves:                0
% 1.52/1.00  inst_num_tautologies:                   0
% 1.52/1.00  inst_num_prop_implied:                  0
% 1.52/1.00  inst_num_existing_simplified:           0
% 1.52/1.00  inst_num_eq_res_simplified:             0
% 1.52/1.00  inst_num_child_elim:                    0
% 1.52/1.00  inst_num_of_dismatching_blockings:      10
% 1.52/1.00  inst_num_of_non_proper_insts:           52
% 1.52/1.00  inst_num_of_duplicates:                 0
% 1.52/1.00  inst_inst_num_from_inst_to_res:         0
% 1.52/1.00  inst_dismatching_checking_time:         0.
% 1.52/1.00  
% 1.52/1.00  ------ Resolution
% 1.52/1.00  
% 1.52/1.00  res_num_of_clauses:                     0
% 1.52/1.00  res_num_in_passive:                     0
% 1.52/1.00  res_num_in_active:                      0
% 1.52/1.00  res_num_of_loops:                       120
% 1.52/1.00  res_forward_subset_subsumed:            7
% 1.52/1.00  res_backward_subset_subsumed:           0
% 1.52/1.00  res_forward_subsumed:                   0
% 1.52/1.00  res_backward_subsumed:                  0
% 1.52/1.00  res_forward_subsumption_resolution:     0
% 1.52/1.00  res_backward_subsumption_resolution:    0
% 1.52/1.00  res_clause_to_clause_subsumption:       49
% 1.52/1.00  res_orphan_elimination:                 0
% 1.52/1.00  res_tautology_del:                      12
% 1.52/1.00  res_num_eq_res_simplified:              0
% 1.52/1.00  res_num_sel_changes:                    0
% 1.52/1.00  res_moves_from_active_to_pass:          0
% 1.52/1.00  
% 1.52/1.00  ------ Superposition
% 1.52/1.00  
% 1.52/1.00  sup_time_total:                         0.
% 1.52/1.00  sup_time_generating:                    0.
% 1.52/1.00  sup_time_sim_full:                      0.
% 1.52/1.00  sup_time_sim_immed:                     0.
% 1.52/1.00  
% 1.52/1.00  sup_num_of_clauses:                     19
% 1.52/1.00  sup_num_in_active:                      14
% 1.52/1.00  sup_num_in_passive:                     5
% 1.52/1.00  sup_num_of_loops:                       13
% 1.52/1.00  sup_fw_superposition:                   1
% 1.52/1.00  sup_bw_superposition:                   0
% 1.52/1.00  sup_immediate_simplified:               0
% 1.52/1.00  sup_given_eliminated:                   0
% 1.52/1.00  comparisons_done:                       0
% 1.52/1.00  comparisons_avoided:                    0
% 1.52/1.00  
% 1.52/1.00  ------ Simplifications
% 1.52/1.00  
% 1.52/1.00  
% 1.52/1.00  sim_fw_subset_subsumed:                 0
% 1.52/1.00  sim_bw_subset_subsumed:                 0
% 1.52/1.00  sim_fw_subsumed:                        2
% 1.52/1.00  sim_bw_subsumed:                        0
% 1.52/1.00  sim_fw_subsumption_res:                 4
% 1.52/1.00  sim_bw_subsumption_res:                 0
% 1.52/1.00  sim_tautology_del:                      0
% 1.52/1.00  sim_eq_tautology_del:                   0
% 1.52/1.00  sim_eq_res_simp:                        0
% 1.52/1.00  sim_fw_demodulated:                     0
% 1.52/1.00  sim_bw_demodulated:                     0
% 1.52/1.00  sim_light_normalised:                   6
% 1.52/1.00  sim_joinable_taut:                      0
% 1.52/1.00  sim_joinable_simp:                      0
% 1.52/1.00  sim_ac_normalised:                      0
% 1.52/1.00  sim_smt_subsumption:                    0
% 1.52/1.00  
%------------------------------------------------------------------------------
