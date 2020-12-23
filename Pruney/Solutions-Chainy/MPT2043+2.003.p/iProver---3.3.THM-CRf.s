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
% DateTime   : Thu Dec  3 12:29:01 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 328 expanded)
%              Number of clauses        :   69 (  94 expanded)
%              Number of leaves         :   21 (  87 expanded)
%              Depth                    :   17
%              Number of atoms          :  468 (1291 expanded)
%              Number of equality atoms :  130 ( 236 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k9_setfam_1(X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f107,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k9_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f63,f67])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
              & v13_waybel_0(X1,k3_yellow_1(X0))
              & v2_waybel_0(X1,k3_yellow_1(X0))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ~ ( v1_xboole_0(X2)
                  & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
              & v13_waybel_0(X1,k3_yellow_1(X0))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ~ ( v1_xboole_0(X2)
                  & r2_hidden(X2,X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f48,plain,(
    ! [X1] :
      ( ? [X2] :
          ( v1_xboole_0(X2)
          & r2_hidden(X2,X1) )
     => ( v1_xboole_0(sK7)
        & r2_hidden(sK7,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( v1_xboole_0(X2)
            & r2_hidden(X2,sK6) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(sK6,k3_yellow_1(X0))
        & v1_subset_1(sK6,u1_struct_0(k3_yellow_1(X0)))
        & ~ v1_xboole_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK5))))
          & v13_waybel_0(X1,k3_yellow_1(sK5))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK5)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( v1_xboole_0(sK7)
    & r2_hidden(sK7,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK5))))
    & v13_waybel_0(sK6,k3_yellow_1(sK5))
    & v1_subset_1(sK6,u1_struct_0(k3_yellow_1(sK5)))
    & ~ v1_xboole_0(sK6)
    & ~ v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f26,f48,f47,f46])).

fof(f81,plain,(
    v13_waybel_0(sK6,k3_yellow_1(sK5)) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0] : k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f102,plain,(
    v13_waybel_0(sK6,k2_yellow_1(k9_setfam_1(sK5))) ),
    inference(definition_unfolding,[],[f81,f70])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ? [X2,X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) ) )
        & ( ! [X2,X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ r1_tarski(X3,X0)
              | ~ r1_tarski(X2,X3) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ? [X2,X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) ) )
        & ( ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1)
              | ~ r1_tarski(X5,X0)
              | ~ r1_tarski(X4,X5) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & r1_tarski(X3,X0)
          & r1_tarski(X2,X3) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X1)
        & r1_tarski(sK4(X0,X1),X0)
        & r1_tarski(sK3(X0,X1),sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ( ~ r2_hidden(sK4(X0,X1),X1)
            & r2_hidden(sK3(X0,X1),X1)
            & r1_tarski(sK4(X0,X1),X0)
            & r1_tarski(sK3(X0,X1),sK4(X0,X1)) ) )
        & ( ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1)
              | ~ r1_tarski(X5,X0)
              | ~ r1_tarski(X4,X5) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f43,f44])).

fof(f73,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f100,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))) ) ),
    inference(definition_unfolding,[],[f73,f70,f67,f70])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f82,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK5)))) ),
    inference(cnf_transformation,[],[f49])).

fof(f101,plain,(
    m1_subset_1(sK6,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))))) ),
    inference(definition_unfolding,[],[f82,f67,f70])).

fof(f83,plain,(
    r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f84,plain,(
    v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k9_setfam_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k9_setfam_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f67])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f71,f67])).

fof(f108,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k9_setfam_1(X1)) ) ),
    inference(equality_resolution,[],[f95])).

fof(f80,plain,(
    v1_subset_1(sK6,u1_struct_0(k3_yellow_1(sK5))) ),
    inference(cnf_transformation,[],[f49])).

fof(f103,plain,(
    v1_subset_1(sK6,u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))) ),
    inference(definition_unfolding,[],[f80,f70])).

cnf(c_940,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4093,plain,
    ( X0 != X1
    | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != X1
    | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) = X0 ),
    inference(instantiation,[status(thm)],[c_940])).

cnf(c_23666,plain,
    ( X0 != k9_setfam_1(sK5)
    | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) = X0
    | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != k9_setfam_1(sK5) ),
    inference(instantiation,[status(thm)],[c_4093])).

cnf(c_23667,plain,
    ( u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != k9_setfam_1(sK5)
    | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) = sK6
    | sK6 != k9_setfam_1(sK5) ),
    inference(instantiation,[status(thm)],[c_23666])).

cnf(c_1894,plain,
    ( u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != X0
    | sK6 != X0
    | sK6 = u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) ),
    inference(instantiation,[status(thm)],[c_940])).

cnf(c_14891,plain,
    ( u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != k9_setfam_1(sK5)
    | sK6 = u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))
    | sK6 != k9_setfam_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1547,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_setfam_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1538,plain,
    ( r2_hidden(X0,k9_setfam_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2831,plain,
    ( r1_tarski(sK0(k9_setfam_1(X0),X1),X0) = iProver_top
    | r1_tarski(k9_setfam_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_1538])).

cnf(c_12,plain,
    ( m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1537,plain,
    ( m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1535,plain,
    ( m1_subset_1(X0,k9_setfam_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2188,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1537,c_1535])).

cnf(c_28,negated_conjecture,
    ( v13_waybel_0(sK6,k2_yellow_1(k9_setfam_1(sK5))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1526,plain,
    ( v13_waybel_0(sK6,k2_yellow_1(k9_setfam_1(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,plain,
    ( ~ v13_waybel_0(X0,k2_yellow_1(k9_setfam_1(X1)))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X1)))))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X3,X0)
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1529,plain,
    ( v13_waybel_0(X0,k2_yellow_1(k9_setfam_1(X1))) != iProver_top
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X1))))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X3,X0) = iProver_top
    | r1_tarski(X3,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_17,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1669,plain,
    ( v13_waybel_0(X0,k2_yellow_1(k9_setfam_1(X1))) != iProver_top
    | m1_subset_1(X0,k9_setfam_1(k9_setfam_1(X1))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X3,X0) = iProver_top
    | r1_tarski(X3,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1529,c_17])).

cnf(c_4857,plain,
    ( m1_subset_1(sK6,k9_setfam_1(k9_setfam_1(sK5))) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1526,c_1669])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1527,plain,
    ( m1_subset_1(sK6,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1563,plain,
    ( m1_subset_1(sK6,k9_setfam_1(k9_setfam_1(sK5))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1527,c_17])).

cnf(c_4988,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X1,sK6) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4857,c_1563])).

cnf(c_5000,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(k1_xboole_0,sK6) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2188,c_4988])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK7,sK6) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_37,plain,
    ( r2_hidden(sK7,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1542,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_25,negated_conjecture,
    ( v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k9_setfam_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_236,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k9_setfam_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_237,plain,
    ( m1_subset_1(X0,k9_setfam_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_236])).

cnf(c_293,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_237])).

cnf(c_407,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_293])).

cnf(c_408,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,sK7) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_1525,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_2830,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_1525])).

cnf(c_3434,plain,
    ( r1_tarski(sK7,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1542,c_2830])).

cnf(c_5002,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r2_hidden(sK7,sK6) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3434,c_4988])).

cnf(c_5153,plain,
    ( r2_hidden(X0,sK6) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5000,c_37,c_5002])).

cnf(c_8449,plain,
    ( r2_hidden(sK0(k9_setfam_1(sK5),X0),sK6) = iProver_top
    | r1_tarski(k9_setfam_1(sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2831,c_5153])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1548,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9649,plain,
    ( r1_tarski(k9_setfam_1(sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_8449,c_1548])).

cnf(c_943,plain,
    ( X0 != X1
    | k9_setfam_1(X0) = k9_setfam_1(X1) ),
    theory(equality)).

cnf(c_7631,plain,
    ( u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != X0
    | k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))) = k9_setfam_1(X0) ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_7632,plain,
    ( u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != sK6
    | k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))) = k9_setfam_1(sK6) ),
    inference(instantiation,[status(thm)],[c_7631])).

cnf(c_944,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1862,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k9_setfam_1(X3))
    | X0 != X2
    | X1 != k9_setfam_1(X3) ),
    inference(instantiation,[status(thm)],[c_944])).

cnf(c_7004,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | m1_subset_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))),k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))))
    | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != X0
    | k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))) != k9_setfam_1(X1) ),
    inference(instantiation,[status(thm)],[c_1862])).

cnf(c_7006,plain,
    ( m1_subset_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))),k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))))
    | ~ m1_subset_1(sK6,k9_setfam_1(sK6))
    | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != sK6
    | k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))) != k9_setfam_1(sK6) ),
    inference(instantiation,[status(thm)],[c_7004])).

cnf(c_2644,plain,
    ( u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) = k9_setfam_1(sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2616,plain,
    ( ~ r1_tarski(X0,k9_setfam_1(sK5))
    | ~ r1_tarski(k9_setfam_1(sK5),X0)
    | X0 = k9_setfam_1(sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2627,plain,
    ( X0 = k9_setfam_1(sK5)
    | r1_tarski(X0,k9_setfam_1(sK5)) != iProver_top
    | r1_tarski(k9_setfam_1(sK5),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2616])).

cnf(c_2629,plain,
    ( sK6 = k9_setfam_1(sK5)
    | r1_tarski(k9_setfam_1(sK5),sK6) != iProver_top
    | r1_tarski(sK6,k9_setfam_1(sK5)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2627])).

cnf(c_2189,plain,
    ( r1_tarski(sK6,k9_setfam_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1563,c_1535])).

cnf(c_19,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_29,negated_conjecture,
    ( v1_subset_1(sK6,u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X0))
    | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != X0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_427,plain,
    ( ~ m1_subset_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))),k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))))
    | sK6 != u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_85,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_67,plain,
    ( m1_subset_1(sK6,k9_setfam_1(sK6))
    | ~ r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23667,c_14891,c_9649,c_7632,c_7006,c_2644,c_2629,c_2189,c_427,c_85,c_67])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.68/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.00  
% 2.68/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.68/1.00  
% 2.68/1.00  ------  iProver source info
% 2.68/1.00  
% 2.68/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.68/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.68/1.00  git: non_committed_changes: false
% 2.68/1.00  git: last_make_outside_of_git: false
% 2.68/1.00  
% 2.68/1.00  ------ 
% 2.68/1.00  
% 2.68/1.00  ------ Input Options
% 2.68/1.00  
% 2.68/1.00  --out_options                           all
% 2.68/1.00  --tptp_safe_out                         true
% 2.68/1.00  --problem_path                          ""
% 2.68/1.00  --include_path                          ""
% 2.68/1.00  --clausifier                            res/vclausify_rel
% 2.68/1.00  --clausifier_options                    --mode clausify
% 2.68/1.00  --stdin                                 false
% 2.68/1.00  --stats_out                             all
% 2.68/1.00  
% 2.68/1.00  ------ General Options
% 2.68/1.00  
% 2.68/1.00  --fof                                   false
% 2.68/1.00  --time_out_real                         305.
% 2.68/1.00  --time_out_virtual                      -1.
% 2.68/1.00  --symbol_type_check                     false
% 2.68/1.00  --clausify_out                          false
% 2.68/1.00  --sig_cnt_out                           false
% 2.68/1.00  --trig_cnt_out                          false
% 2.68/1.00  --trig_cnt_out_tolerance                1.
% 2.68/1.00  --trig_cnt_out_sk_spl                   false
% 2.68/1.00  --abstr_cl_out                          false
% 2.68/1.00  
% 2.68/1.00  ------ Global Options
% 2.68/1.00  
% 2.68/1.00  --schedule                              default
% 2.68/1.00  --add_important_lit                     false
% 2.68/1.00  --prop_solver_per_cl                    1000
% 2.68/1.00  --min_unsat_core                        false
% 2.68/1.00  --soft_assumptions                      false
% 2.68/1.00  --soft_lemma_size                       3
% 2.68/1.00  --prop_impl_unit_size                   0
% 2.68/1.00  --prop_impl_unit                        []
% 2.68/1.00  --share_sel_clauses                     true
% 2.68/1.00  --reset_solvers                         false
% 2.68/1.00  --bc_imp_inh                            [conj_cone]
% 2.68/1.00  --conj_cone_tolerance                   3.
% 2.68/1.00  --extra_neg_conj                        none
% 2.68/1.00  --large_theory_mode                     true
% 2.68/1.00  --prolific_symb_bound                   200
% 2.68/1.00  --lt_threshold                          2000
% 2.68/1.00  --clause_weak_htbl                      true
% 2.68/1.00  --gc_record_bc_elim                     false
% 2.68/1.00  
% 2.68/1.00  ------ Preprocessing Options
% 2.68/1.00  
% 2.68/1.00  --preprocessing_flag                    true
% 2.68/1.00  --time_out_prep_mult                    0.1
% 2.68/1.00  --splitting_mode                        input
% 2.68/1.00  --splitting_grd                         true
% 2.68/1.00  --splitting_cvd                         false
% 2.68/1.00  --splitting_cvd_svl                     false
% 2.68/1.00  --splitting_nvd                         32
% 2.68/1.00  --sub_typing                            true
% 2.68/1.00  --prep_gs_sim                           true
% 2.68/1.00  --prep_unflatten                        true
% 2.68/1.00  --prep_res_sim                          true
% 2.68/1.00  --prep_upred                            true
% 2.68/1.00  --prep_sem_filter                       exhaustive
% 2.68/1.00  --prep_sem_filter_out                   false
% 2.68/1.00  --pred_elim                             true
% 2.68/1.00  --res_sim_input                         true
% 2.68/1.00  --eq_ax_congr_red                       true
% 2.68/1.00  --pure_diseq_elim                       true
% 2.68/1.00  --brand_transform                       false
% 2.68/1.00  --non_eq_to_eq                          false
% 2.68/1.00  --prep_def_merge                        true
% 2.68/1.00  --prep_def_merge_prop_impl              false
% 2.68/1.00  --prep_def_merge_mbd                    true
% 2.68/1.00  --prep_def_merge_tr_red                 false
% 2.68/1.00  --prep_def_merge_tr_cl                  false
% 2.68/1.00  --smt_preprocessing                     true
% 2.68/1.00  --smt_ac_axioms                         fast
% 2.68/1.00  --preprocessed_out                      false
% 2.68/1.00  --preprocessed_stats                    false
% 2.68/1.00  
% 2.68/1.00  ------ Abstraction refinement Options
% 2.68/1.00  
% 2.68/1.00  --abstr_ref                             []
% 2.68/1.00  --abstr_ref_prep                        false
% 2.68/1.00  --abstr_ref_until_sat                   false
% 2.68/1.00  --abstr_ref_sig_restrict                funpre
% 2.68/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.68/1.00  --abstr_ref_under                       []
% 2.68/1.00  
% 2.68/1.00  ------ SAT Options
% 2.68/1.00  
% 2.68/1.00  --sat_mode                              false
% 2.68/1.00  --sat_fm_restart_options                ""
% 2.68/1.00  --sat_gr_def                            false
% 2.68/1.00  --sat_epr_types                         true
% 2.68/1.00  --sat_non_cyclic_types                  false
% 2.68/1.00  --sat_finite_models                     false
% 2.68/1.00  --sat_fm_lemmas                         false
% 2.68/1.00  --sat_fm_prep                           false
% 2.68/1.00  --sat_fm_uc_incr                        true
% 2.68/1.00  --sat_out_model                         small
% 2.68/1.00  --sat_out_clauses                       false
% 2.68/1.00  
% 2.68/1.00  ------ QBF Options
% 2.68/1.00  
% 2.68/1.00  --qbf_mode                              false
% 2.68/1.00  --qbf_elim_univ                         false
% 2.68/1.00  --qbf_dom_inst                          none
% 2.68/1.00  --qbf_dom_pre_inst                      false
% 2.68/1.00  --qbf_sk_in                             false
% 2.68/1.00  --qbf_pred_elim                         true
% 2.68/1.00  --qbf_split                             512
% 2.68/1.00  
% 2.68/1.00  ------ BMC1 Options
% 2.68/1.00  
% 2.68/1.00  --bmc1_incremental                      false
% 2.68/1.00  --bmc1_axioms                           reachable_all
% 2.68/1.00  --bmc1_min_bound                        0
% 2.68/1.00  --bmc1_max_bound                        -1
% 2.68/1.00  --bmc1_max_bound_default                -1
% 2.68/1.00  --bmc1_symbol_reachability              true
% 2.68/1.00  --bmc1_property_lemmas                  false
% 2.68/1.00  --bmc1_k_induction                      false
% 2.68/1.00  --bmc1_non_equiv_states                 false
% 2.68/1.00  --bmc1_deadlock                         false
% 2.68/1.00  --bmc1_ucm                              false
% 2.68/1.00  --bmc1_add_unsat_core                   none
% 2.68/1.00  --bmc1_unsat_core_children              false
% 2.68/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.68/1.00  --bmc1_out_stat                         full
% 2.68/1.00  --bmc1_ground_init                      false
% 2.68/1.00  --bmc1_pre_inst_next_state              false
% 2.68/1.00  --bmc1_pre_inst_state                   false
% 2.68/1.00  --bmc1_pre_inst_reach_state             false
% 2.68/1.00  --bmc1_out_unsat_core                   false
% 2.68/1.00  --bmc1_aig_witness_out                  false
% 2.68/1.00  --bmc1_verbose                          false
% 2.68/1.00  --bmc1_dump_clauses_tptp                false
% 2.68/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.68/1.00  --bmc1_dump_file                        -
% 2.68/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.68/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.68/1.00  --bmc1_ucm_extend_mode                  1
% 2.68/1.00  --bmc1_ucm_init_mode                    2
% 2.68/1.00  --bmc1_ucm_cone_mode                    none
% 2.68/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.68/1.00  --bmc1_ucm_relax_model                  4
% 2.68/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.68/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.68/1.00  --bmc1_ucm_layered_model                none
% 2.68/1.00  --bmc1_ucm_max_lemma_size               10
% 2.68/1.00  
% 2.68/1.00  ------ AIG Options
% 2.68/1.00  
% 2.68/1.00  --aig_mode                              false
% 2.68/1.00  
% 2.68/1.00  ------ Instantiation Options
% 2.68/1.00  
% 2.68/1.00  --instantiation_flag                    true
% 2.68/1.00  --inst_sos_flag                         false
% 2.68/1.00  --inst_sos_phase                        true
% 2.68/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.68/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.68/1.00  --inst_lit_sel_side                     num_symb
% 2.68/1.00  --inst_solver_per_active                1400
% 2.68/1.00  --inst_solver_calls_frac                1.
% 2.68/1.00  --inst_passive_queue_type               priority_queues
% 2.68/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.68/1.00  --inst_passive_queues_freq              [25;2]
% 2.68/1.00  --inst_dismatching                      true
% 2.68/1.00  --inst_eager_unprocessed_to_passive     true
% 2.68/1.00  --inst_prop_sim_given                   true
% 2.68/1.00  --inst_prop_sim_new                     false
% 2.68/1.00  --inst_subs_new                         false
% 2.68/1.00  --inst_eq_res_simp                      false
% 2.68/1.00  --inst_subs_given                       false
% 2.68/1.00  --inst_orphan_elimination               true
% 2.68/1.00  --inst_learning_loop_flag               true
% 2.68/1.00  --inst_learning_start                   3000
% 2.68/1.00  --inst_learning_factor                  2
% 2.68/1.00  --inst_start_prop_sim_after_learn       3
% 2.68/1.00  --inst_sel_renew                        solver
% 2.68/1.00  --inst_lit_activity_flag                true
% 2.68/1.00  --inst_restr_to_given                   false
% 2.68/1.00  --inst_activity_threshold               500
% 2.68/1.00  --inst_out_proof                        true
% 2.68/1.00  
% 2.68/1.00  ------ Resolution Options
% 2.68/1.00  
% 2.68/1.00  --resolution_flag                       true
% 2.68/1.00  --res_lit_sel                           adaptive
% 2.68/1.00  --res_lit_sel_side                      none
% 2.68/1.00  --res_ordering                          kbo
% 2.68/1.00  --res_to_prop_solver                    active
% 2.68/1.00  --res_prop_simpl_new                    false
% 2.68/1.00  --res_prop_simpl_given                  true
% 2.68/1.00  --res_passive_queue_type                priority_queues
% 2.68/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.68/1.00  --res_passive_queues_freq               [15;5]
% 2.68/1.00  --res_forward_subs                      full
% 2.68/1.00  --res_backward_subs                     full
% 2.68/1.00  --res_forward_subs_resolution           true
% 2.68/1.00  --res_backward_subs_resolution          true
% 2.68/1.00  --res_orphan_elimination                true
% 2.68/1.00  --res_time_limit                        2.
% 2.68/1.00  --res_out_proof                         true
% 2.68/1.00  
% 2.68/1.00  ------ Superposition Options
% 2.68/1.00  
% 2.68/1.00  --superposition_flag                    true
% 2.68/1.00  --sup_passive_queue_type                priority_queues
% 2.68/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.68/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.68/1.00  --demod_completeness_check              fast
% 2.68/1.00  --demod_use_ground                      true
% 2.68/1.00  --sup_to_prop_solver                    passive
% 2.68/1.00  --sup_prop_simpl_new                    true
% 2.68/1.00  --sup_prop_simpl_given                  true
% 2.68/1.00  --sup_fun_splitting                     false
% 2.68/1.00  --sup_smt_interval                      50000
% 2.68/1.00  
% 2.68/1.00  ------ Superposition Simplification Setup
% 2.68/1.00  
% 2.68/1.00  --sup_indices_passive                   []
% 2.68/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.68/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.00  --sup_full_bw                           [BwDemod]
% 2.68/1.00  --sup_immed_triv                        [TrivRules]
% 2.68/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.68/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.00  --sup_immed_bw_main                     []
% 2.68/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.68/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/1.00  
% 2.68/1.00  ------ Combination Options
% 2.68/1.00  
% 2.68/1.00  --comb_res_mult                         3
% 2.68/1.00  --comb_sup_mult                         2
% 2.68/1.00  --comb_inst_mult                        10
% 2.68/1.00  
% 2.68/1.00  ------ Debug Options
% 2.68/1.00  
% 2.68/1.00  --dbg_backtrace                         false
% 2.68/1.00  --dbg_dump_prop_clauses                 false
% 2.68/1.00  --dbg_dump_prop_clauses_file            -
% 2.68/1.00  --dbg_out_stat                          false
% 2.68/1.00  ------ Parsing...
% 2.68/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.68/1.00  
% 2.68/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.68/1.00  
% 2.68/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.68/1.00  
% 2.68/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.68/1.00  ------ Proving...
% 2.68/1.00  ------ Problem Properties 
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  clauses                                 28
% 2.68/1.00  conjectures                             3
% 2.68/1.00  EPR                                     7
% 2.68/1.00  Horn                                    22
% 2.68/1.00  unary                                   8
% 2.68/1.00  binary                                  8
% 2.68/1.00  lits                                    63
% 2.68/1.00  lits eq                                 9
% 2.68/1.00  fd_pure                                 0
% 2.68/1.00  fd_pseudo                               0
% 2.68/1.00  fd_cond                                 0
% 2.68/1.00  fd_pseudo_cond                          5
% 2.68/1.00  AC symbols                              0
% 2.68/1.00  
% 2.68/1.00  ------ Schedule dynamic 5 is on 
% 2.68/1.00  
% 2.68/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  ------ 
% 2.68/1.00  Current options:
% 2.68/1.00  ------ 
% 2.68/1.00  
% 2.68/1.00  ------ Input Options
% 2.68/1.00  
% 2.68/1.00  --out_options                           all
% 2.68/1.00  --tptp_safe_out                         true
% 2.68/1.00  --problem_path                          ""
% 2.68/1.00  --include_path                          ""
% 2.68/1.00  --clausifier                            res/vclausify_rel
% 2.68/1.00  --clausifier_options                    --mode clausify
% 2.68/1.00  --stdin                                 false
% 2.68/1.00  --stats_out                             all
% 2.68/1.00  
% 2.68/1.00  ------ General Options
% 2.68/1.00  
% 2.68/1.00  --fof                                   false
% 2.68/1.00  --time_out_real                         305.
% 2.68/1.00  --time_out_virtual                      -1.
% 2.68/1.00  --symbol_type_check                     false
% 2.68/1.00  --clausify_out                          false
% 2.68/1.00  --sig_cnt_out                           false
% 2.68/1.00  --trig_cnt_out                          false
% 2.68/1.00  --trig_cnt_out_tolerance                1.
% 2.68/1.00  --trig_cnt_out_sk_spl                   false
% 2.68/1.00  --abstr_cl_out                          false
% 2.68/1.00  
% 2.68/1.00  ------ Global Options
% 2.68/1.00  
% 2.68/1.00  --schedule                              default
% 2.68/1.00  --add_important_lit                     false
% 2.68/1.00  --prop_solver_per_cl                    1000
% 2.68/1.00  --min_unsat_core                        false
% 2.68/1.00  --soft_assumptions                      false
% 2.68/1.00  --soft_lemma_size                       3
% 2.68/1.00  --prop_impl_unit_size                   0
% 2.68/1.00  --prop_impl_unit                        []
% 2.68/1.00  --share_sel_clauses                     true
% 2.68/1.00  --reset_solvers                         false
% 2.68/1.00  --bc_imp_inh                            [conj_cone]
% 2.68/1.00  --conj_cone_tolerance                   3.
% 2.68/1.00  --extra_neg_conj                        none
% 2.68/1.00  --large_theory_mode                     true
% 2.68/1.00  --prolific_symb_bound                   200
% 2.68/1.00  --lt_threshold                          2000
% 2.68/1.00  --clause_weak_htbl                      true
% 2.68/1.00  --gc_record_bc_elim                     false
% 2.68/1.00  
% 2.68/1.00  ------ Preprocessing Options
% 2.68/1.00  
% 2.68/1.00  --preprocessing_flag                    true
% 2.68/1.00  --time_out_prep_mult                    0.1
% 2.68/1.00  --splitting_mode                        input
% 2.68/1.00  --splitting_grd                         true
% 2.68/1.00  --splitting_cvd                         false
% 2.68/1.00  --splitting_cvd_svl                     false
% 2.68/1.00  --splitting_nvd                         32
% 2.68/1.00  --sub_typing                            true
% 2.68/1.00  --prep_gs_sim                           true
% 2.68/1.00  --prep_unflatten                        true
% 2.68/1.00  --prep_res_sim                          true
% 2.68/1.00  --prep_upred                            true
% 2.68/1.00  --prep_sem_filter                       exhaustive
% 2.68/1.00  --prep_sem_filter_out                   false
% 2.68/1.00  --pred_elim                             true
% 2.68/1.00  --res_sim_input                         true
% 2.68/1.00  --eq_ax_congr_red                       true
% 2.68/1.00  --pure_diseq_elim                       true
% 2.68/1.00  --brand_transform                       false
% 2.68/1.00  --non_eq_to_eq                          false
% 2.68/1.00  --prep_def_merge                        true
% 2.68/1.00  --prep_def_merge_prop_impl              false
% 2.68/1.00  --prep_def_merge_mbd                    true
% 2.68/1.00  --prep_def_merge_tr_red                 false
% 2.68/1.00  --prep_def_merge_tr_cl                  false
% 2.68/1.00  --smt_preprocessing                     true
% 2.68/1.00  --smt_ac_axioms                         fast
% 2.68/1.00  --preprocessed_out                      false
% 2.68/1.00  --preprocessed_stats                    false
% 2.68/1.00  
% 2.68/1.00  ------ Abstraction refinement Options
% 2.68/1.00  
% 2.68/1.00  --abstr_ref                             []
% 2.68/1.00  --abstr_ref_prep                        false
% 2.68/1.00  --abstr_ref_until_sat                   false
% 2.68/1.00  --abstr_ref_sig_restrict                funpre
% 2.68/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.68/1.00  --abstr_ref_under                       []
% 2.68/1.00  
% 2.68/1.00  ------ SAT Options
% 2.68/1.00  
% 2.68/1.00  --sat_mode                              false
% 2.68/1.00  --sat_fm_restart_options                ""
% 2.68/1.00  --sat_gr_def                            false
% 2.68/1.00  --sat_epr_types                         true
% 2.68/1.00  --sat_non_cyclic_types                  false
% 2.68/1.00  --sat_finite_models                     false
% 2.68/1.00  --sat_fm_lemmas                         false
% 2.68/1.00  --sat_fm_prep                           false
% 2.68/1.00  --sat_fm_uc_incr                        true
% 2.68/1.00  --sat_out_model                         small
% 2.68/1.00  --sat_out_clauses                       false
% 2.68/1.00  
% 2.68/1.00  ------ QBF Options
% 2.68/1.00  
% 2.68/1.00  --qbf_mode                              false
% 2.68/1.00  --qbf_elim_univ                         false
% 2.68/1.00  --qbf_dom_inst                          none
% 2.68/1.00  --qbf_dom_pre_inst                      false
% 2.68/1.00  --qbf_sk_in                             false
% 2.68/1.00  --qbf_pred_elim                         true
% 2.68/1.00  --qbf_split                             512
% 2.68/1.00  
% 2.68/1.00  ------ BMC1 Options
% 2.68/1.00  
% 2.68/1.00  --bmc1_incremental                      false
% 2.68/1.00  --bmc1_axioms                           reachable_all
% 2.68/1.00  --bmc1_min_bound                        0
% 2.68/1.00  --bmc1_max_bound                        -1
% 2.68/1.00  --bmc1_max_bound_default                -1
% 2.68/1.00  --bmc1_symbol_reachability              true
% 2.68/1.00  --bmc1_property_lemmas                  false
% 2.68/1.00  --bmc1_k_induction                      false
% 2.68/1.00  --bmc1_non_equiv_states                 false
% 2.68/1.00  --bmc1_deadlock                         false
% 2.68/1.00  --bmc1_ucm                              false
% 2.68/1.00  --bmc1_add_unsat_core                   none
% 2.68/1.00  --bmc1_unsat_core_children              false
% 2.68/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.68/1.00  --bmc1_out_stat                         full
% 2.68/1.00  --bmc1_ground_init                      false
% 2.68/1.00  --bmc1_pre_inst_next_state              false
% 2.68/1.00  --bmc1_pre_inst_state                   false
% 2.68/1.00  --bmc1_pre_inst_reach_state             false
% 2.68/1.00  --bmc1_out_unsat_core                   false
% 2.68/1.00  --bmc1_aig_witness_out                  false
% 2.68/1.00  --bmc1_verbose                          false
% 2.68/1.00  --bmc1_dump_clauses_tptp                false
% 2.68/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.68/1.00  --bmc1_dump_file                        -
% 2.68/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.68/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.68/1.00  --bmc1_ucm_extend_mode                  1
% 2.68/1.00  --bmc1_ucm_init_mode                    2
% 2.68/1.00  --bmc1_ucm_cone_mode                    none
% 2.68/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.68/1.00  --bmc1_ucm_relax_model                  4
% 2.68/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.68/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.68/1.00  --bmc1_ucm_layered_model                none
% 2.68/1.00  --bmc1_ucm_max_lemma_size               10
% 2.68/1.00  
% 2.68/1.00  ------ AIG Options
% 2.68/1.00  
% 2.68/1.00  --aig_mode                              false
% 2.68/1.00  
% 2.68/1.00  ------ Instantiation Options
% 2.68/1.00  
% 2.68/1.00  --instantiation_flag                    true
% 2.68/1.00  --inst_sos_flag                         false
% 2.68/1.00  --inst_sos_phase                        true
% 2.68/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.68/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.68/1.00  --inst_lit_sel_side                     none
% 2.68/1.00  --inst_solver_per_active                1400
% 2.68/1.00  --inst_solver_calls_frac                1.
% 2.68/1.00  --inst_passive_queue_type               priority_queues
% 2.68/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.68/1.00  --inst_passive_queues_freq              [25;2]
% 2.68/1.00  --inst_dismatching                      true
% 2.68/1.00  --inst_eager_unprocessed_to_passive     true
% 2.68/1.00  --inst_prop_sim_given                   true
% 2.68/1.00  --inst_prop_sim_new                     false
% 2.68/1.00  --inst_subs_new                         false
% 2.68/1.00  --inst_eq_res_simp                      false
% 2.68/1.00  --inst_subs_given                       false
% 2.68/1.00  --inst_orphan_elimination               true
% 2.68/1.00  --inst_learning_loop_flag               true
% 2.68/1.00  --inst_learning_start                   3000
% 2.68/1.00  --inst_learning_factor                  2
% 2.68/1.00  --inst_start_prop_sim_after_learn       3
% 2.68/1.00  --inst_sel_renew                        solver
% 2.68/1.00  --inst_lit_activity_flag                true
% 2.68/1.00  --inst_restr_to_given                   false
% 2.68/1.00  --inst_activity_threshold               500
% 2.68/1.00  --inst_out_proof                        true
% 2.68/1.00  
% 2.68/1.00  ------ Resolution Options
% 2.68/1.00  
% 2.68/1.00  --resolution_flag                       false
% 2.68/1.00  --res_lit_sel                           adaptive
% 2.68/1.00  --res_lit_sel_side                      none
% 2.68/1.00  --res_ordering                          kbo
% 2.68/1.00  --res_to_prop_solver                    active
% 2.68/1.00  --res_prop_simpl_new                    false
% 2.68/1.00  --res_prop_simpl_given                  true
% 2.68/1.00  --res_passive_queue_type                priority_queues
% 2.68/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.68/1.00  --res_passive_queues_freq               [15;5]
% 2.68/1.00  --res_forward_subs                      full
% 2.68/1.00  --res_backward_subs                     full
% 2.68/1.00  --res_forward_subs_resolution           true
% 2.68/1.00  --res_backward_subs_resolution          true
% 2.68/1.00  --res_orphan_elimination                true
% 2.68/1.00  --res_time_limit                        2.
% 2.68/1.00  --res_out_proof                         true
% 2.68/1.00  
% 2.68/1.00  ------ Superposition Options
% 2.68/1.00  
% 2.68/1.00  --superposition_flag                    true
% 2.68/1.00  --sup_passive_queue_type                priority_queues
% 2.68/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.68/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.68/1.00  --demod_completeness_check              fast
% 2.68/1.00  --demod_use_ground                      true
% 2.68/1.00  --sup_to_prop_solver                    passive
% 2.68/1.00  --sup_prop_simpl_new                    true
% 2.68/1.00  --sup_prop_simpl_given                  true
% 2.68/1.00  --sup_fun_splitting                     false
% 2.68/1.00  --sup_smt_interval                      50000
% 2.68/1.00  
% 2.68/1.00  ------ Superposition Simplification Setup
% 2.68/1.00  
% 2.68/1.00  --sup_indices_passive                   []
% 2.68/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.68/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.68/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.00  --sup_full_bw                           [BwDemod]
% 2.68/1.00  --sup_immed_triv                        [TrivRules]
% 2.68/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.68/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.00  --sup_immed_bw_main                     []
% 2.68/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.68/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.68/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.68/1.00  
% 2.68/1.00  ------ Combination Options
% 2.68/1.00  
% 2.68/1.00  --comb_res_mult                         3
% 2.68/1.00  --comb_sup_mult                         2
% 2.68/1.00  --comb_inst_mult                        10
% 2.68/1.00  
% 2.68/1.00  ------ Debug Options
% 2.68/1.00  
% 2.68/1.00  --dbg_backtrace                         false
% 2.68/1.00  --dbg_dump_prop_clauses                 false
% 2.68/1.00  --dbg_dump_prop_clauses_file            -
% 2.68/1.00  --dbg_out_stat                          false
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  ------ Proving...
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  % SZS status Theorem for theBenchmark.p
% 2.68/1.00  
% 2.68/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.68/1.00  
% 2.68/1.00  fof(f1,axiom,(
% 2.68/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f17,plain,(
% 2.68/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.68/1.00    inference(ennf_transformation,[],[f1])).
% 2.68/1.00  
% 2.68/1.00  fof(f27,plain,(
% 2.68/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.68/1.00    inference(nnf_transformation,[],[f17])).
% 2.68/1.00  
% 2.68/1.00  fof(f28,plain,(
% 2.68/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.68/1.00    inference(rectify,[],[f27])).
% 2.68/1.00  
% 2.68/1.00  fof(f29,plain,(
% 2.68/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.68/1.00    introduced(choice_axiom,[])).
% 2.68/1.00  
% 2.68/1.00  fof(f30,plain,(
% 2.68/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.68/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 2.68/1.00  
% 2.68/1.00  fof(f51,plain,(
% 2.68/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.68/1.00    inference(cnf_transformation,[],[f30])).
% 2.68/1.00  
% 2.68/1.00  fof(f4,axiom,(
% 2.68/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f36,plain,(
% 2.68/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.68/1.00    inference(nnf_transformation,[],[f4])).
% 2.68/1.00  
% 2.68/1.00  fof(f37,plain,(
% 2.68/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.68/1.00    inference(rectify,[],[f36])).
% 2.68/1.00  
% 2.68/1.00  fof(f38,plain,(
% 2.68/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 2.68/1.00    introduced(choice_axiom,[])).
% 2.68/1.00  
% 2.68/1.00  fof(f39,plain,(
% 2.68/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.68/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 2.68/1.00  
% 2.68/1.00  fof(f58,plain,(
% 2.68/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.68/1.00    inference(cnf_transformation,[],[f39])).
% 2.68/1.00  
% 2.68/1.00  fof(f9,axiom,(
% 2.68/1.00    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 2.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f67,plain,(
% 2.68/1.00    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 2.68/1.00    inference(cnf_transformation,[],[f9])).
% 2.68/1.00  
% 2.68/1.00  fof(f88,plain,(
% 2.68/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k9_setfam_1(X0) != X1) )),
% 2.68/1.00    inference(definition_unfolding,[],[f58,f67])).
% 2.68/1.00  
% 2.68/1.00  fof(f107,plain,(
% 2.68/1.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k9_setfam_1(X0))) )),
% 2.68/1.00    inference(equality_resolution,[],[f88])).
% 2.68/1.00  
% 2.68/1.00  fof(f5,axiom,(
% 2.68/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f62,plain,(
% 2.68/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.68/1.00    inference(cnf_transformation,[],[f5])).
% 2.68/1.00  
% 2.68/1.00  fof(f89,plain,(
% 2.68/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k9_setfam_1(X0))) )),
% 2.68/1.00    inference(definition_unfolding,[],[f62,f67])).
% 2.68/1.00  
% 2.68/1.00  fof(f6,axiom,(
% 2.68/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f40,plain,(
% 2.68/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.68/1.00    inference(nnf_transformation,[],[f6])).
% 2.68/1.00  
% 2.68/1.00  fof(f63,plain,(
% 2.68/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.68/1.00    inference(cnf_transformation,[],[f40])).
% 2.68/1.00  
% 2.68/1.00  fof(f91,plain,(
% 2.68/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k9_setfam_1(X1))) )),
% 2.68/1.00    inference(definition_unfolding,[],[f63,f67])).
% 2.68/1.00  
% 2.68/1.00  fof(f14,conjecture,(
% 2.68/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 2.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f15,negated_conjecture,(
% 2.68/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 2.68/1.00    inference(negated_conjecture,[],[f14])).
% 2.68/1.00  
% 2.68/1.00  fof(f16,plain,(
% 2.68/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 2.68/1.00    inference(pure_predicate_removal,[],[f15])).
% 2.68/1.00  
% 2.68/1.00  fof(f25,plain,(
% 2.68/1.00    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 2.68/1.00    inference(ennf_transformation,[],[f16])).
% 2.68/1.00  
% 2.68/1.00  fof(f26,plain,(
% 2.68/1.00    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.68/1.00    inference(flattening,[],[f25])).
% 2.68/1.00  
% 2.68/1.00  fof(f48,plain,(
% 2.68/1.00    ( ! [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) => (v1_xboole_0(sK7) & r2_hidden(sK7,X1))) )),
% 2.68/1.00    introduced(choice_axiom,[])).
% 2.68/1.00  
% 2.68/1.00  fof(f47,plain,(
% 2.68/1.00    ( ! [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(sK6,k3_yellow_1(X0)) & v1_subset_1(sK6,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(sK6))) )),
% 2.68/1.00    introduced(choice_axiom,[])).
% 2.68/1.00  
% 2.68/1.00  fof(f46,plain,(
% 2.68/1.00    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK5)))) & v13_waybel_0(X1,k3_yellow_1(sK5)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(sK5))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK5))),
% 2.68/1.00    introduced(choice_axiom,[])).
% 2.68/1.00  
% 2.68/1.00  fof(f49,plain,(
% 2.68/1.00    ((v1_xboole_0(sK7) & r2_hidden(sK7,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK5)))) & v13_waybel_0(sK6,k3_yellow_1(sK5)) & v1_subset_1(sK6,u1_struct_0(k3_yellow_1(sK5))) & ~v1_xboole_0(sK6)) & ~v1_xboole_0(sK5)),
% 2.68/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f26,f48,f47,f46])).
% 2.68/1.00  
% 2.68/1.00  fof(f81,plain,(
% 2.68/1.00    v13_waybel_0(sK6,k3_yellow_1(sK5))),
% 2.68/1.00    inference(cnf_transformation,[],[f49])).
% 2.68/1.00  
% 2.68/1.00  fof(f11,axiom,(
% 2.68/1.00    ! [X0] : k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0)),
% 2.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f70,plain,(
% 2.68/1.00    ( ! [X0] : (k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0)) )),
% 2.68/1.00    inference(cnf_transformation,[],[f11])).
% 2.68/1.00  
% 2.68/1.00  fof(f102,plain,(
% 2.68/1.00    v13_waybel_0(sK6,k2_yellow_1(k9_setfam_1(sK5)))),
% 2.68/1.00    inference(definition_unfolding,[],[f81,f70])).
% 2.68/1.00  
% 2.68/1.00  fof(f13,axiom,(
% 2.68/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) => (v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : ((r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => r2_hidden(X3,X1))))),
% 2.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f23,plain,(
% 2.68/1.00    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | (~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 2.68/1.00    inference(ennf_transformation,[],[f13])).
% 2.68/1.00  
% 2.68/1.00  fof(f24,plain,(
% 2.68/1.00    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 2.68/1.00    inference(flattening,[],[f23])).
% 2.68/1.00  
% 2.68/1.00  fof(f42,plain,(
% 2.68/1.00    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 2.68/1.00    inference(nnf_transformation,[],[f24])).
% 2.68/1.00  
% 2.68/1.00  fof(f43,plain,(
% 2.68/1.00    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 2.68/1.00    inference(rectify,[],[f42])).
% 2.68/1.00  
% 2.68/1.00  fof(f44,plain,(
% 2.68/1.00    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK3(X0,X1),X1) & r1_tarski(sK4(X0,X1),X0) & r1_tarski(sK3(X0,X1),sK4(X0,X1))))),
% 2.68/1.00    introduced(choice_axiom,[])).
% 2.68/1.00  
% 2.68/1.00  fof(f45,plain,(
% 2.68/1.00    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK3(X0,X1),X1) & r1_tarski(sK4(X0,X1),X0) & r1_tarski(sK3(X0,X1),sK4(X0,X1)))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 2.68/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f43,f44])).
% 2.68/1.00  
% 2.68/1.00  fof(f73,plain,(
% 2.68/1.00    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))) )),
% 2.68/1.00    inference(cnf_transformation,[],[f45])).
% 2.68/1.00  
% 2.68/1.00  fof(f100,plain,(
% 2.68/1.00    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0))) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))))) )),
% 2.68/1.00    inference(definition_unfolding,[],[f73,f70,f67,f70])).
% 2.68/1.00  
% 2.68/1.00  fof(f10,axiom,(
% 2.68/1.00    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 2.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f68,plain,(
% 2.68/1.00    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 2.68/1.00    inference(cnf_transformation,[],[f10])).
% 2.68/1.00  
% 2.68/1.00  fof(f82,plain,(
% 2.68/1.00    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK5))))),
% 2.68/1.00    inference(cnf_transformation,[],[f49])).
% 2.68/1.00  
% 2.68/1.00  fof(f101,plain,(
% 2.68/1.00    m1_subset_1(sK6,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))))),
% 2.68/1.00    inference(definition_unfolding,[],[f82,f67,f70])).
% 2.68/1.00  
% 2.68/1.00  fof(f83,plain,(
% 2.68/1.00    r2_hidden(sK7,sK6)),
% 2.68/1.00    inference(cnf_transformation,[],[f49])).
% 2.68/1.00  
% 2.68/1.00  fof(f3,axiom,(
% 2.68/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f34,plain,(
% 2.68/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.68/1.00    inference(nnf_transformation,[],[f3])).
% 2.68/1.00  
% 2.68/1.00  fof(f35,plain,(
% 2.68/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.68/1.00    inference(flattening,[],[f34])).
% 2.68/1.00  
% 2.68/1.00  fof(f55,plain,(
% 2.68/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.68/1.00    inference(cnf_transformation,[],[f35])).
% 2.68/1.00  
% 2.68/1.00  fof(f105,plain,(
% 2.68/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.68/1.00    inference(equality_resolution,[],[f55])).
% 2.68/1.00  
% 2.68/1.00  fof(f84,plain,(
% 2.68/1.00    v1_xboole_0(sK7)),
% 2.68/1.00    inference(cnf_transformation,[],[f49])).
% 2.68/1.00  
% 2.68/1.00  fof(f8,axiom,(
% 2.68/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f21,plain,(
% 2.68/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.68/1.00    inference(ennf_transformation,[],[f8])).
% 2.68/1.00  
% 2.68/1.00  fof(f66,plain,(
% 2.68/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.68/1.00    inference(cnf_transformation,[],[f21])).
% 2.68/1.00  
% 2.68/1.00  fof(f93,plain,(
% 2.68/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k9_setfam_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.68/1.00    inference(definition_unfolding,[],[f66,f67])).
% 2.68/1.00  
% 2.68/1.00  fof(f64,plain,(
% 2.68/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.68/1.00    inference(cnf_transformation,[],[f40])).
% 2.68/1.00  
% 2.68/1.00  fof(f90,plain,(
% 2.68/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k9_setfam_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.68/1.00    inference(definition_unfolding,[],[f64,f67])).
% 2.68/1.00  
% 2.68/1.00  fof(f52,plain,(
% 2.68/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.68/1.00    inference(cnf_transformation,[],[f30])).
% 2.68/1.00  
% 2.68/1.00  fof(f57,plain,(
% 2.68/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.68/1.00    inference(cnf_transformation,[],[f35])).
% 2.68/1.00  
% 2.68/1.00  fof(f12,axiom,(
% 2.68/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.68/1.00  
% 2.68/1.00  fof(f22,plain,(
% 2.68/1.00    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.68/1.00    inference(ennf_transformation,[],[f12])).
% 2.68/1.00  
% 2.68/1.00  fof(f41,plain,(
% 2.68/1.00    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.68/1.00    inference(nnf_transformation,[],[f22])).
% 2.68/1.00  
% 2.68/1.00  fof(f71,plain,(
% 2.68/1.00    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.68/1.00    inference(cnf_transformation,[],[f41])).
% 2.68/1.00  
% 2.68/1.00  fof(f95,plain,(
% 2.68/1.00    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(X0))) )),
% 2.68/1.00    inference(definition_unfolding,[],[f71,f67])).
% 2.68/1.00  
% 2.68/1.00  fof(f108,plain,(
% 2.68/1.00    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k9_setfam_1(X1))) )),
% 2.68/1.00    inference(equality_resolution,[],[f95])).
% 2.68/1.00  
% 2.68/1.00  fof(f80,plain,(
% 2.68/1.00    v1_subset_1(sK6,u1_struct_0(k3_yellow_1(sK5)))),
% 2.68/1.00    inference(cnf_transformation,[],[f49])).
% 2.68/1.00  
% 2.68/1.00  fof(f103,plain,(
% 2.68/1.00    v1_subset_1(sK6,u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))))),
% 2.68/1.00    inference(definition_unfolding,[],[f80,f70])).
% 2.68/1.00  
% 2.68/1.00  cnf(c_940,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_4093,plain,
% 2.68/1.00      ( X0 != X1
% 2.68/1.00      | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != X1
% 2.68/1.00      | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) = X0 ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_940]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_23666,plain,
% 2.68/1.00      ( X0 != k9_setfam_1(sK5)
% 2.68/1.00      | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) = X0
% 2.68/1.00      | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != k9_setfam_1(sK5) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_4093]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_23667,plain,
% 2.68/1.00      ( u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != k9_setfam_1(sK5)
% 2.68/1.00      | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) = sK6
% 2.68/1.00      | sK6 != k9_setfam_1(sK5) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_23666]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1894,plain,
% 2.68/1.00      ( u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != X0
% 2.68/1.00      | sK6 != X0
% 2.68/1.00      | sK6 = u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_940]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_14891,plain,
% 2.68/1.00      ( u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != k9_setfam_1(sK5)
% 2.68/1.00      | sK6 = u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))
% 2.68/1.00      | sK6 != k9_setfam_1(sK5) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_1894]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1,plain,
% 2.68/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.68/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1547,plain,
% 2.68/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.68/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_11,plain,
% 2.68/1.00      ( ~ r2_hidden(X0,k9_setfam_1(X1)) | r1_tarski(X0,X1) ),
% 2.68/1.00      inference(cnf_transformation,[],[f107]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1538,plain,
% 2.68/1.00      ( r2_hidden(X0,k9_setfam_1(X1)) != iProver_top
% 2.68/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2831,plain,
% 2.68/1.00      ( r1_tarski(sK0(k9_setfam_1(X0),X1),X0) = iProver_top
% 2.68/1.00      | r1_tarski(k9_setfam_1(X0),X1) = iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_1547,c_1538]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_12,plain,
% 2.68/1.00      ( m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) ),
% 2.68/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1537,plain,
% 2.68/1.00      ( m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_14,plain,
% 2.68/1.00      ( ~ m1_subset_1(X0,k9_setfam_1(X1)) | r1_tarski(X0,X1) ),
% 2.68/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1535,plain,
% 2.68/1.00      ( m1_subset_1(X0,k9_setfam_1(X1)) != iProver_top
% 2.68/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2188,plain,
% 2.68/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_1537,c_1535]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_28,negated_conjecture,
% 2.68/1.00      ( v13_waybel_0(sK6,k2_yellow_1(k9_setfam_1(sK5))) ),
% 2.68/1.00      inference(cnf_transformation,[],[f102]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1526,plain,
% 2.68/1.00      ( v13_waybel_0(sK6,k2_yellow_1(k9_setfam_1(sK5))) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_24,plain,
% 2.68/1.00      ( ~ v13_waybel_0(X0,k2_yellow_1(k9_setfam_1(X1)))
% 2.68/1.00      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X1)))))
% 2.68/1.00      | ~ r2_hidden(X2,X0)
% 2.68/1.00      | r2_hidden(X3,X0)
% 2.68/1.00      | ~ r1_tarski(X3,X1)
% 2.68/1.00      | ~ r1_tarski(X2,X3) ),
% 2.68/1.00      inference(cnf_transformation,[],[f100]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1529,plain,
% 2.68/1.00      ( v13_waybel_0(X0,k2_yellow_1(k9_setfam_1(X1))) != iProver_top
% 2.68/1.00      | m1_subset_1(X0,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X1))))) != iProver_top
% 2.68/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.68/1.00      | r2_hidden(X3,X0) = iProver_top
% 2.68/1.00      | r1_tarski(X3,X1) != iProver_top
% 2.68/1.00      | r1_tarski(X2,X3) != iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_17,plain,
% 2.68/1.00      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 2.68/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1669,plain,
% 2.68/1.00      ( v13_waybel_0(X0,k2_yellow_1(k9_setfam_1(X1))) != iProver_top
% 2.68/1.00      | m1_subset_1(X0,k9_setfam_1(k9_setfam_1(X1))) != iProver_top
% 2.68/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.68/1.00      | r2_hidden(X3,X0) = iProver_top
% 2.68/1.00      | r1_tarski(X3,X1) != iProver_top
% 2.68/1.00      | r1_tarski(X2,X3) != iProver_top ),
% 2.68/1.00      inference(demodulation,[status(thm)],[c_1529,c_17]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_4857,plain,
% 2.68/1.00      ( m1_subset_1(sK6,k9_setfam_1(k9_setfam_1(sK5))) != iProver_top
% 2.68/1.00      | r2_hidden(X0,sK6) != iProver_top
% 2.68/1.00      | r2_hidden(X1,sK6) = iProver_top
% 2.68/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.68/1.00      | r1_tarski(X1,sK5) != iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_1526,c_1669]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_27,negated_conjecture,
% 2.68/1.00      ( m1_subset_1(sK6,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))))) ),
% 2.68/1.00      inference(cnf_transformation,[],[f101]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1527,plain,
% 2.68/1.00      ( m1_subset_1(sK6,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))))) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1563,plain,
% 2.68/1.00      ( m1_subset_1(sK6,k9_setfam_1(k9_setfam_1(sK5))) = iProver_top ),
% 2.68/1.00      inference(demodulation,[status(thm)],[c_1527,c_17]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_4988,plain,
% 2.68/1.00      ( r2_hidden(X0,sK6) != iProver_top
% 2.68/1.00      | r2_hidden(X1,sK6) = iProver_top
% 2.68/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.68/1.00      | r1_tarski(X1,sK5) != iProver_top ),
% 2.68/1.00      inference(global_propositional_subsumption,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_4857,c_1563]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_5000,plain,
% 2.68/1.00      ( r2_hidden(X0,sK6) = iProver_top
% 2.68/1.00      | r2_hidden(k1_xboole_0,sK6) != iProver_top
% 2.68/1.00      | r1_tarski(X0,sK5) != iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_2188,c_4988]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_26,negated_conjecture,
% 2.68/1.00      ( r2_hidden(sK7,sK6) ),
% 2.68/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_37,plain,
% 2.68/1.00      ( r2_hidden(sK7,sK6) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_7,plain,
% 2.68/1.00      ( r1_tarski(X0,X0) ),
% 2.68/1.00      inference(cnf_transformation,[],[f105]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1542,plain,
% 2.68/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_25,negated_conjecture,
% 2.68/1.00      ( v1_xboole_0(sK7) ),
% 2.68/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_16,plain,
% 2.68/1.00      ( ~ m1_subset_1(X0,k9_setfam_1(X1))
% 2.68/1.00      | ~ r2_hidden(X2,X0)
% 2.68/1.00      | ~ v1_xboole_0(X1) ),
% 2.68/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_13,plain,
% 2.68/1.00      ( m1_subset_1(X0,k9_setfam_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.68/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_236,plain,
% 2.68/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k9_setfam_1(X1)) ),
% 2.68/1.00      inference(prop_impl,[status(thm)],[c_13]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_237,plain,
% 2.68/1.00      ( m1_subset_1(X0,k9_setfam_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.68/1.00      inference(renaming,[status(thm)],[c_236]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_293,plain,
% 2.68/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.68/1.00      inference(bin_hyper_res,[status(thm)],[c_16,c_237]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_407,plain,
% 2.68/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | sK7 != X2 ),
% 2.68/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_293]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_408,plain,
% 2.68/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,sK7) ),
% 2.68/1.00      inference(unflattening,[status(thm)],[c_407]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1525,plain,
% 2.68/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.68/1.00      | r1_tarski(X1,sK7) != iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2830,plain,
% 2.68/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.68/1.00      | r1_tarski(X0,sK7) != iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_1547,c_1525]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_3434,plain,
% 2.68/1.00      ( r1_tarski(sK7,X0) = iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_1542,c_2830]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_5002,plain,
% 2.68/1.00      ( r2_hidden(X0,sK6) = iProver_top
% 2.68/1.00      | r2_hidden(sK7,sK6) != iProver_top
% 2.68/1.00      | r1_tarski(X0,sK5) != iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_3434,c_4988]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_5153,plain,
% 2.68/1.00      ( r2_hidden(X0,sK6) = iProver_top
% 2.68/1.00      | r1_tarski(X0,sK5) != iProver_top ),
% 2.68/1.00      inference(global_propositional_subsumption,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_5000,c_37,c_5002]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_8449,plain,
% 2.68/1.00      ( r2_hidden(sK0(k9_setfam_1(sK5),X0),sK6) = iProver_top
% 2.68/1.00      | r1_tarski(k9_setfam_1(sK5),X0) = iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_2831,c_5153]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_0,plain,
% 2.68/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.68/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1548,plain,
% 2.68/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.68/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_9649,plain,
% 2.68/1.00      ( r1_tarski(k9_setfam_1(sK5),sK6) = iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_8449,c_1548]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_943,plain,
% 2.68/1.00      ( X0 != X1 | k9_setfam_1(X0) = k9_setfam_1(X1) ),
% 2.68/1.00      theory(equality) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_7631,plain,
% 2.68/1.00      ( u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != X0
% 2.68/1.00      | k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))) = k9_setfam_1(X0) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_943]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_7632,plain,
% 2.68/1.00      ( u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != sK6
% 2.68/1.00      | k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))) = k9_setfam_1(sK6) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_7631]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_944,plain,
% 2.68/1.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.68/1.00      theory(equality) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_1862,plain,
% 2.68/1.00      ( m1_subset_1(X0,X1)
% 2.68/1.00      | ~ m1_subset_1(X2,k9_setfam_1(X3))
% 2.68/1.00      | X0 != X2
% 2.68/1.00      | X1 != k9_setfam_1(X3) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_944]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_7004,plain,
% 2.68/1.00      ( ~ m1_subset_1(X0,k9_setfam_1(X1))
% 2.68/1.00      | m1_subset_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))),k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))))
% 2.68/1.00      | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != X0
% 2.68/1.00      | k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))) != k9_setfam_1(X1) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_1862]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_7006,plain,
% 2.68/1.00      ( m1_subset_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))),k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))))
% 2.68/1.00      | ~ m1_subset_1(sK6,k9_setfam_1(sK6))
% 2.68/1.00      | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != sK6
% 2.68/1.00      | k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))) != k9_setfam_1(sK6) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_7004]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2644,plain,
% 2.68/1.00      ( u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) = k9_setfam_1(sK5) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_5,plain,
% 2.68/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.68/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2616,plain,
% 2.68/1.00      ( ~ r1_tarski(X0,k9_setfam_1(sK5))
% 2.68/1.00      | ~ r1_tarski(k9_setfam_1(sK5),X0)
% 2.68/1.00      | X0 = k9_setfam_1(sK5) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2627,plain,
% 2.68/1.00      ( X0 = k9_setfam_1(sK5)
% 2.68/1.00      | r1_tarski(X0,k9_setfam_1(sK5)) != iProver_top
% 2.68/1.00      | r1_tarski(k9_setfam_1(sK5),X0) != iProver_top ),
% 2.68/1.00      inference(predicate_to_equality,[status(thm)],[c_2616]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2629,plain,
% 2.68/1.00      ( sK6 = k9_setfam_1(sK5)
% 2.68/1.00      | r1_tarski(k9_setfam_1(sK5),sK6) != iProver_top
% 2.68/1.00      | r1_tarski(sK6,k9_setfam_1(sK5)) != iProver_top ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_2627]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_2189,plain,
% 2.68/1.00      ( r1_tarski(sK6,k9_setfam_1(sK5)) = iProver_top ),
% 2.68/1.00      inference(superposition,[status(thm)],[c_1563,c_1535]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_19,plain,
% 2.68/1.00      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k9_setfam_1(X0)) ),
% 2.68/1.00      inference(cnf_transformation,[],[f108]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_29,negated_conjecture,
% 2.68/1.00      ( v1_subset_1(sK6,u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))) ),
% 2.68/1.00      inference(cnf_transformation,[],[f103]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_426,plain,
% 2.68/1.00      ( ~ m1_subset_1(X0,k9_setfam_1(X0))
% 2.68/1.00      | u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) != X0
% 2.68/1.00      | sK6 != X0 ),
% 2.68/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_427,plain,
% 2.68/1.00      ( ~ m1_subset_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))),k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK5)))))
% 2.68/1.00      | sK6 != u1_struct_0(k2_yellow_1(k9_setfam_1(sK5))) ),
% 2.68/1.00      inference(unflattening,[status(thm)],[c_426]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_85,plain,
% 2.68/1.00      ( r1_tarski(sK6,sK6) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(c_67,plain,
% 2.68/1.00      ( m1_subset_1(sK6,k9_setfam_1(sK6)) | ~ r1_tarski(sK6,sK6) ),
% 2.68/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 2.68/1.00  
% 2.68/1.00  cnf(contradiction,plain,
% 2.68/1.00      ( $false ),
% 2.68/1.00      inference(minisat,
% 2.68/1.00                [status(thm)],
% 2.68/1.00                [c_23667,c_14891,c_9649,c_7632,c_7006,c_2644,c_2629,
% 2.68/1.00                 c_2189,c_427,c_85,c_67]) ).
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.68/1.00  
% 2.68/1.00  ------                               Statistics
% 2.68/1.00  
% 2.68/1.00  ------ General
% 2.68/1.00  
% 2.68/1.00  abstr_ref_over_cycles:                  0
% 2.68/1.00  abstr_ref_under_cycles:                 0
% 2.68/1.00  gc_basic_clause_elim:                   0
% 2.68/1.00  forced_gc_time:                         0
% 2.68/1.00  parsing_time:                           0.008
% 2.68/1.00  unif_index_cands_time:                  0.
% 2.68/1.00  unif_index_add_time:                    0.
% 2.68/1.00  orderings_time:                         0.
% 2.68/1.00  out_proof_time:                         0.014
% 2.68/1.00  total_time:                             0.49
% 2.68/1.00  num_of_symbols:                         49
% 2.68/1.00  num_of_terms:                           16459
% 2.68/1.00  
% 2.68/1.00  ------ Preprocessing
% 2.68/1.00  
% 2.68/1.00  num_of_splits:                          0
% 2.68/1.00  num_of_split_atoms:                     0
% 2.68/1.00  num_of_reused_defs:                     0
% 2.68/1.00  num_eq_ax_congr_red:                    30
% 2.68/1.00  num_of_sem_filtered_clauses:            1
% 2.68/1.00  num_of_subtypes:                        0
% 2.68/1.00  monotx_restored_types:                  0
% 2.68/1.00  sat_num_of_epr_types:                   0
% 2.68/1.00  sat_num_of_non_cyclic_types:            0
% 2.68/1.00  sat_guarded_non_collapsed_types:        0
% 2.68/1.00  num_pure_diseq_elim:                    0
% 2.68/1.00  simp_replaced_by:                       0
% 2.68/1.00  res_preprocessed:                       134
% 2.68/1.00  prep_upred:                             0
% 2.68/1.00  prep_unflattend:                        6
% 2.68/1.00  smt_new_axioms:                         0
% 2.68/1.00  pred_elim_cands:                        4
% 2.68/1.00  pred_elim:                              2
% 2.68/1.00  pred_elim_cl:                           3
% 2.68/1.00  pred_elim_cycles:                       4
% 2.68/1.00  merged_defs:                            16
% 2.68/1.00  merged_defs_ncl:                        0
% 2.68/1.00  bin_hyper_res:                          18
% 2.68/1.00  prep_cycles:                            4
% 2.68/1.00  pred_elim_time:                         0.009
% 2.68/1.00  splitting_time:                         0.
% 2.68/1.00  sem_filter_time:                        0.
% 2.68/1.00  monotx_time:                            0.001
% 2.68/1.00  subtype_inf_time:                       0.
% 2.68/1.00  
% 2.68/1.00  ------ Problem properties
% 2.68/1.00  
% 2.68/1.00  clauses:                                28
% 2.68/1.00  conjectures:                            3
% 2.68/1.00  epr:                                    7
% 2.68/1.00  horn:                                   22
% 2.68/1.00  ground:                                 6
% 2.68/1.00  unary:                                  8
% 2.68/1.00  binary:                                 8
% 2.68/1.00  lits:                                   63
% 2.68/1.00  lits_eq:                                9
% 2.68/1.00  fd_pure:                                0
% 2.68/1.00  fd_pseudo:                              0
% 2.68/1.00  fd_cond:                                0
% 2.68/1.00  fd_pseudo_cond:                         5
% 2.68/1.00  ac_symbols:                             0
% 2.68/1.00  
% 2.68/1.00  ------ Propositional Solver
% 2.68/1.00  
% 2.68/1.00  prop_solver_calls:                      27
% 2.68/1.00  prop_fast_solver_calls:                 1154
% 2.68/1.00  smt_solver_calls:                       0
% 2.68/1.00  smt_fast_solver_calls:                  0
% 2.68/1.00  prop_num_of_clauses:                    7971
% 2.68/1.00  prop_preprocess_simplified:             16334
% 2.68/1.00  prop_fo_subsumed:                       24
% 2.68/1.00  prop_solver_time:                       0.
% 2.68/1.00  smt_solver_time:                        0.
% 2.68/1.00  smt_fast_solver_time:                   0.
% 2.68/1.00  prop_fast_solver_time:                  0.
% 2.68/1.00  prop_unsat_core_time:                   0.
% 2.68/1.00  
% 2.68/1.00  ------ QBF
% 2.68/1.00  
% 2.68/1.00  qbf_q_res:                              0
% 2.68/1.00  qbf_num_tautologies:                    0
% 2.68/1.00  qbf_prep_cycles:                        0
% 2.68/1.00  
% 2.68/1.00  ------ BMC1
% 2.68/1.00  
% 2.68/1.00  bmc1_current_bound:                     -1
% 2.68/1.00  bmc1_last_solved_bound:                 -1
% 2.68/1.00  bmc1_unsat_core_size:                   -1
% 2.68/1.00  bmc1_unsat_core_parents_size:           -1
% 2.68/1.00  bmc1_merge_next_fun:                    0
% 2.68/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.68/1.00  
% 2.68/1.00  ------ Instantiation
% 2.68/1.00  
% 2.68/1.00  inst_num_of_clauses:                    2022
% 2.68/1.00  inst_num_in_passive:                    744
% 2.68/1.00  inst_num_in_active:                     626
% 2.68/1.00  inst_num_in_unprocessed:                651
% 2.68/1.00  inst_num_of_loops:                      851
% 2.68/1.00  inst_num_of_learning_restarts:          0
% 2.68/1.00  inst_num_moves_active_passive:          223
% 2.68/1.00  inst_lit_activity:                      0
% 2.68/1.00  inst_lit_activity_moves:                0
% 2.68/1.00  inst_num_tautologies:                   0
% 2.68/1.00  inst_num_prop_implied:                  0
% 2.68/1.00  inst_num_existing_simplified:           0
% 2.68/1.00  inst_num_eq_res_simplified:             0
% 2.68/1.00  inst_num_child_elim:                    0
% 2.68/1.00  inst_num_of_dismatching_blockings:      1517
% 2.68/1.00  inst_num_of_non_proper_insts:           2013
% 2.68/1.00  inst_num_of_duplicates:                 0
% 2.68/1.00  inst_inst_num_from_inst_to_res:         0
% 2.68/1.00  inst_dismatching_checking_time:         0.
% 2.68/1.00  
% 2.68/1.00  ------ Resolution
% 2.68/1.00  
% 2.68/1.00  res_num_of_clauses:                     0
% 2.68/1.00  res_num_in_passive:                     0
% 2.68/1.00  res_num_in_active:                      0
% 2.68/1.00  res_num_of_loops:                       138
% 2.68/1.00  res_forward_subset_subsumed:            185
% 2.68/1.00  res_backward_subset_subsumed:           0
% 2.68/1.00  res_forward_subsumed:                   0
% 2.68/1.00  res_backward_subsumed:                  0
% 2.68/1.00  res_forward_subsumption_resolution:     0
% 2.68/1.00  res_backward_subsumption_resolution:    0
% 2.68/1.00  res_clause_to_clause_subsumption:       3480
% 2.68/1.00  res_orphan_elimination:                 0
% 2.68/1.00  res_tautology_del:                      166
% 2.68/1.00  res_num_eq_res_simplified:              0
% 2.68/1.00  res_num_sel_changes:                    0
% 2.68/1.00  res_moves_from_active_to_pass:          0
% 2.68/1.00  
% 2.68/1.00  ------ Superposition
% 2.68/1.00  
% 2.68/1.00  sup_time_total:                         0.
% 2.68/1.00  sup_time_generating:                    0.
% 2.68/1.00  sup_time_sim_full:                      0.
% 2.68/1.00  sup_time_sim_immed:                     0.
% 2.68/1.00  
% 2.68/1.00  sup_num_of_clauses:                     759
% 2.68/1.00  sup_num_in_active:                      163
% 2.68/1.00  sup_num_in_passive:                     596
% 2.68/1.00  sup_num_of_loops:                       170
% 2.68/1.00  sup_fw_superposition:                   755
% 2.68/1.00  sup_bw_superposition:                   585
% 2.68/1.00  sup_immediate_simplified:               175
% 2.68/1.00  sup_given_eliminated:                   5
% 2.68/1.00  comparisons_done:                       0
% 2.68/1.00  comparisons_avoided:                    33
% 2.68/1.00  
% 2.68/1.00  ------ Simplifications
% 2.68/1.00  
% 2.68/1.00  
% 2.68/1.00  sim_fw_subset_subsumed:                 61
% 2.68/1.00  sim_bw_subset_subsumed:                 9
% 2.68/1.00  sim_fw_subsumed:                        82
% 2.68/1.00  sim_bw_subsumed:                        0
% 2.68/1.00  sim_fw_subsumption_res:                 10
% 2.68/1.00  sim_bw_subsumption_res:                 0
% 2.68/1.00  sim_tautology_del:                      6
% 2.68/1.00  sim_eq_tautology_del:                   45
% 2.68/1.00  sim_eq_res_simp:                        2
% 2.68/1.00  sim_fw_demodulated:                     7
% 2.68/1.00  sim_bw_demodulated:                     46
% 2.68/1.00  sim_light_normalised:                   6
% 2.68/1.00  sim_joinable_taut:                      0
% 2.68/1.00  sim_joinable_simp:                      0
% 2.68/1.00  sim_ac_normalised:                      0
% 2.68/1.00  sim_smt_subsumption:                    0
% 2.68/1.00  
%------------------------------------------------------------------------------
