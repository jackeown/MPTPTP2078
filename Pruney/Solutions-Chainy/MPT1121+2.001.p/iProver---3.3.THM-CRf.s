%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:37 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  168 (2206 expanded)
%              Number of clauses        :  105 ( 624 expanded)
%              Number of leaves         :   15 ( 529 expanded)
%              Depth                    :   25
%              Number of atoms          :  739 (12832 expanded)
%              Number of equality atoms :  180 (2991 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( ( k2_pre_topc(X0,X1) = X1
                  & v2_pre_topc(X0) )
               => v4_pre_topc(X1,X0) )
              & ( v4_pre_topc(X1,X0)
               => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,X0)
              & k2_pre_topc(X0,X1) = X1
              & v2_pre_topc(X0) )
            | ( k2_pre_topc(X0,X1) != X1
              & v4_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,X0)
              & k2_pre_topc(X0,X1) = X1
              & v2_pre_topc(X0) )
            | ( k2_pre_topc(X0,X1) != X1
              & v4_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,X0)
              & k2_pre_topc(X0,X1) = X1
              & v2_pre_topc(X0) )
            | ( k2_pre_topc(X0,X1) != X1
              & v4_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( ~ v4_pre_topc(sK5,X0)
            & k2_pre_topc(X0,sK5) = sK5
            & v2_pre_topc(X0) )
          | ( k2_pre_topc(X0,sK5) != sK5
            & v4_pre_topc(sK5,X0) ) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( ~ v4_pre_topc(X1,X0)
                & k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
              | ( k2_pre_topc(X0,X1) != X1
                & v4_pre_topc(X1,X0) ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ( ~ v4_pre_topc(X1,sK4)
              & k2_pre_topc(sK4,X1) = X1
              & v2_pre_topc(sK4) )
            | ( k2_pre_topc(sK4,X1) != X1
              & v4_pre_topc(X1,sK4) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( ( ~ v4_pre_topc(sK5,sK4)
        & k2_pre_topc(sK4,sK5) = sK5
        & v2_pre_topc(sK4) )
      | ( k2_pre_topc(sK4,sK5) != sK5
        & v4_pre_topc(sK5,sK4) ) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f41,f40])).

fof(f66,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,
    ( k2_pre_topc(sK4,sK5) = sK5
    | v4_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( r2_hidden(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                     => r2_hidden(X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r1_tarski(X1,X3)
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X2,sK2(X0,X1,X2))
        & r1_tarski(X1,sK2(X0,X1,X2))
        & v4_pre_topc(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( ~ r2_hidden(X2,sK2(X0,X1,X2))
                    & r1_tarski(X1,sK2(X0,X1,X2))
                    & v4_pre_topc(sK2(X0,X1,X2),X0)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X2,X4)
      | ~ r1_tarski(X1,X4)
      | ~ v4_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X3,X2)
                  <=> ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) ) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2)
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r1_tarski(X1,X3)
                  | ~ v4_pre_topc(X3,X0) )
                & ( ( r1_tarski(X1,X3)
                    & v4_pre_topc(X3,X0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1))
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK3(X0,X1))
                | ~ r1_tarski(X1,X3)
                | ~ v4_pre_topc(X3,X0) )
              & ( ( r1_tarski(X1,X3)
                  & v4_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK3(X0,X1)) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1))
            & ! [X3] :
                ( ( ( r2_hidden(X3,sK3(X0,X1))
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0) )
                  & ( ( r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,sK3(X0,X1)) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,
    ( v2_pre_topc(sK4)
    | v4_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,
    ( ~ v4_pre_topc(sK5,sK4)
    | k2_pre_topc(sK4,sK5) != sK5 ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ( ~ v4_pre_topc(sK1(X0,X1),X0)
            & r2_hidden(sK1(X0,X1),X1)
            & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f30])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,sK3(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1547,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_615,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(X0,k2_pre_topc(sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_1537,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK4,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_1779,plain,
    ( r1_tarski(sK5,k2_pre_topc(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_1537])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1552,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2119,plain,
    ( k2_pre_topc(sK4,sK5) = sK5
    | r1_tarski(k2_pre_topc(sK4,sK5),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_1552])).

cnf(c_25,negated_conjecture,
    ( v4_pre_topc(sK5,sK4)
    | k2_pre_topc(sK4,sK5) = sK5 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_617,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK5,k2_pre_topc(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_707,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_708,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(k2_pre_topc(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_710,plain,
    ( m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_1781,plain,
    ( ~ r1_tarski(k2_pre_topc(sK4,sK5),sK5)
    | ~ r1_tarski(sK5,k2_pre_topc(sK4,sK5))
    | k2_pre_topc(sK4,sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1810,plain,
    ( r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5))
    | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1809,plain,
    ( ~ r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),sK5)
    | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1906,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(X0))
    | r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),X0)
    | ~ r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2097,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5))
    | r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1906])).

cnf(c_1554,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,X0)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_626,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,X0)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ r1_tarski(X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_627,plain,
    ( ~ v4_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X2,X0)
    | ~ r2_hidden(X2,k2_pre_topc(sK4,X1))
    | ~ r2_hidden(X2,u1_struct_0(sK4))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_626])).

cnf(c_1536,plain,
    ( v4_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X2,X0) = iProver_top
    | r2_hidden(X2,k2_pre_topc(sK4,X1)) != iProver_top
    | r2_hidden(X2,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_1841,plain,
    ( v4_pre_topc(sK5,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK4,X0)) != iProver_top
    | r2_hidden(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_1536])).

cnf(c_2146,plain,
    ( v4_pre_topc(sK5,sK4) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK4,sK5)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_1841])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_83,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_85,plain,
    ( r1_tarski(sK5,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_2264,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK4,sK5)) != iProver_top
    | v4_pre_topc(sK5,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2146,c_85])).

cnf(c_2265,plain,
    ( v4_pre_topc(sK5,sK4) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK4,sK5)) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_2264])).

cnf(c_2274,plain,
    ( v4_pre_topc(sK5,sK4) != iProver_top
    | r2_hidden(sK0(k2_pre_topc(sK4,sK5),X0),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK0(k2_pre_topc(sK4,sK5),X0),sK5) = iProver_top
    | r1_tarski(k2_pre_topc(sK4,sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1554,c_2265])).

cnf(c_2275,plain,
    ( ~ v4_pre_topc(sK5,sK4)
    | ~ r2_hidden(sK0(k2_pre_topc(sK4,sK5),X0),u1_struct_0(sK4))
    | r2_hidden(sK0(k2_pre_topc(sK4,sK5),X0),sK5)
    | r1_tarski(k2_pre_topc(sK4,sK5),X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2274])).

cnf(c_2277,plain,
    ( ~ v4_pre_topc(sK5,sK4)
    | ~ r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),u1_struct_0(sK4))
    | r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),sK5)
    | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_2275])).

cnf(c_2853,plain,
    ( k2_pre_topc(sK4,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2119,c_28,c_25,c_617,c_710,c_1781,c_1810,c_1809,c_2097,c_2277])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_setfam_1(u1_struct_0(X1),sK3(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,negated_conjecture,
    ( v4_pre_topc(sK5,sK4)
    | v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_533,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k6_setfam_1(u1_struct_0(X1),sK3(X1,X0)) = k2_pre_topc(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_534,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_pre_topc(sK5,sK4)
    | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_534,c_29])).

cnf(c_539,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0) ),
    inference(renaming,[status(thm)],[c_538])).

cnf(c_1539,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0)
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_30,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_22,negated_conjecture,
    ( ~ v4_pre_topc(sK5,sK4)
    | k2_pre_topc(sK4,sK5) != sK5 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_36,plain,
    ( k2_pre_topc(sK4,sK5) != sK5
    | v4_pre_topc(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_535,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0)
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_2279,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1539,c_30,c_28,c_25,c_36,c_535,c_617,c_710,c_1781,c_1810,c_1809,c_2097,c_2277])).

cnf(c_2287,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)) = k2_pre_topc(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1547,c_2279])).

cnf(c_2856,plain,
    ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_2853,c_2287])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_436,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_437,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_441,plain,
    ( m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_pre_topc(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_29])).

cnf(c_442,plain,
    ( v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(renaming,[status(thm)],[c_441])).

cnf(c_1543,plain,
    ( v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_443,plain,
    ( v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_2334,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1543,c_28,c_25,c_36,c_443,c_617,c_710,c_1781,c_1810,c_1809,c_2097,c_2277])).

cnf(c_9,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_388,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_389,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(sK1(sK4,X0),X0)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_393,plain,
    ( r2_hidden(sK1(sK4,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v4_pre_topc(sK5,sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_29])).

cnf(c_394,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(sK1(sK4,X0),X0) ),
    inference(renaming,[status(thm)],[c_393])).

cnf(c_1545,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(sK1(sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_390,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(sK1(sK4,X0),X0) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_2409,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(sK1(sK4,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1545,c_30,c_28,c_25,c_36,c_390,c_617,c_710,c_1781,c_1810,c_1809,c_2097,c_2277])).

cnf(c_2418,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(sK4,sK3(sK4,X0)),sK3(sK4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2334,c_2409])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1553,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6692,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(sK4,sK3(sK4,X0)),X1) = iProver_top
    | r1_tarski(sK3(sK4,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2418,c_1553])).

cnf(c_8040,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(sK4,sK3(sK4,X0)),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK3(sK4,X0),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6692,c_1553])).

cnf(c_10,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_364,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_365,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_369,plain,
    ( m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v4_pre_topc(sK5,sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_29])).

cnf(c_370,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_369])).

cnf(c_2342,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(sK1(sK4,sK3(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_2343,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | m1_subset_1(sK1(sK4,sK3(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2342])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(sK1(X0,X1),X0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_412,plain,
    ( ~ v4_pre_topc(sK1(X0,X1),X0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_413,plain,
    ( ~ v4_pre_topc(sK1(sK4,X0),sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | v4_pre_topc(sK5,sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | ~ v4_pre_topc(sK1(sK4,X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_29])).

cnf(c_418,plain,
    ( ~ v4_pre_topc(sK1(sK4,X0),sK4)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(renaming,[status(thm)],[c_417])).

cnf(c_1544,plain,
    ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_419,plain,
    ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_2578,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1544,c_28,c_25,c_36,c_419,c_617,c_710,c_1781,c_1810,c_1809,c_2097,c_2277])).

cnf(c_2579,plain,
    ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2578])).

cnf(c_2587,plain,
    ( v4_pre_topc(sK1(sK4,sK3(sK4,X0)),sK4) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2334,c_2579])).

cnf(c_19,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,sK3(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_457,plain,
    ( v4_pre_topc(X0,X1)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,sK3(X1,X2))
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_458,plain,
    ( v4_pre_topc(X0,sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,sK3(sK4,X1))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_462,plain,
    ( ~ r2_hidden(X0,sK3(sK4,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_pre_topc(sK5,sK4)
    | v4_pre_topc(X0,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_29])).

cnf(c_463,plain,
    ( v4_pre_topc(X0,sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,sK3(sK4,X1)) ),
    inference(renaming,[status(thm)],[c_462])).

cnf(c_9014,plain,
    ( v4_pre_topc(sK1(sK4,sK3(sK4,X0)),sK4)
    | v4_pre_topc(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK1(sK4,sK3(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK3(sK4,X0)),sK3(sK4,X0)) ),
    inference(instantiation,[status(thm)],[c_463])).

cnf(c_9015,plain,
    ( v4_pre_topc(sK1(sK4,sK3(sK4,X0)),sK4) = iProver_top
    | v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK1(sK4,sK3(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(sK4,sK3(sK4,X0)),sK3(sK4,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9014])).

cnf(c_10229,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8040,c_28,c_25,c_36,c_443,c_617,c_710,c_1781,c_1810,c_1809,c_2097,c_2277,c_2343,c_2418,c_2587,c_9015])).

cnf(c_10230,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10229])).

cnf(c_10237,plain,
    ( v4_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2856,c_10230])).

cnf(c_31,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10237,c_2853,c_36,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.87/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.01  
% 2.87/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.87/1.01  
% 2.87/1.01  ------  iProver source info
% 2.87/1.01  
% 2.87/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.87/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.87/1.01  git: non_committed_changes: false
% 2.87/1.01  git: last_make_outside_of_git: false
% 2.87/1.01  
% 2.87/1.01  ------ 
% 2.87/1.01  
% 2.87/1.01  ------ Input Options
% 2.87/1.01  
% 2.87/1.01  --out_options                           all
% 2.87/1.01  --tptp_safe_out                         true
% 2.87/1.01  --problem_path                          ""
% 2.87/1.01  --include_path                          ""
% 2.87/1.01  --clausifier                            res/vclausify_rel
% 2.87/1.01  --clausifier_options                    --mode clausify
% 2.87/1.01  --stdin                                 false
% 2.87/1.01  --stats_out                             all
% 2.87/1.01  
% 2.87/1.01  ------ General Options
% 2.87/1.01  
% 2.87/1.01  --fof                                   false
% 2.87/1.01  --time_out_real                         305.
% 2.87/1.01  --time_out_virtual                      -1.
% 2.87/1.01  --symbol_type_check                     false
% 2.87/1.01  --clausify_out                          false
% 2.87/1.01  --sig_cnt_out                           false
% 2.87/1.01  --trig_cnt_out                          false
% 2.87/1.01  --trig_cnt_out_tolerance                1.
% 2.87/1.01  --trig_cnt_out_sk_spl                   false
% 2.87/1.01  --abstr_cl_out                          false
% 2.87/1.01  
% 2.87/1.01  ------ Global Options
% 2.87/1.01  
% 2.87/1.01  --schedule                              default
% 2.87/1.01  --add_important_lit                     false
% 2.87/1.01  --prop_solver_per_cl                    1000
% 2.87/1.01  --min_unsat_core                        false
% 2.87/1.01  --soft_assumptions                      false
% 2.87/1.01  --soft_lemma_size                       3
% 2.87/1.01  --prop_impl_unit_size                   0
% 2.87/1.01  --prop_impl_unit                        []
% 2.87/1.01  --share_sel_clauses                     true
% 2.87/1.01  --reset_solvers                         false
% 2.87/1.01  --bc_imp_inh                            [conj_cone]
% 2.87/1.01  --conj_cone_tolerance                   3.
% 2.87/1.01  --extra_neg_conj                        none
% 2.87/1.01  --large_theory_mode                     true
% 2.87/1.01  --prolific_symb_bound                   200
% 2.87/1.01  --lt_threshold                          2000
% 2.87/1.01  --clause_weak_htbl                      true
% 2.87/1.01  --gc_record_bc_elim                     false
% 2.87/1.01  
% 2.87/1.01  ------ Preprocessing Options
% 2.87/1.01  
% 2.87/1.01  --preprocessing_flag                    true
% 2.87/1.01  --time_out_prep_mult                    0.1
% 2.87/1.01  --splitting_mode                        input
% 2.87/1.01  --splitting_grd                         true
% 2.87/1.01  --splitting_cvd                         false
% 2.87/1.01  --splitting_cvd_svl                     false
% 2.87/1.01  --splitting_nvd                         32
% 2.87/1.01  --sub_typing                            true
% 2.87/1.01  --prep_gs_sim                           true
% 2.87/1.01  --prep_unflatten                        true
% 2.87/1.01  --prep_res_sim                          true
% 2.87/1.01  --prep_upred                            true
% 2.87/1.01  --prep_sem_filter                       exhaustive
% 2.87/1.01  --prep_sem_filter_out                   false
% 2.87/1.01  --pred_elim                             true
% 2.87/1.01  --res_sim_input                         true
% 2.87/1.01  --eq_ax_congr_red                       true
% 2.87/1.01  --pure_diseq_elim                       true
% 2.87/1.01  --brand_transform                       false
% 2.87/1.01  --non_eq_to_eq                          false
% 2.87/1.01  --prep_def_merge                        true
% 2.87/1.01  --prep_def_merge_prop_impl              false
% 2.87/1.01  --prep_def_merge_mbd                    true
% 2.87/1.01  --prep_def_merge_tr_red                 false
% 2.87/1.01  --prep_def_merge_tr_cl                  false
% 2.87/1.01  --smt_preprocessing                     true
% 2.87/1.01  --smt_ac_axioms                         fast
% 2.87/1.01  --preprocessed_out                      false
% 2.87/1.01  --preprocessed_stats                    false
% 2.87/1.01  
% 2.87/1.01  ------ Abstraction refinement Options
% 2.87/1.01  
% 2.87/1.01  --abstr_ref                             []
% 2.87/1.01  --abstr_ref_prep                        false
% 2.87/1.01  --abstr_ref_until_sat                   false
% 2.87/1.01  --abstr_ref_sig_restrict                funpre
% 2.87/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/1.01  --abstr_ref_under                       []
% 2.87/1.01  
% 2.87/1.01  ------ SAT Options
% 2.87/1.01  
% 2.87/1.01  --sat_mode                              false
% 2.87/1.01  --sat_fm_restart_options                ""
% 2.87/1.01  --sat_gr_def                            false
% 2.87/1.01  --sat_epr_types                         true
% 2.87/1.01  --sat_non_cyclic_types                  false
% 2.87/1.01  --sat_finite_models                     false
% 2.87/1.01  --sat_fm_lemmas                         false
% 2.87/1.01  --sat_fm_prep                           false
% 2.87/1.01  --sat_fm_uc_incr                        true
% 2.87/1.01  --sat_out_model                         small
% 2.87/1.01  --sat_out_clauses                       false
% 2.87/1.01  
% 2.87/1.01  ------ QBF Options
% 2.87/1.01  
% 2.87/1.01  --qbf_mode                              false
% 2.87/1.01  --qbf_elim_univ                         false
% 2.87/1.01  --qbf_dom_inst                          none
% 2.87/1.01  --qbf_dom_pre_inst                      false
% 2.87/1.01  --qbf_sk_in                             false
% 2.87/1.01  --qbf_pred_elim                         true
% 2.87/1.01  --qbf_split                             512
% 2.87/1.01  
% 2.87/1.01  ------ BMC1 Options
% 2.87/1.01  
% 2.87/1.01  --bmc1_incremental                      false
% 2.87/1.01  --bmc1_axioms                           reachable_all
% 2.87/1.01  --bmc1_min_bound                        0
% 2.87/1.01  --bmc1_max_bound                        -1
% 2.87/1.01  --bmc1_max_bound_default                -1
% 2.87/1.01  --bmc1_symbol_reachability              true
% 2.87/1.01  --bmc1_property_lemmas                  false
% 2.87/1.01  --bmc1_k_induction                      false
% 2.87/1.01  --bmc1_non_equiv_states                 false
% 2.87/1.01  --bmc1_deadlock                         false
% 2.87/1.01  --bmc1_ucm                              false
% 2.87/1.01  --bmc1_add_unsat_core                   none
% 2.87/1.01  --bmc1_unsat_core_children              false
% 2.87/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/1.01  --bmc1_out_stat                         full
% 2.87/1.01  --bmc1_ground_init                      false
% 2.87/1.01  --bmc1_pre_inst_next_state              false
% 2.87/1.01  --bmc1_pre_inst_state                   false
% 2.87/1.01  --bmc1_pre_inst_reach_state             false
% 2.87/1.01  --bmc1_out_unsat_core                   false
% 2.87/1.01  --bmc1_aig_witness_out                  false
% 2.87/1.01  --bmc1_verbose                          false
% 2.87/1.01  --bmc1_dump_clauses_tptp                false
% 2.87/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.87/1.01  --bmc1_dump_file                        -
% 2.87/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.87/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.87/1.01  --bmc1_ucm_extend_mode                  1
% 2.87/1.01  --bmc1_ucm_init_mode                    2
% 2.87/1.01  --bmc1_ucm_cone_mode                    none
% 2.87/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.87/1.01  --bmc1_ucm_relax_model                  4
% 2.87/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.87/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/1.01  --bmc1_ucm_layered_model                none
% 2.87/1.01  --bmc1_ucm_max_lemma_size               10
% 2.87/1.01  
% 2.87/1.01  ------ AIG Options
% 2.87/1.01  
% 2.87/1.01  --aig_mode                              false
% 2.87/1.01  
% 2.87/1.01  ------ Instantiation Options
% 2.87/1.01  
% 2.87/1.01  --instantiation_flag                    true
% 2.87/1.01  --inst_sos_flag                         false
% 2.87/1.01  --inst_sos_phase                        true
% 2.87/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/1.01  --inst_lit_sel_side                     num_symb
% 2.87/1.01  --inst_solver_per_active                1400
% 2.87/1.01  --inst_solver_calls_frac                1.
% 2.87/1.01  --inst_passive_queue_type               priority_queues
% 2.87/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/1.01  --inst_passive_queues_freq              [25;2]
% 2.87/1.01  --inst_dismatching                      true
% 2.87/1.01  --inst_eager_unprocessed_to_passive     true
% 2.87/1.01  --inst_prop_sim_given                   true
% 2.87/1.01  --inst_prop_sim_new                     false
% 2.87/1.01  --inst_subs_new                         false
% 2.87/1.01  --inst_eq_res_simp                      false
% 2.87/1.01  --inst_subs_given                       false
% 2.87/1.01  --inst_orphan_elimination               true
% 2.87/1.01  --inst_learning_loop_flag               true
% 2.87/1.01  --inst_learning_start                   3000
% 2.87/1.01  --inst_learning_factor                  2
% 2.87/1.01  --inst_start_prop_sim_after_learn       3
% 2.87/1.01  --inst_sel_renew                        solver
% 2.87/1.01  --inst_lit_activity_flag                true
% 2.87/1.01  --inst_restr_to_given                   false
% 2.87/1.01  --inst_activity_threshold               500
% 2.87/1.01  --inst_out_proof                        true
% 2.87/1.01  
% 2.87/1.01  ------ Resolution Options
% 2.87/1.01  
% 2.87/1.01  --resolution_flag                       true
% 2.87/1.01  --res_lit_sel                           adaptive
% 2.87/1.01  --res_lit_sel_side                      none
% 2.87/1.01  --res_ordering                          kbo
% 2.87/1.01  --res_to_prop_solver                    active
% 2.87/1.01  --res_prop_simpl_new                    false
% 2.87/1.01  --res_prop_simpl_given                  true
% 2.87/1.01  --res_passive_queue_type                priority_queues
% 2.87/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/1.01  --res_passive_queues_freq               [15;5]
% 2.87/1.01  --res_forward_subs                      full
% 2.87/1.01  --res_backward_subs                     full
% 2.87/1.01  --res_forward_subs_resolution           true
% 2.87/1.01  --res_backward_subs_resolution          true
% 2.87/1.01  --res_orphan_elimination                true
% 2.87/1.01  --res_time_limit                        2.
% 2.87/1.01  --res_out_proof                         true
% 2.87/1.01  
% 2.87/1.01  ------ Superposition Options
% 2.87/1.01  
% 2.87/1.01  --superposition_flag                    true
% 2.87/1.01  --sup_passive_queue_type                priority_queues
% 2.87/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.87/1.01  --demod_completeness_check              fast
% 2.87/1.01  --demod_use_ground                      true
% 2.87/1.01  --sup_to_prop_solver                    passive
% 2.87/1.01  --sup_prop_simpl_new                    true
% 2.87/1.01  --sup_prop_simpl_given                  true
% 2.87/1.01  --sup_fun_splitting                     false
% 2.87/1.01  --sup_smt_interval                      50000
% 2.87/1.01  
% 2.87/1.01  ------ Superposition Simplification Setup
% 2.87/1.01  
% 2.87/1.01  --sup_indices_passive                   []
% 2.87/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.01  --sup_full_bw                           [BwDemod]
% 2.87/1.01  --sup_immed_triv                        [TrivRules]
% 2.87/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.01  --sup_immed_bw_main                     []
% 2.87/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.01  
% 2.87/1.01  ------ Combination Options
% 2.87/1.01  
% 2.87/1.01  --comb_res_mult                         3
% 2.87/1.01  --comb_sup_mult                         2
% 2.87/1.01  --comb_inst_mult                        10
% 2.87/1.01  
% 2.87/1.01  ------ Debug Options
% 2.87/1.01  
% 2.87/1.01  --dbg_backtrace                         false
% 2.87/1.01  --dbg_dump_prop_clauses                 false
% 2.87/1.01  --dbg_dump_prop_clauses_file            -
% 2.87/1.01  --dbg_out_stat                          false
% 2.87/1.01  ------ Parsing...
% 2.87/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.87/1.01  
% 2.87/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.87/1.01  
% 2.87/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.87/1.01  
% 2.87/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.87/1.01  ------ Proving...
% 2.87/1.01  ------ Problem Properties 
% 2.87/1.01  
% 2.87/1.01  
% 2.87/1.01  clauses                                 24
% 2.87/1.01  conjectures                             3
% 2.87/1.01  EPR                                     3
% 2.87/1.01  Horn                                    11
% 2.87/1.01  unary                                   2
% 2.87/1.01  binary                                  6
% 2.87/1.01  lits                                    80
% 2.87/1.01  lits eq                                 4
% 2.87/1.01  fd_pure                                 0
% 2.87/1.01  fd_pseudo                               0
% 2.87/1.01  fd_cond                                 0
% 2.87/1.01  fd_pseudo_cond                          1
% 2.87/1.01  AC symbols                              0
% 2.87/1.01  
% 2.87/1.01  ------ Schedule dynamic 5 is on 
% 2.87/1.01  
% 2.87/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.87/1.01  
% 2.87/1.01  
% 2.87/1.01  ------ 
% 2.87/1.01  Current options:
% 2.87/1.01  ------ 
% 2.87/1.01  
% 2.87/1.01  ------ Input Options
% 2.87/1.01  
% 2.87/1.01  --out_options                           all
% 2.87/1.01  --tptp_safe_out                         true
% 2.87/1.01  --problem_path                          ""
% 2.87/1.01  --include_path                          ""
% 2.87/1.01  --clausifier                            res/vclausify_rel
% 2.87/1.01  --clausifier_options                    --mode clausify
% 2.87/1.01  --stdin                                 false
% 2.87/1.01  --stats_out                             all
% 2.87/1.01  
% 2.87/1.01  ------ General Options
% 2.87/1.01  
% 2.87/1.01  --fof                                   false
% 2.87/1.01  --time_out_real                         305.
% 2.87/1.01  --time_out_virtual                      -1.
% 2.87/1.01  --symbol_type_check                     false
% 2.87/1.01  --clausify_out                          false
% 2.87/1.01  --sig_cnt_out                           false
% 2.87/1.01  --trig_cnt_out                          false
% 2.87/1.01  --trig_cnt_out_tolerance                1.
% 2.87/1.01  --trig_cnt_out_sk_spl                   false
% 2.87/1.01  --abstr_cl_out                          false
% 2.87/1.01  
% 2.87/1.01  ------ Global Options
% 2.87/1.01  
% 2.87/1.01  --schedule                              default
% 2.87/1.01  --add_important_lit                     false
% 2.87/1.01  --prop_solver_per_cl                    1000
% 2.87/1.01  --min_unsat_core                        false
% 2.87/1.01  --soft_assumptions                      false
% 2.87/1.01  --soft_lemma_size                       3
% 2.87/1.01  --prop_impl_unit_size                   0
% 2.87/1.01  --prop_impl_unit                        []
% 2.87/1.01  --share_sel_clauses                     true
% 2.87/1.01  --reset_solvers                         false
% 2.87/1.01  --bc_imp_inh                            [conj_cone]
% 2.87/1.01  --conj_cone_tolerance                   3.
% 2.87/1.01  --extra_neg_conj                        none
% 2.87/1.01  --large_theory_mode                     true
% 2.87/1.01  --prolific_symb_bound                   200
% 2.87/1.01  --lt_threshold                          2000
% 2.87/1.01  --clause_weak_htbl                      true
% 2.87/1.01  --gc_record_bc_elim                     false
% 2.87/1.01  
% 2.87/1.01  ------ Preprocessing Options
% 2.87/1.01  
% 2.87/1.01  --preprocessing_flag                    true
% 2.87/1.01  --time_out_prep_mult                    0.1
% 2.87/1.01  --splitting_mode                        input
% 2.87/1.01  --splitting_grd                         true
% 2.87/1.01  --splitting_cvd                         false
% 2.87/1.01  --splitting_cvd_svl                     false
% 2.87/1.01  --splitting_nvd                         32
% 2.87/1.01  --sub_typing                            true
% 2.87/1.01  --prep_gs_sim                           true
% 2.87/1.01  --prep_unflatten                        true
% 2.87/1.01  --prep_res_sim                          true
% 2.87/1.01  --prep_upred                            true
% 2.87/1.01  --prep_sem_filter                       exhaustive
% 2.87/1.01  --prep_sem_filter_out                   false
% 2.87/1.01  --pred_elim                             true
% 2.87/1.01  --res_sim_input                         true
% 2.87/1.01  --eq_ax_congr_red                       true
% 2.87/1.01  --pure_diseq_elim                       true
% 2.87/1.01  --brand_transform                       false
% 2.87/1.01  --non_eq_to_eq                          false
% 2.87/1.01  --prep_def_merge                        true
% 2.87/1.01  --prep_def_merge_prop_impl              false
% 2.87/1.01  --prep_def_merge_mbd                    true
% 2.87/1.01  --prep_def_merge_tr_red                 false
% 2.87/1.01  --prep_def_merge_tr_cl                  false
% 2.87/1.01  --smt_preprocessing                     true
% 2.87/1.01  --smt_ac_axioms                         fast
% 2.87/1.01  --preprocessed_out                      false
% 2.87/1.01  --preprocessed_stats                    false
% 2.87/1.01  
% 2.87/1.01  ------ Abstraction refinement Options
% 2.87/1.01  
% 2.87/1.01  --abstr_ref                             []
% 2.87/1.01  --abstr_ref_prep                        false
% 2.87/1.01  --abstr_ref_until_sat                   false
% 2.87/1.01  --abstr_ref_sig_restrict                funpre
% 2.87/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/1.01  --abstr_ref_under                       []
% 2.87/1.01  
% 2.87/1.01  ------ SAT Options
% 2.87/1.01  
% 2.87/1.01  --sat_mode                              false
% 2.87/1.01  --sat_fm_restart_options                ""
% 2.87/1.01  --sat_gr_def                            false
% 2.87/1.01  --sat_epr_types                         true
% 2.87/1.01  --sat_non_cyclic_types                  false
% 2.87/1.01  --sat_finite_models                     false
% 2.87/1.01  --sat_fm_lemmas                         false
% 2.87/1.01  --sat_fm_prep                           false
% 2.87/1.01  --sat_fm_uc_incr                        true
% 2.87/1.01  --sat_out_model                         small
% 2.87/1.01  --sat_out_clauses                       false
% 2.87/1.01  
% 2.87/1.01  ------ QBF Options
% 2.87/1.01  
% 2.87/1.01  --qbf_mode                              false
% 2.87/1.01  --qbf_elim_univ                         false
% 2.87/1.01  --qbf_dom_inst                          none
% 2.87/1.01  --qbf_dom_pre_inst                      false
% 2.87/1.01  --qbf_sk_in                             false
% 2.87/1.01  --qbf_pred_elim                         true
% 2.87/1.01  --qbf_split                             512
% 2.87/1.01  
% 2.87/1.01  ------ BMC1 Options
% 2.87/1.01  
% 2.87/1.01  --bmc1_incremental                      false
% 2.87/1.01  --bmc1_axioms                           reachable_all
% 2.87/1.01  --bmc1_min_bound                        0
% 2.87/1.01  --bmc1_max_bound                        -1
% 2.87/1.01  --bmc1_max_bound_default                -1
% 2.87/1.01  --bmc1_symbol_reachability              true
% 2.87/1.01  --bmc1_property_lemmas                  false
% 2.87/1.01  --bmc1_k_induction                      false
% 2.87/1.01  --bmc1_non_equiv_states                 false
% 2.87/1.01  --bmc1_deadlock                         false
% 2.87/1.01  --bmc1_ucm                              false
% 2.87/1.01  --bmc1_add_unsat_core                   none
% 2.87/1.01  --bmc1_unsat_core_children              false
% 2.87/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/1.01  --bmc1_out_stat                         full
% 2.87/1.01  --bmc1_ground_init                      false
% 2.87/1.01  --bmc1_pre_inst_next_state              false
% 2.87/1.01  --bmc1_pre_inst_state                   false
% 2.87/1.01  --bmc1_pre_inst_reach_state             false
% 2.87/1.01  --bmc1_out_unsat_core                   false
% 2.87/1.01  --bmc1_aig_witness_out                  false
% 2.87/1.01  --bmc1_verbose                          false
% 2.87/1.01  --bmc1_dump_clauses_tptp                false
% 2.87/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.87/1.01  --bmc1_dump_file                        -
% 2.87/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.87/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.87/1.01  --bmc1_ucm_extend_mode                  1
% 2.87/1.01  --bmc1_ucm_init_mode                    2
% 2.87/1.01  --bmc1_ucm_cone_mode                    none
% 2.87/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.87/1.01  --bmc1_ucm_relax_model                  4
% 2.87/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.87/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/1.01  --bmc1_ucm_layered_model                none
% 2.87/1.01  --bmc1_ucm_max_lemma_size               10
% 2.87/1.01  
% 2.87/1.01  ------ AIG Options
% 2.87/1.01  
% 2.87/1.01  --aig_mode                              false
% 2.87/1.01  
% 2.87/1.01  ------ Instantiation Options
% 2.87/1.01  
% 2.87/1.01  --instantiation_flag                    true
% 2.87/1.01  --inst_sos_flag                         false
% 2.87/1.01  --inst_sos_phase                        true
% 2.87/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/1.01  --inst_lit_sel_side                     none
% 2.87/1.01  --inst_solver_per_active                1400
% 2.87/1.01  --inst_solver_calls_frac                1.
% 2.87/1.01  --inst_passive_queue_type               priority_queues
% 2.87/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/1.01  --inst_passive_queues_freq              [25;2]
% 2.87/1.01  --inst_dismatching                      true
% 2.87/1.01  --inst_eager_unprocessed_to_passive     true
% 2.87/1.01  --inst_prop_sim_given                   true
% 2.87/1.01  --inst_prop_sim_new                     false
% 2.87/1.01  --inst_subs_new                         false
% 2.87/1.01  --inst_eq_res_simp                      false
% 2.87/1.01  --inst_subs_given                       false
% 2.87/1.01  --inst_orphan_elimination               true
% 2.87/1.01  --inst_learning_loop_flag               true
% 2.87/1.01  --inst_learning_start                   3000
% 2.87/1.01  --inst_learning_factor                  2
% 2.87/1.01  --inst_start_prop_sim_after_learn       3
% 2.87/1.01  --inst_sel_renew                        solver
% 2.87/1.01  --inst_lit_activity_flag                true
% 2.87/1.01  --inst_restr_to_given                   false
% 2.87/1.01  --inst_activity_threshold               500
% 2.87/1.01  --inst_out_proof                        true
% 2.87/1.01  
% 2.87/1.01  ------ Resolution Options
% 2.87/1.01  
% 2.87/1.01  --resolution_flag                       false
% 2.87/1.01  --res_lit_sel                           adaptive
% 2.87/1.01  --res_lit_sel_side                      none
% 2.87/1.01  --res_ordering                          kbo
% 2.87/1.01  --res_to_prop_solver                    active
% 2.87/1.01  --res_prop_simpl_new                    false
% 2.87/1.01  --res_prop_simpl_given                  true
% 2.87/1.01  --res_passive_queue_type                priority_queues
% 2.87/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/1.01  --res_passive_queues_freq               [15;5]
% 2.87/1.01  --res_forward_subs                      full
% 2.87/1.01  --res_backward_subs                     full
% 2.87/1.01  --res_forward_subs_resolution           true
% 2.87/1.01  --res_backward_subs_resolution          true
% 2.87/1.01  --res_orphan_elimination                true
% 2.87/1.01  --res_time_limit                        2.
% 2.87/1.01  --res_out_proof                         true
% 2.87/1.01  
% 2.87/1.01  ------ Superposition Options
% 2.87/1.01  
% 2.87/1.01  --superposition_flag                    true
% 2.87/1.01  --sup_passive_queue_type                priority_queues
% 2.87/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.87/1.01  --demod_completeness_check              fast
% 2.87/1.01  --demod_use_ground                      true
% 2.87/1.01  --sup_to_prop_solver                    passive
% 2.87/1.01  --sup_prop_simpl_new                    true
% 2.87/1.01  --sup_prop_simpl_given                  true
% 2.87/1.01  --sup_fun_splitting                     false
% 2.87/1.01  --sup_smt_interval                      50000
% 2.87/1.01  
% 2.87/1.01  ------ Superposition Simplification Setup
% 2.87/1.01  
% 2.87/1.01  --sup_indices_passive                   []
% 2.87/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.01  --sup_full_bw                           [BwDemod]
% 2.87/1.01  --sup_immed_triv                        [TrivRules]
% 2.87/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.01  --sup_immed_bw_main                     []
% 2.87/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/1.01  
% 2.87/1.01  ------ Combination Options
% 2.87/1.01  
% 2.87/1.01  --comb_res_mult                         3
% 2.87/1.01  --comb_sup_mult                         2
% 2.87/1.01  --comb_inst_mult                        10
% 2.87/1.01  
% 2.87/1.01  ------ Debug Options
% 2.87/1.01  
% 2.87/1.01  --dbg_backtrace                         false
% 2.87/1.01  --dbg_dump_prop_clauses                 false
% 2.87/1.01  --dbg_dump_prop_clauses_file            -
% 2.87/1.01  --dbg_out_stat                          false
% 2.87/1.01  
% 2.87/1.01  
% 2.87/1.01  
% 2.87/1.01  
% 2.87/1.01  ------ Proving...
% 2.87/1.01  
% 2.87/1.01  
% 2.87/1.01  % SZS status Theorem for theBenchmark.p
% 2.87/1.01  
% 2.87/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.87/1.01  
% 2.87/1.01  fof(f9,conjecture,(
% 2.87/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.87/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.01  
% 2.87/1.01  fof(f10,negated_conjecture,(
% 2.87/1.01    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.87/1.01    inference(negated_conjecture,[],[f9])).
% 2.87/1.01  
% 2.87/1.01  fof(f22,plain,(
% 2.87/1.01    ? [X0] : (? [X1] : (((~v4_pre_topc(X1,X0) & (k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0))) | (k2_pre_topc(X0,X1) != X1 & v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.87/1.01    inference(ennf_transformation,[],[f10])).
% 2.87/1.01  
% 2.87/1.01  fof(f23,plain,(
% 2.87/1.01    ? [X0] : (? [X1] : (((~v4_pre_topc(X1,X0) & k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) | (k2_pre_topc(X0,X1) != X1 & v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.87/1.01    inference(flattening,[],[f22])).
% 2.87/1.01  
% 2.87/1.01  fof(f41,plain,(
% 2.87/1.01    ( ! [X0] : (? [X1] : (((~v4_pre_topc(X1,X0) & k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) | (k2_pre_topc(X0,X1) != X1 & v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((~v4_pre_topc(sK5,X0) & k2_pre_topc(X0,sK5) = sK5 & v2_pre_topc(X0)) | (k2_pre_topc(X0,sK5) != sK5 & v4_pre_topc(sK5,X0))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.87/1.01    introduced(choice_axiom,[])).
% 2.87/1.01  
% 2.87/1.01  fof(f40,plain,(
% 2.87/1.01    ? [X0] : (? [X1] : (((~v4_pre_topc(X1,X0) & k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) | (k2_pre_topc(X0,X1) != X1 & v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (((~v4_pre_topc(X1,sK4) & k2_pre_topc(sK4,X1) = X1 & v2_pre_topc(sK4)) | (k2_pre_topc(sK4,X1) != X1 & v4_pre_topc(X1,sK4))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4))),
% 2.87/1.01    introduced(choice_axiom,[])).
% 2.87/1.01  
% 2.87/1.01  fof(f42,plain,(
% 2.87/1.01    (((~v4_pre_topc(sK5,sK4) & k2_pre_topc(sK4,sK5) = sK5 & v2_pre_topc(sK4)) | (k2_pre_topc(sK4,sK5) != sK5 & v4_pre_topc(sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4)),
% 2.87/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f41,f40])).
% 2.87/1.01  
% 2.87/1.01  fof(f66,plain,(
% 2.87/1.01    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.87/1.01    inference(cnf_transformation,[],[f42])).
% 2.87/1.01  
% 2.87/1.01  fof(f8,axiom,(
% 2.87/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.87/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.01  
% 2.87/1.01  fof(f21,plain,(
% 2.87/1.01    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.87/1.01    inference(ennf_transformation,[],[f8])).
% 2.87/1.01  
% 2.87/1.01  fof(f64,plain,(
% 2.87/1.01    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.87/1.01    inference(cnf_transformation,[],[f21])).
% 2.87/1.01  
% 2.87/1.01  fof(f65,plain,(
% 2.87/1.01    l1_pre_topc(sK4)),
% 2.87/1.01    inference(cnf_transformation,[],[f42])).
% 2.87/1.01  
% 2.87/1.01  fof(f2,axiom,(
% 2.87/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.87/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.01  
% 2.87/1.01  fof(f28,plain,(
% 2.87/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.87/1.01    inference(nnf_transformation,[],[f2])).
% 2.87/1.01  
% 2.87/1.01  fof(f29,plain,(
% 2.87/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.87/1.01    inference(flattening,[],[f28])).
% 2.87/1.01  
% 2.87/1.01  fof(f48,plain,(
% 2.87/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.87/1.01    inference(cnf_transformation,[],[f29])).
% 2.87/1.01  
% 2.87/1.01  fof(f69,plain,(
% 2.87/1.01    k2_pre_topc(sK4,sK5) = sK5 | v4_pre_topc(sK5,sK4)),
% 2.87/1.01    inference(cnf_transformation,[],[f42])).
% 2.87/1.01  
% 2.87/1.01  fof(f4,axiom,(
% 2.87/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.87/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.01  
% 2.87/1.01  fof(f13,plain,(
% 2.87/1.01    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.87/1.01    inference(ennf_transformation,[],[f4])).
% 2.87/1.01  
% 2.87/1.01  fof(f14,plain,(
% 2.87/1.01    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.87/1.01    inference(flattening,[],[f13])).
% 2.87/1.01  
% 2.87/1.01  fof(f50,plain,(
% 2.87/1.01    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.87/1.01    inference(cnf_transformation,[],[f14])).
% 2.87/1.01  
% 2.87/1.01  fof(f1,axiom,(
% 2.87/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.87/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.01  
% 2.87/1.01  fof(f11,plain,(
% 2.87/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.87/1.01    inference(ennf_transformation,[],[f1])).
% 2.87/1.01  
% 2.87/1.01  fof(f24,plain,(
% 2.87/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.87/1.01    inference(nnf_transformation,[],[f11])).
% 2.87/1.01  
% 2.87/1.01  fof(f25,plain,(
% 2.87/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.87/1.01    inference(rectify,[],[f24])).
% 2.87/1.01  
% 2.87/1.01  fof(f26,plain,(
% 2.87/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.87/1.01    introduced(choice_axiom,[])).
% 2.87/1.01  
% 2.87/1.01  fof(f27,plain,(
% 2.87/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.87/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 2.87/1.01  
% 2.87/1.01  fof(f44,plain,(
% 2.87/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.87/1.01    inference(cnf_transformation,[],[f27])).
% 2.87/1.01  
% 2.87/1.01  fof(f45,plain,(
% 2.87/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.87/1.01    inference(cnf_transformation,[],[f27])).
% 2.87/1.01  
% 2.87/1.01  fof(f3,axiom,(
% 2.87/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.87/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.01  
% 2.87/1.01  fof(f12,plain,(
% 2.87/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.87/1.01    inference(ennf_transformation,[],[f3])).
% 2.87/1.01  
% 2.87/1.01  fof(f49,plain,(
% 2.87/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.87/1.01    inference(cnf_transformation,[],[f12])).
% 2.87/1.01  
% 2.87/1.01  fof(f6,axiom,(
% 2.87/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (r2_hidden(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) => r2_hidden(X2,X3)))))))),
% 2.87/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.01  
% 2.87/1.01  fof(f17,plain,(
% 2.87/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : ((r2_hidden(X2,X3) | (~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.87/1.01    inference(ennf_transformation,[],[f6])).
% 2.87/1.01  
% 2.87/1.01  fof(f18,plain,(
% 2.87/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (r2_hidden(X2,X3) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.87/1.01    inference(flattening,[],[f17])).
% 2.87/1.01  
% 2.87/1.01  fof(f32,plain,(
% 2.87/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X2,X3) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.87/1.01    inference(nnf_transformation,[],[f18])).
% 2.87/1.01  
% 2.87/1.01  fof(f33,plain,(
% 2.87/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.87/1.01    inference(rectify,[],[f32])).
% 2.87/1.01  
% 2.87/1.01  fof(f34,plain,(
% 2.87/1.01    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(X2,sK2(X0,X1,X2)) & r1_tarski(X1,sK2(X0,X1,X2)) & v4_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.87/1.01    introduced(choice_axiom,[])).
% 2.87/1.01  
% 2.87/1.01  fof(f35,plain,(
% 2.87/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (~r2_hidden(X2,sK2(X0,X1,X2)) & r1_tarski(X1,sK2(X0,X1,X2)) & v4_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.87/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 2.87/1.01  
% 2.87/1.01  fof(f54,plain,(
% 2.87/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~r2_hidden(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.87/1.01    inference(cnf_transformation,[],[f35])).
% 2.87/1.01  
% 2.87/1.01  fof(f46,plain,(
% 2.87/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.87/1.01    inference(cnf_transformation,[],[f29])).
% 2.87/1.01  
% 2.87/1.01  fof(f74,plain,(
% 2.87/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.87/1.01    inference(equality_resolution,[],[f46])).
% 2.87/1.01  
% 2.87/1.01  fof(f7,axiom,(
% 2.87/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r1_tarski(X1,X3) & v4_pre_topc(X3,X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 2.87/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.01  
% 2.87/1.01  fof(f19,plain,(
% 2.87/1.01    ! [X0] : (! [X1] : (? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : ((r2_hidden(X3,X2) <=> (r1_tarski(X1,X3) & v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.87/1.01    inference(ennf_transformation,[],[f7])).
% 2.87/1.01  
% 2.87/1.01  fof(f20,plain,(
% 2.87/1.01    ! [X0] : (! [X1] : (? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : ((r2_hidden(X3,X2) <=> (r1_tarski(X1,X3) & v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.87/1.01    inference(flattening,[],[f19])).
% 2.87/1.01  
% 2.87/1.01  fof(f36,plain,(
% 2.87/1.01    ! [X0] : (! [X1] : (? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : (((r2_hidden(X3,X2) | (~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0))) & ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.87/1.01    inference(nnf_transformation,[],[f20])).
% 2.87/1.01  
% 2.87/1.01  fof(f37,plain,(
% 2.87/1.01    ! [X0] : (! [X1] : (? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : (((r2_hidden(X3,X2) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0)) & ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.87/1.01    inference(flattening,[],[f36])).
% 2.87/1.01  
% 2.87/1.01  fof(f38,plain,(
% 2.87/1.01    ! [X1,X0] : (? [X2] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),X2) & ! [X3] : (((r2_hidden(X3,X2) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0)) & ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1)) & ! [X3] : (((r2_hidden(X3,sK3(X0,X1)) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0)) & ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) | ~r2_hidden(X3,sK3(X0,X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.87/1.01    introduced(choice_axiom,[])).
% 2.87/1.01  
% 2.87/1.01  fof(f39,plain,(
% 2.87/1.01    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1)) & ! [X3] : (((r2_hidden(X3,sK3(X0,X1)) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0)) & ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) | ~r2_hidden(X3,sK3(X0,X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.87/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 2.87/1.01  
% 2.87/1.01  fof(f63,plain,(
% 2.87/1.01    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.87/1.01    inference(cnf_transformation,[],[f39])).
% 2.87/1.01  
% 2.87/1.01  fof(f67,plain,(
% 2.87/1.01    v2_pre_topc(sK4) | v4_pre_topc(sK5,sK4)),
% 2.87/1.01    inference(cnf_transformation,[],[f42])).
% 2.87/1.01  
% 2.87/1.01  fof(f72,plain,(
% 2.87/1.01    ~v4_pre_topc(sK5,sK4) | k2_pre_topc(sK4,sK5) != sK5),
% 2.87/1.01    inference(cnf_transformation,[],[f42])).
% 2.87/1.01  
% 2.87/1.01  fof(f59,plain,(
% 2.87/1.01    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.87/1.01    inference(cnf_transformation,[],[f39])).
% 2.87/1.01  
% 2.87/1.01  fof(f5,axiom,(
% 2.87/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))) => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0))))),
% 2.87/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.87/1.01  
% 2.87/1.01  fof(f15,plain,(
% 2.87/1.01    ! [X0] : (! [X1] : ((v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ? [X2] : ((~v4_pre_topc(X2,X0) & r2_hidden(X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.87/1.01    inference(ennf_transformation,[],[f5])).
% 2.87/1.01  
% 2.87/1.01  fof(f16,plain,(
% 2.87/1.01    ! [X0] : (! [X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.87/1.01    inference(flattening,[],[f15])).
% 2.87/1.01  
% 2.87/1.01  fof(f30,plain,(
% 2.87/1.01    ! [X1,X0] : (? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.87/1.01    introduced(choice_axiom,[])).
% 2.87/1.01  
% 2.87/1.01  fof(f31,plain,(
% 2.87/1.01    ! [X0] : (! [X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | (~v4_pre_topc(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.87/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f30])).
% 2.87/1.01  
% 2.87/1.01  fof(f52,plain,(
% 2.87/1.01    ( ! [X0,X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | r2_hidden(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.87/1.01    inference(cnf_transformation,[],[f31])).
% 2.87/1.01  
% 2.87/1.01  fof(f43,plain,(
% 2.87/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.87/1.01    inference(cnf_transformation,[],[f27])).
% 2.87/1.01  
% 2.87/1.01  fof(f51,plain,(
% 2.87/1.01    ( ! [X0,X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.87/1.01    inference(cnf_transformation,[],[f31])).
% 2.87/1.01  
% 2.87/1.01  fof(f53,plain,(
% 2.87/1.01    ( ! [X0,X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.87/1.01    inference(cnf_transformation,[],[f31])).
% 2.87/1.01  
% 2.87/1.01  fof(f60,plain,(
% 2.87/1.01    ( ! [X0,X3,X1] : (v4_pre_topc(X3,X0) | ~r2_hidden(X3,sK3(X0,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.87/1.01    inference(cnf_transformation,[],[f39])).
% 2.87/1.01  
% 2.87/1.01  cnf(c_28,negated_conjecture,
% 2.87/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.87/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1547,plain,
% 2.87/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.87/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_21,plain,
% 2.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.01      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 2.87/1.01      | ~ l1_pre_topc(X1) ),
% 2.87/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_29,negated_conjecture,
% 2.87/1.01      ( l1_pre_topc(sK4) ),
% 2.87/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_614,plain,
% 2.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.01      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 2.87/1.01      | sK4 != X1 ),
% 2.87/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_615,plain,
% 2.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.01      | r1_tarski(X0,k2_pre_topc(sK4,X0)) ),
% 2.87/1.01      inference(unflattening,[status(thm)],[c_614]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1537,plain,
% 2.87/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.87/1.01      | r1_tarski(X0,k2_pre_topc(sK4,X0)) = iProver_top ),
% 2.87/1.01      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1779,plain,
% 2.87/1.01      ( r1_tarski(sK5,k2_pre_topc(sK4,sK5)) = iProver_top ),
% 2.87/1.01      inference(superposition,[status(thm)],[c_1547,c_1537]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_3,plain,
% 2.87/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.87/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1552,plain,
% 2.87/1.01      ( X0 = X1
% 2.87/1.01      | r1_tarski(X1,X0) != iProver_top
% 2.87/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.87/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_2119,plain,
% 2.87/1.01      ( k2_pre_topc(sK4,sK5) = sK5
% 2.87/1.01      | r1_tarski(k2_pre_topc(sK4,sK5),sK5) != iProver_top ),
% 2.87/1.01      inference(superposition,[status(thm)],[c_1779,c_1552]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_25,negated_conjecture,
% 2.87/1.01      ( v4_pre_topc(sK5,sK4) | k2_pre_topc(sK4,sK5) = sK5 ),
% 2.87/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_617,plain,
% 2.87/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.01      | r1_tarski(sK5,k2_pre_topc(sK4,sK5)) ),
% 2.87/1.01      inference(instantiation,[status(thm)],[c_615]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_7,plain,
% 2.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.01      | ~ l1_pre_topc(X1) ),
% 2.87/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_707,plain,
% 2.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.01      | sK4 != X1 ),
% 2.87/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_29]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_708,plain,
% 2.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.01      | m1_subset_1(k2_pre_topc(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.87/1.01      inference(unflattening,[status(thm)],[c_707]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_710,plain,
% 2.87/1.01      ( m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.87/1.01      inference(instantiation,[status(thm)],[c_708]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1781,plain,
% 2.87/1.01      ( ~ r1_tarski(k2_pre_topc(sK4,sK5),sK5)
% 2.87/1.01      | ~ r1_tarski(sK5,k2_pre_topc(sK4,sK5))
% 2.87/1.01      | k2_pre_topc(sK4,sK5) = sK5 ),
% 2.87/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1,plain,
% 2.87/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.87/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1810,plain,
% 2.87/1.01      ( r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5))
% 2.87/1.01      | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
% 2.87/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_0,plain,
% 2.87/1.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.87/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1809,plain,
% 2.87/1.01      ( ~ r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),sK5)
% 2.87/1.01      | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
% 2.87/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_6,plain,
% 2.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.87/1.01      | ~ r2_hidden(X2,X0)
% 2.87/1.01      | r2_hidden(X2,X1) ),
% 2.87/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_1906,plain,
% 2.87/1.01      ( ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(X0))
% 2.87/1.01      | r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),X0)
% 2.87/1.01      | ~ r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5)) ),
% 2.87/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.87/1.01  
% 2.87/1.01  cnf(c_2097,plain,
% 2.87/1.01      ( ~ m1_subset_1(k2_pre_topc(sK4,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.01      | ~ r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),k2_pre_topc(sK4,sK5))
% 2.87/1.01      | r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),u1_struct_0(sK4)) ),
% 2.87/1.01      inference(instantiation,[status(thm)],[c_1906]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1554,plain,
% 2.87/1.02      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.87/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_15,plain,
% 2.87/1.02      ( ~ v4_pre_topc(X0,X1)
% 2.87/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.02      | r2_hidden(X3,X0)
% 2.87/1.02      | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
% 2.87/1.02      | ~ r2_hidden(X3,u1_struct_0(X1))
% 2.87/1.02      | ~ r1_tarski(X2,X0)
% 2.87/1.02      | ~ l1_pre_topc(X1) ),
% 2.87/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_626,plain,
% 2.87/1.02      ( ~ v4_pre_topc(X0,X1)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.02      | r2_hidden(X3,X0)
% 2.87/1.02      | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
% 2.87/1.02      | ~ r2_hidden(X3,u1_struct_0(X1))
% 2.87/1.02      | ~ r1_tarski(X2,X0)
% 2.87/1.02      | sK4 != X1 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_627,plain,
% 2.87/1.02      ( ~ v4_pre_topc(X0,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | r2_hidden(X2,X0)
% 2.87/1.02      | ~ r2_hidden(X2,k2_pre_topc(sK4,X1))
% 2.87/1.02      | ~ r2_hidden(X2,u1_struct_0(sK4))
% 2.87/1.02      | ~ r1_tarski(X1,X0) ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_626]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1536,plain,
% 2.87/1.02      ( v4_pre_topc(X0,sK4) != iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.87/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.87/1.02      | r2_hidden(X2,X0) = iProver_top
% 2.87/1.02      | r2_hidden(X2,k2_pre_topc(sK4,X1)) != iProver_top
% 2.87/1.02      | r2_hidden(X2,u1_struct_0(sK4)) != iProver_top
% 2.87/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_627]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1841,plain,
% 2.87/1.02      ( v4_pre_topc(sK5,sK4) != iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.87/1.02      | r2_hidden(X1,k2_pre_topc(sK4,X0)) != iProver_top
% 2.87/1.02      | r2_hidden(X1,u1_struct_0(sK4)) != iProver_top
% 2.87/1.02      | r2_hidden(X1,sK5) = iProver_top
% 2.87/1.02      | r1_tarski(X0,sK5) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_1547,c_1536]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2146,plain,
% 2.87/1.02      ( v4_pre_topc(sK5,sK4) != iProver_top
% 2.87/1.02      | r2_hidden(X0,k2_pre_topc(sK4,sK5)) != iProver_top
% 2.87/1.02      | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
% 2.87/1.02      | r2_hidden(X0,sK5) = iProver_top
% 2.87/1.02      | r1_tarski(sK5,sK5) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_1547,c_1841]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_5,plain,
% 2.87/1.02      ( r1_tarski(X0,X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_83,plain,
% 2.87/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_85,plain,
% 2.87/1.02      ( r1_tarski(sK5,sK5) = iProver_top ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_83]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2264,plain,
% 2.87/1.02      ( r2_hidden(X0,sK5) = iProver_top
% 2.87/1.02      | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
% 2.87/1.02      | r2_hidden(X0,k2_pre_topc(sK4,sK5)) != iProver_top
% 2.87/1.02      | v4_pre_topc(sK5,sK4) != iProver_top ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_2146,c_85]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2265,plain,
% 2.87/1.02      ( v4_pre_topc(sK5,sK4) != iProver_top
% 2.87/1.02      | r2_hidden(X0,k2_pre_topc(sK4,sK5)) != iProver_top
% 2.87/1.02      | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
% 2.87/1.02      | r2_hidden(X0,sK5) = iProver_top ),
% 2.87/1.02      inference(renaming,[status(thm)],[c_2264]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2274,plain,
% 2.87/1.02      ( v4_pre_topc(sK5,sK4) != iProver_top
% 2.87/1.02      | r2_hidden(sK0(k2_pre_topc(sK4,sK5),X0),u1_struct_0(sK4)) != iProver_top
% 2.87/1.02      | r2_hidden(sK0(k2_pre_topc(sK4,sK5),X0),sK5) = iProver_top
% 2.87/1.02      | r1_tarski(k2_pre_topc(sK4,sK5),X0) = iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_1554,c_2265]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2275,plain,
% 2.87/1.02      ( ~ v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ r2_hidden(sK0(k2_pre_topc(sK4,sK5),X0),u1_struct_0(sK4))
% 2.87/1.02      | r2_hidden(sK0(k2_pre_topc(sK4,sK5),X0),sK5)
% 2.87/1.02      | r1_tarski(k2_pre_topc(sK4,sK5),X0) ),
% 2.87/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2274]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2277,plain,
% 2.87/1.02      ( ~ v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),u1_struct_0(sK4))
% 2.87/1.02      | r2_hidden(sK0(k2_pre_topc(sK4,sK5),sK5),sK5)
% 2.87/1.02      | r1_tarski(k2_pre_topc(sK4,sK5),sK5) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_2275]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2853,plain,
% 2.87/1.02      ( k2_pre_topc(sK4,sK5) = sK5 ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_2119,c_28,c_25,c_617,c_710,c_1781,c_1810,c_1809,
% 2.87/1.02                 c_2097,c_2277]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_16,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.02      | ~ v2_pre_topc(X1)
% 2.87/1.02      | ~ l1_pre_topc(X1)
% 2.87/1.02      | k6_setfam_1(u1_struct_0(X1),sK3(X1,X0)) = k2_pre_topc(X1,X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_27,negated_conjecture,
% 2.87/1.02      ( v4_pre_topc(sK5,sK4) | v2_pre_topc(sK4) ),
% 2.87/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_533,plain,
% 2.87/1.02      ( v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.02      | ~ l1_pre_topc(X1)
% 2.87/1.02      | k6_setfam_1(u1_struct_0(X1),sK3(X1,X0)) = k2_pre_topc(X1,X0)
% 2.87/1.02      | sK4 != X1 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_534,plain,
% 2.87/1.02      ( v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | ~ l1_pre_topc(sK4)
% 2.87/1.02      | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0) ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_533]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_538,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0) ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_534,c_29]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_539,plain,
% 2.87/1.02      ( v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0) ),
% 2.87/1.02      inference(renaming,[status(thm)],[c_538]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1539,plain,
% 2.87/1.02      ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0)
% 2.87/1.02      | v4_pre_topc(sK5,sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_30,plain,
% 2.87/1.02      ( l1_pre_topc(sK4) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_22,negated_conjecture,
% 2.87/1.02      ( ~ v4_pre_topc(sK5,sK4) | k2_pre_topc(sK4,sK5) != sK5 ),
% 2.87/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_36,plain,
% 2.87/1.02      ( k2_pre_topc(sK4,sK5) != sK5
% 2.87/1.02      | v4_pre_topc(sK5,sK4) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_535,plain,
% 2.87/1.02      ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0)
% 2.87/1.02      | v4_pre_topc(sK5,sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.87/1.02      | l1_pre_topc(sK4) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2279,plain,
% 2.87/1.02      ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)) = k2_pre_topc(sK4,X0)
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_1539,c_30,c_28,c_25,c_36,c_535,c_617,c_710,c_1781,
% 2.87/1.02                 c_1810,c_1809,c_2097,c_2277]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2287,plain,
% 2.87/1.02      ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)) = k2_pre_topc(sK4,sK5) ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_1547,c_2279]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2856,plain,
% 2.87/1.02      ( k6_setfam_1(u1_struct_0(sK4),sK3(sK4,sK5)) = sK5 ),
% 2.87/1.02      inference(demodulation,[status(thm)],[c_2853,c_2287]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_20,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.02      | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.87/1.02      | ~ v2_pre_topc(X1)
% 2.87/1.02      | ~ l1_pre_topc(X1) ),
% 2.87/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_436,plain,
% 2.87/1.02      ( v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.02      | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.87/1.02      | ~ l1_pre_topc(X1)
% 2.87/1.02      | sK4 != X1 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_437,plain,
% 2.87/1.02      ( v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.87/1.02      | ~ l1_pre_topc(sK4) ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_436]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_441,plain,
% 2.87/1.02      ( m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | v4_pre_topc(sK5,sK4) ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_437,c_29]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_442,plain,
% 2.87/1.02      ( v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
% 2.87/1.02      inference(renaming,[status(thm)],[c_441]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1543,plain,
% 2.87/1.02      ( v4_pre_topc(sK5,sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.87/1.02      | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_443,plain,
% 2.87/1.02      ( v4_pre_topc(sK5,sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.87/1.02      | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2334,plain,
% 2.87/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.87/1.02      | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_1543,c_28,c_25,c_36,c_443,c_617,c_710,c_1781,c_1810,
% 2.87/1.02                 c_1809,c_2097,c_2277]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_9,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
% 2.87/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.87/1.02      | r2_hidden(sK1(X0,X1),X1)
% 2.87/1.02      | ~ v2_pre_topc(X0)
% 2.87/1.02      | ~ l1_pre_topc(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_388,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.87/1.02      | r2_hidden(sK1(X0,X1),X1)
% 2.87/1.02      | ~ l1_pre_topc(X0)
% 2.87/1.02      | sK4 != X0 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_389,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.87/1.02      | r2_hidden(sK1(sK4,X0),X0)
% 2.87/1.02      | ~ l1_pre_topc(sK4) ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_388]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_393,plain,
% 2.87/1.02      ( r2_hidden(sK1(sK4,X0),X0)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_389,c_29]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_394,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.87/1.02      | r2_hidden(sK1(sK4,X0),X0) ),
% 2.87/1.02      inference(renaming,[status(thm)],[c_393]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1545,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
% 2.87/1.02      | v4_pre_topc(sK5,sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 2.87/1.02      | r2_hidden(sK1(sK4,X0),X0) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_390,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
% 2.87/1.02      | v4_pre_topc(sK5,sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 2.87/1.02      | r2_hidden(sK1(sK4,X0),X0) = iProver_top
% 2.87/1.02      | l1_pre_topc(sK4) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2409,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 2.87/1.02      | r2_hidden(sK1(sK4,X0),X0) = iProver_top ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_1545,c_30,c_28,c_25,c_36,c_390,c_617,c_710,c_1781,
% 2.87/1.02                 c_1810,c_1809,c_2097,c_2277]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2418,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.87/1.02      | r2_hidden(sK1(sK4,sK3(sK4,X0)),sK3(sK4,X0)) = iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_2334,c_2409]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2,plain,
% 2.87/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.87/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1553,plain,
% 2.87/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.87/1.02      | r2_hidden(X0,X2) = iProver_top
% 2.87/1.02      | r1_tarski(X1,X2) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_6692,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.87/1.02      | r2_hidden(sK1(sK4,sK3(sK4,X0)),X1) = iProver_top
% 2.87/1.02      | r1_tarski(sK3(sK4,X0),X1) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_2418,c_1553]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_8040,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.87/1.02      | r2_hidden(sK1(sK4,sK3(sK4,X0)),X1) = iProver_top
% 2.87/1.02      | r1_tarski(X2,X1) != iProver_top
% 2.87/1.02      | r1_tarski(sK3(sK4,X0),X2) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_6692,c_1553]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_10,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
% 2.87/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.87/1.02      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.87/1.02      | ~ v2_pre_topc(X0)
% 2.87/1.02      | ~ l1_pre_topc(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_364,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.87/1.02      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 2.87/1.02      | ~ l1_pre_topc(X0)
% 2.87/1.02      | sK4 != X0 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_365,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.87/1.02      | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | ~ l1_pre_topc(sK4) ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_364]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_369,plain,
% 2.87/1.02      ( m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_365,c_29]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_370,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.87/1.02      | m1_subset_1(sK1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.87/1.02      inference(renaming,[status(thm)],[c_369]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2342,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4)
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.87/1.02      | m1_subset_1(sK1(sK4,sK3(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_370]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2343,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
% 2.87/1.02      | v4_pre_topc(sK5,sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 2.87/1.02      | m1_subset_1(sK1(sK4,sK3(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_2342]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_8,plain,
% 2.87/1.02      ( ~ v4_pre_topc(sK1(X0,X1),X0)
% 2.87/1.02      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
% 2.87/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.87/1.02      | ~ v2_pre_topc(X0)
% 2.87/1.02      | ~ l1_pre_topc(X0) ),
% 2.87/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_412,plain,
% 2.87/1.02      ( ~ v4_pre_topc(sK1(X0,X1),X0)
% 2.87/1.02      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.87/1.02      | ~ l1_pre_topc(X0)
% 2.87/1.02      | sK4 != X0 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_413,plain,
% 2.87/1.02      ( ~ v4_pre_topc(sK1(sK4,X0),sK4)
% 2.87/1.02      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.87/1.02      | ~ l1_pre_topc(sK4) ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_412]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_417,plain,
% 2.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
% 2.87/1.02      | ~ v4_pre_topc(sK1(sK4,X0),sK4) ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_413,c_29]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_418,plain,
% 2.87/1.02      ( ~ v4_pre_topc(sK1(sK4,X0),sK4)
% 2.87/1.02      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4)
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
% 2.87/1.02      inference(renaming,[status(thm)],[c_417]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_1544,plain,
% 2.87/1.02      ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
% 2.87/1.02      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
% 2.87/1.02      | v4_pre_topc(sK5,sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_419,plain,
% 2.87/1.02      ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
% 2.87/1.02      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
% 2.87/1.02      | v4_pre_topc(sK5,sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2578,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
% 2.87/1.02      | v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_1544,c_28,c_25,c_36,c_419,c_617,c_710,c_1781,c_1810,
% 2.87/1.02                 c_1809,c_2097,c_2277]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2579,plain,
% 2.87/1.02      ( v4_pre_topc(sK1(sK4,X0),sK4) != iProver_top
% 2.87/1.02      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),X0),sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
% 2.87/1.02      inference(renaming,[status(thm)],[c_2578]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_2587,plain,
% 2.87/1.02      ( v4_pre_topc(sK1(sK4,sK3(sK4,X0)),sK4) != iProver_top
% 2.87/1.02      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_2334,c_2579]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_19,plain,
% 2.87/1.02      ( v4_pre_topc(X0,X1)
% 2.87/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.02      | ~ r2_hidden(X0,sK3(X1,X2))
% 2.87/1.02      | ~ v2_pre_topc(X1)
% 2.87/1.02      | ~ l1_pre_topc(X1) ),
% 2.87/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_457,plain,
% 2.87/1.02      ( v4_pre_topc(X0,X1)
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.87/1.02      | ~ r2_hidden(X0,sK3(X1,X2))
% 2.87/1.02      | ~ l1_pre_topc(X1)
% 2.87/1.02      | sK4 != X1 ),
% 2.87/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_458,plain,
% 2.87/1.02      ( v4_pre_topc(X0,sK4)
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | ~ r2_hidden(X0,sK3(sK4,X1))
% 2.87/1.02      | ~ l1_pre_topc(sK4) ),
% 2.87/1.02      inference(unflattening,[status(thm)],[c_457]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_462,plain,
% 2.87/1.02      ( ~ r2_hidden(X0,sK3(sK4,X1))
% 2.87/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | v4_pre_topc(X0,sK4) ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_458,c_29]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_463,plain,
% 2.87/1.02      ( v4_pre_topc(X0,sK4)
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | ~ r2_hidden(X0,sK3(sK4,X1)) ),
% 2.87/1.02      inference(renaming,[status(thm)],[c_462]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_9014,plain,
% 2.87/1.02      ( v4_pre_topc(sK1(sK4,sK3(sK4,X0)),sK4)
% 2.87/1.02      | v4_pre_topc(sK5,sK4)
% 2.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | ~ m1_subset_1(sK1(sK4,sK3(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.87/1.02      | ~ r2_hidden(sK1(sK4,sK3(sK4,X0)),sK3(sK4,X0)) ),
% 2.87/1.02      inference(instantiation,[status(thm)],[c_463]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_9015,plain,
% 2.87/1.02      ( v4_pre_topc(sK1(sK4,sK3(sK4,X0)),sK4) = iProver_top
% 2.87/1.02      | v4_pre_topc(sK5,sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.87/1.02      | m1_subset_1(sK1(sK4,sK3(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.87/1.02      | r2_hidden(sK1(sK4,sK3(sK4,X0)),sK3(sK4,X0)) != iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_9014]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_10229,plain,
% 2.87/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.87/1.02      | v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top ),
% 2.87/1.02      inference(global_propositional_subsumption,
% 2.87/1.02                [status(thm)],
% 2.87/1.02                [c_8040,c_28,c_25,c_36,c_443,c_617,c_710,c_1781,c_1810,
% 2.87/1.02                 c_1809,c_2097,c_2277,c_2343,c_2418,c_2587,c_9015]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_10230,plain,
% 2.87/1.02      ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK4),sK3(sK4,X0)),sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.87/1.02      inference(renaming,[status(thm)],[c_10229]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_10237,plain,
% 2.87/1.02      ( v4_pre_topc(sK5,sK4) = iProver_top
% 2.87/1.02      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.87/1.02      inference(superposition,[status(thm)],[c_2856,c_10230]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(c_31,plain,
% 2.87/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.87/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.87/1.02  
% 2.87/1.02  cnf(contradiction,plain,
% 2.87/1.02      ( $false ),
% 2.87/1.02      inference(minisat,[status(thm)],[c_10237,c_2853,c_36,c_31]) ).
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.87/1.02  
% 2.87/1.02  ------                               Statistics
% 2.87/1.02  
% 2.87/1.02  ------ General
% 2.87/1.02  
% 2.87/1.02  abstr_ref_over_cycles:                  0
% 2.87/1.02  abstr_ref_under_cycles:                 0
% 2.87/1.02  gc_basic_clause_elim:                   0
% 2.87/1.02  forced_gc_time:                         0
% 2.87/1.02  parsing_time:                           0.008
% 2.87/1.02  unif_index_cands_time:                  0.
% 2.87/1.02  unif_index_add_time:                    0.
% 2.87/1.02  orderings_time:                         0.
% 2.87/1.02  out_proof_time:                         0.011
% 2.87/1.02  total_time:                             0.372
% 2.87/1.02  num_of_symbols:                         47
% 2.87/1.02  num_of_terms:                           7305
% 2.87/1.02  
% 2.87/1.02  ------ Preprocessing
% 2.87/1.02  
% 2.87/1.02  num_of_splits:                          0
% 2.87/1.02  num_of_split_atoms:                     0
% 2.87/1.02  num_of_reused_defs:                     0
% 2.87/1.02  num_eq_ax_congr_red:                    24
% 2.87/1.02  num_of_sem_filtered_clauses:            1
% 2.87/1.02  num_of_subtypes:                        0
% 2.87/1.02  monotx_restored_types:                  0
% 2.87/1.02  sat_num_of_epr_types:                   0
% 2.87/1.02  sat_num_of_non_cyclic_types:            0
% 2.87/1.02  sat_guarded_non_collapsed_types:        0
% 2.87/1.02  num_pure_diseq_elim:                    0
% 2.87/1.02  simp_replaced_by:                       0
% 2.87/1.02  res_preprocessed:                       125
% 2.87/1.02  prep_upred:                             0
% 2.87/1.02  prep_unflattend:                        15
% 2.87/1.02  smt_new_axioms:                         0
% 2.87/1.02  pred_elim_cands:                        4
% 2.87/1.02  pred_elim:                              2
% 2.87/1.02  pred_elim_cl:                           2
% 2.87/1.02  pred_elim_cycles:                       4
% 2.87/1.02  merged_defs:                            8
% 2.87/1.02  merged_defs_ncl:                        0
% 2.87/1.02  bin_hyper_res:                          9
% 2.87/1.02  prep_cycles:                            4
% 2.87/1.02  pred_elim_time:                         0.009
% 2.87/1.02  splitting_time:                         0.
% 2.87/1.02  sem_filter_time:                        0.
% 2.87/1.02  monotx_time:                            0.
% 2.87/1.02  subtype_inf_time:                       0.
% 2.87/1.02  
% 2.87/1.02  ------ Problem properties
% 2.87/1.02  
% 2.87/1.02  clauses:                                24
% 2.87/1.02  conjectures:                            3
% 2.87/1.02  epr:                                    3
% 2.87/1.02  horn:                                   11
% 2.87/1.02  ground:                                 3
% 2.87/1.02  unary:                                  2
% 2.87/1.02  binary:                                 6
% 2.87/1.02  lits:                                   80
% 2.87/1.02  lits_eq:                                4
% 2.87/1.02  fd_pure:                                0
% 2.87/1.02  fd_pseudo:                              0
% 2.87/1.02  fd_cond:                                0
% 2.87/1.02  fd_pseudo_cond:                         1
% 2.87/1.02  ac_symbols:                             0
% 2.87/1.02  
% 2.87/1.02  ------ Propositional Solver
% 2.87/1.02  
% 2.87/1.02  prop_solver_calls:                      31
% 2.87/1.02  prop_fast_solver_calls:                 1350
% 2.87/1.02  smt_solver_calls:                       0
% 2.87/1.02  smt_fast_solver_calls:                  0
% 2.87/1.02  prop_num_of_clauses:                    3215
% 2.87/1.02  prop_preprocess_simplified:             7117
% 2.87/1.02  prop_fo_subsumed:                       24
% 2.87/1.02  prop_solver_time:                       0.
% 2.87/1.02  smt_solver_time:                        0.
% 2.87/1.02  smt_fast_solver_time:                   0.
% 2.87/1.02  prop_fast_solver_time:                  0.
% 2.87/1.02  prop_unsat_core_time:                   0.
% 2.87/1.02  
% 2.87/1.02  ------ QBF
% 2.87/1.02  
% 2.87/1.02  qbf_q_res:                              0
% 2.87/1.02  qbf_num_tautologies:                    0
% 2.87/1.02  qbf_prep_cycles:                        0
% 2.87/1.02  
% 2.87/1.02  ------ BMC1
% 2.87/1.02  
% 2.87/1.02  bmc1_current_bound:                     -1
% 2.87/1.02  bmc1_last_solved_bound:                 -1
% 2.87/1.02  bmc1_unsat_core_size:                   -1
% 2.87/1.02  bmc1_unsat_core_parents_size:           -1
% 2.87/1.02  bmc1_merge_next_fun:                    0
% 2.87/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.87/1.02  
% 2.87/1.02  ------ Instantiation
% 2.87/1.02  
% 2.87/1.02  inst_num_of_clauses:                    763
% 2.87/1.02  inst_num_in_passive:                    214
% 2.87/1.02  inst_num_in_active:                     449
% 2.87/1.02  inst_num_in_unprocessed:                100
% 2.87/1.02  inst_num_of_loops:                      630
% 2.87/1.02  inst_num_of_learning_restarts:          0
% 2.87/1.02  inst_num_moves_active_passive:          175
% 2.87/1.02  inst_lit_activity:                      0
% 2.87/1.02  inst_lit_activity_moves:                0
% 2.87/1.02  inst_num_tautologies:                   0
% 2.87/1.02  inst_num_prop_implied:                  0
% 2.87/1.02  inst_num_existing_simplified:           0
% 2.87/1.02  inst_num_eq_res_simplified:             0
% 2.87/1.02  inst_num_child_elim:                    0
% 2.87/1.02  inst_num_of_dismatching_blockings:      401
% 2.87/1.02  inst_num_of_non_proper_insts:           1006
% 2.87/1.02  inst_num_of_duplicates:                 0
% 2.87/1.02  inst_inst_num_from_inst_to_res:         0
% 2.87/1.02  inst_dismatching_checking_time:         0.
% 2.87/1.02  
% 2.87/1.02  ------ Resolution
% 2.87/1.02  
% 2.87/1.02  res_num_of_clauses:                     0
% 2.87/1.02  res_num_in_passive:                     0
% 2.87/1.02  res_num_in_active:                      0
% 2.87/1.02  res_num_of_loops:                       129
% 2.87/1.02  res_forward_subset_subsumed:            100
% 2.87/1.02  res_backward_subset_subsumed:           2
% 2.87/1.02  res_forward_subsumed:                   0
% 2.87/1.02  res_backward_subsumed:                  0
% 2.87/1.02  res_forward_subsumption_resolution:     0
% 2.87/1.02  res_backward_subsumption_resolution:    0
% 2.87/1.02  res_clause_to_clause_subsumption:       3745
% 2.87/1.02  res_orphan_elimination:                 0
% 2.87/1.02  res_tautology_del:                      145
% 2.87/1.02  res_num_eq_res_simplified:              0
% 2.87/1.02  res_num_sel_changes:                    0
% 2.87/1.02  res_moves_from_active_to_pass:          0
% 2.87/1.02  
% 2.87/1.02  ------ Superposition
% 2.87/1.02  
% 2.87/1.02  sup_time_total:                         0.
% 2.87/1.02  sup_time_generating:                    0.
% 2.87/1.02  sup_time_sim_full:                      0.
% 2.87/1.02  sup_time_sim_immed:                     0.
% 2.87/1.02  
% 2.87/1.02  sup_num_of_clauses:                     266
% 2.87/1.02  sup_num_in_active:                      117
% 2.87/1.02  sup_num_in_passive:                     149
% 2.87/1.02  sup_num_of_loops:                       124
% 2.87/1.02  sup_fw_superposition:                   279
% 2.87/1.02  sup_bw_superposition:                   76
% 2.87/1.02  sup_immediate_simplified:               81
% 2.87/1.02  sup_given_eliminated:                   0
% 2.87/1.02  comparisons_done:                       0
% 2.87/1.02  comparisons_avoided:                    0
% 2.87/1.02  
% 2.87/1.02  ------ Simplifications
% 2.87/1.02  
% 2.87/1.02  
% 2.87/1.02  sim_fw_subset_subsumed:                 11
% 2.87/1.02  sim_bw_subset_subsumed:                 16
% 2.87/1.02  sim_fw_subsumed:                        24
% 2.87/1.02  sim_bw_subsumed:                        0
% 2.87/1.02  sim_fw_subsumption_res:                 2
% 2.87/1.02  sim_bw_subsumption_res:                 0
% 2.87/1.02  sim_tautology_del:                      6
% 2.87/1.02  sim_eq_tautology_del:                   41
% 2.87/1.02  sim_eq_res_simp:                        1
% 2.87/1.02  sim_fw_demodulated:                     0
% 2.87/1.02  sim_bw_demodulated:                     4
% 2.87/1.02  sim_light_normalised:                   61
% 2.87/1.02  sim_joinable_taut:                      0
% 2.87/1.02  sim_joinable_simp:                      0
% 2.87/1.02  sim_ac_normalised:                      0
% 2.87/1.02  sim_smt_subsumption:                    0
% 2.87/1.02  
%------------------------------------------------------------------------------
