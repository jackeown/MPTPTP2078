%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:59 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 409 expanded)
%              Number of clauses        :   75 ( 121 expanded)
%              Number of leaves         :   16 ( 114 expanded)
%              Depth                    :   17
%              Number of atoms          :  474 (2415 expanded)
%              Number of equality atoms :  121 ( 387 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                              & v4_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k1_tarski(sK6) != k9_subset_1(u1_struct_0(X0),X1,X3)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK6,X1)
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK5,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(X2,sK5)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & v2_tex_2(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3)
                  | ~ v4_pre_topc(X3,sK4)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & v2_tex_2(X1,sK4)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ! [X3] :
        ( k1_tarski(sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3)
        | ~ v4_pre_topc(X3,sK4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
    & r2_hidden(sK6,sK5)
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & v2_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f30,f51,f50,f49])).

fof(f88,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k2_tarski(X0,X0)) = k2_tarski(X0,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f66,f66])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f85,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v4_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f44])).

fof(f47,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v4_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
                    & v4_pre_topc(sK3(X0,X1,X4),X0)
                    & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f45,f47,f46])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f66])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    ! [X3] :
      ( k1_tarski(sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3)
      | ~ v4_pre_topc(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f94,plain,(
    ! [X3] :
      ( k2_tarski(sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3)
      | ~ v4_pre_topc(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(definition_unfolding,[],[f89,f66])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( v4_pre_topc(sK3(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_31,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2494,plain,
    ( r2_hidden(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_xboole_0(X1,k2_tarski(X0,X0)) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2502,plain,
    ( k3_xboole_0(X0,k2_tarski(X1,X1)) = k2_tarski(X1,X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6643,plain,
    ( k3_xboole_0(sK5,k2_tarski(sK6,sK6)) = k2_tarski(sK6,sK6) ),
    inference(superposition,[status(thm)],[c_2494,c_2502])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2491,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2498,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4194,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2491,c_2498])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_20,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_275,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_276,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_275])).

cnf(c_345,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_17,c_276])).

cnf(c_2489,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_4456,plain,
    ( k9_subset_1(u1_struct_0(sK4),X0,sK5) = k3_xboole_0(X0,sK5) ),
    inference(superposition,[status(thm)],[c_4194,c_2489])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_344,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_276])).

cnf(c_2490,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_5186,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4456,c_2490])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2976,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3447,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2976])).

cnf(c_3455,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3447])).

cnf(c_13735,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5186,c_37,c_3455])).

cnf(c_13742,plain,
    ( m1_subset_1(k3_xboole_0(sK5,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_13735])).

cnf(c_15229,plain,
    ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6643,c_13742])).

cnf(c_27,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK3(X1,X0,X2)) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_585,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | k9_subset_1(u1_struct_0(X1),X0,sK3(X1,X0,X2)) = X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_35])).

cnf(c_586,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_2486,plain,
    ( k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1
    | v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_2932,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
    | v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2491,c_2486])).

cnf(c_33,negated_conjecture,
    ( v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_874,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1
    | sK5 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_586])).

cnf(c_875,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,sK5)
    | k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_874])).

cnf(c_876,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_875])).

cnf(c_3216,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2932,c_37,c_876])).

cnf(c_16307,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k2_tarski(sK6,sK6))) = k2_tarski(sK6,sK6)
    | r1_tarski(k2_tarski(sK6,sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_15229,c_3216])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_tarski(X0,X0),X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2805,plain,
    ( ~ r2_hidden(sK6,sK5)
    | r1_tarski(k2_tarski(sK6,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2837,plain,
    ( r2_hidden(sK6,X0)
    | ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4780,plain,
    ( r2_hidden(sK6,u1_struct_0(sK4))
    | ~ r2_hidden(sK6,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2837])).

cnf(c_3238,plain,
    ( ~ r2_hidden(sK6,X0)
    | r1_tarski(k2_tarski(sK6,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_6233,plain,
    ( ~ r2_hidden(sK6,u1_struct_0(sK4))
    | r1_tarski(k2_tarski(sK6,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3238])).

cnf(c_2777,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_6235,plain,
    ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k2_tarski(sK6,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2777])).

cnf(c_2765,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,sK5)
    | k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_586])).

cnf(c_11618,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k2_tarski(sK6,sK6),sK5)
    | k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k2_tarski(sK6,sK6))) = k2_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_2765])).

cnf(c_16758,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k2_tarski(sK6,sK6))) = k2_tarski(sK6,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16307,c_34,c_33,c_31,c_2805,c_3447,c_4780,c_6233,c_6235,c_11618])).

cnf(c_30,negated_conjecture,
    ( ~ v4_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k2_tarski(sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2495,plain,
    ( k2_tarski(sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X0)
    | v4_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_16761,plain,
    ( v4_pre_topc(sK3(sK4,sK5,k2_tarski(sK6,sK6)),sK4) != iProver_top
    | m1_subset_1(sK3(sK4,sK5,k2_tarski(sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16758,c_2495])).

cnf(c_29,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_564,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_35])).

cnf(c_565,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_564])).

cnf(c_2758,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,sK5,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_11619,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | m1_subset_1(sK3(sK4,sK5,k2_tarski(sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k2_tarski(sK6,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_2758])).

cnf(c_11626,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(sK3(sK4,sK5,k2_tarski(sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k2_tarski(sK6,sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11619])).

cnf(c_6238,plain,
    ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r1_tarski(k2_tarski(sK6,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6235])).

cnf(c_6236,plain,
    ( r2_hidden(sK6,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(k2_tarski(sK6,sK6),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6233])).

cnf(c_4782,plain,
    ( r2_hidden(sK6,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(sK6,sK5) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4780])).

cnf(c_28,plain,
    ( v4_pre_topc(sK3(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_543,plain,
    ( v4_pre_topc(sK3(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_35])).

cnf(c_544,plain,
    ( v4_pre_topc(sK3(sK4,X0,X1),sK4)
    | ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_2755,plain,
    ( v4_pre_topc(sK3(sK4,sK5,X0),sK4)
    | ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_3025,plain,
    ( v4_pre_topc(sK3(sK4,sK5,k2_tarski(sK6,sK6)),sK4)
    | ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k2_tarski(sK6,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_2755])).

cnf(c_3026,plain,
    ( v4_pre_topc(sK3(sK4,sK5,k2_tarski(sK6,sK6)),sK4) = iProver_top
    | v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k2_tarski(sK6,sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3025])).

cnf(c_2806,plain,
    ( r2_hidden(sK6,sK5) != iProver_top
    | r1_tarski(k2_tarski(sK6,sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2805])).

cnf(c_40,plain,
    ( r2_hidden(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_38,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16761,c_11626,c_6238,c_6236,c_4782,c_3455,c_3026,c_2806,c_40,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:24:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 3.62/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.05  
% 3.62/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/1.05  
% 3.62/1.05  ------  iProver source info
% 3.62/1.05  
% 3.62/1.05  git: date: 2020-06-30 10:37:57 +0100
% 3.62/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/1.05  git: non_committed_changes: false
% 3.62/1.05  git: last_make_outside_of_git: false
% 3.62/1.05  
% 3.62/1.05  ------ 
% 3.62/1.05  
% 3.62/1.05  ------ Input Options
% 3.62/1.05  
% 3.62/1.05  --out_options                           all
% 3.62/1.05  --tptp_safe_out                         true
% 3.62/1.05  --problem_path                          ""
% 3.62/1.05  --include_path                          ""
% 3.62/1.05  --clausifier                            res/vclausify_rel
% 3.62/1.05  --clausifier_options                    --mode clausify
% 3.62/1.05  --stdin                                 false
% 3.62/1.05  --stats_out                             all
% 3.62/1.05  
% 3.62/1.05  ------ General Options
% 3.62/1.05  
% 3.62/1.05  --fof                                   false
% 3.62/1.05  --time_out_real                         305.
% 3.62/1.05  --time_out_virtual                      -1.
% 3.62/1.05  --symbol_type_check                     false
% 3.62/1.05  --clausify_out                          false
% 3.62/1.05  --sig_cnt_out                           false
% 3.62/1.05  --trig_cnt_out                          false
% 3.62/1.05  --trig_cnt_out_tolerance                1.
% 3.62/1.05  --trig_cnt_out_sk_spl                   false
% 3.62/1.05  --abstr_cl_out                          false
% 3.62/1.05  
% 3.62/1.05  ------ Global Options
% 3.62/1.05  
% 3.62/1.05  --schedule                              default
% 3.62/1.05  --add_important_lit                     false
% 3.62/1.05  --prop_solver_per_cl                    1000
% 3.62/1.05  --min_unsat_core                        false
% 3.62/1.05  --soft_assumptions                      false
% 3.62/1.05  --soft_lemma_size                       3
% 3.62/1.05  --prop_impl_unit_size                   0
% 3.62/1.05  --prop_impl_unit                        []
% 3.62/1.05  --share_sel_clauses                     true
% 3.62/1.05  --reset_solvers                         false
% 3.62/1.05  --bc_imp_inh                            [conj_cone]
% 3.62/1.05  --conj_cone_tolerance                   3.
% 3.62/1.05  --extra_neg_conj                        none
% 3.62/1.05  --large_theory_mode                     true
% 3.62/1.05  --prolific_symb_bound                   200
% 3.62/1.05  --lt_threshold                          2000
% 3.62/1.05  --clause_weak_htbl                      true
% 3.62/1.05  --gc_record_bc_elim                     false
% 3.62/1.05  
% 3.62/1.05  ------ Preprocessing Options
% 3.62/1.05  
% 3.62/1.05  --preprocessing_flag                    true
% 3.62/1.05  --time_out_prep_mult                    0.1
% 3.62/1.05  --splitting_mode                        input
% 3.62/1.05  --splitting_grd                         true
% 3.62/1.05  --splitting_cvd                         false
% 3.62/1.05  --splitting_cvd_svl                     false
% 3.62/1.05  --splitting_nvd                         32
% 3.62/1.05  --sub_typing                            true
% 3.62/1.05  --prep_gs_sim                           true
% 3.62/1.05  --prep_unflatten                        true
% 3.62/1.05  --prep_res_sim                          true
% 3.62/1.05  --prep_upred                            true
% 3.62/1.05  --prep_sem_filter                       exhaustive
% 3.62/1.05  --prep_sem_filter_out                   false
% 3.62/1.05  --pred_elim                             true
% 3.62/1.05  --res_sim_input                         true
% 3.62/1.05  --eq_ax_congr_red                       true
% 3.62/1.05  --pure_diseq_elim                       true
% 3.62/1.05  --brand_transform                       false
% 3.62/1.05  --non_eq_to_eq                          false
% 3.62/1.05  --prep_def_merge                        true
% 3.62/1.05  --prep_def_merge_prop_impl              false
% 3.62/1.05  --prep_def_merge_mbd                    true
% 3.62/1.05  --prep_def_merge_tr_red                 false
% 3.62/1.05  --prep_def_merge_tr_cl                  false
% 3.62/1.05  --smt_preprocessing                     true
% 3.62/1.05  --smt_ac_axioms                         fast
% 3.62/1.05  --preprocessed_out                      false
% 3.62/1.05  --preprocessed_stats                    false
% 3.62/1.05  
% 3.62/1.05  ------ Abstraction refinement Options
% 3.62/1.05  
% 3.62/1.05  --abstr_ref                             []
% 3.62/1.05  --abstr_ref_prep                        false
% 3.62/1.05  --abstr_ref_until_sat                   false
% 3.62/1.05  --abstr_ref_sig_restrict                funpre
% 3.62/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/1.05  --abstr_ref_under                       []
% 3.62/1.05  
% 3.62/1.05  ------ SAT Options
% 3.62/1.05  
% 3.62/1.05  --sat_mode                              false
% 3.62/1.05  --sat_fm_restart_options                ""
% 3.62/1.05  --sat_gr_def                            false
% 3.62/1.05  --sat_epr_types                         true
% 3.62/1.05  --sat_non_cyclic_types                  false
% 3.62/1.05  --sat_finite_models                     false
% 3.62/1.05  --sat_fm_lemmas                         false
% 3.62/1.05  --sat_fm_prep                           false
% 3.62/1.05  --sat_fm_uc_incr                        true
% 3.62/1.05  --sat_out_model                         small
% 3.62/1.05  --sat_out_clauses                       false
% 3.62/1.05  
% 3.62/1.05  ------ QBF Options
% 3.62/1.05  
% 3.62/1.05  --qbf_mode                              false
% 3.62/1.05  --qbf_elim_univ                         false
% 3.62/1.05  --qbf_dom_inst                          none
% 3.62/1.05  --qbf_dom_pre_inst                      false
% 3.62/1.05  --qbf_sk_in                             false
% 3.62/1.05  --qbf_pred_elim                         true
% 3.62/1.05  --qbf_split                             512
% 3.62/1.05  
% 3.62/1.05  ------ BMC1 Options
% 3.62/1.05  
% 3.62/1.05  --bmc1_incremental                      false
% 3.62/1.05  --bmc1_axioms                           reachable_all
% 3.62/1.05  --bmc1_min_bound                        0
% 3.62/1.05  --bmc1_max_bound                        -1
% 3.62/1.05  --bmc1_max_bound_default                -1
% 3.62/1.05  --bmc1_symbol_reachability              true
% 3.62/1.05  --bmc1_property_lemmas                  false
% 3.62/1.05  --bmc1_k_induction                      false
% 3.62/1.05  --bmc1_non_equiv_states                 false
% 3.62/1.05  --bmc1_deadlock                         false
% 3.62/1.05  --bmc1_ucm                              false
% 3.62/1.05  --bmc1_add_unsat_core                   none
% 3.62/1.05  --bmc1_unsat_core_children              false
% 3.62/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/1.05  --bmc1_out_stat                         full
% 3.62/1.05  --bmc1_ground_init                      false
% 3.62/1.05  --bmc1_pre_inst_next_state              false
% 3.62/1.05  --bmc1_pre_inst_state                   false
% 3.62/1.05  --bmc1_pre_inst_reach_state             false
% 3.62/1.05  --bmc1_out_unsat_core                   false
% 3.62/1.05  --bmc1_aig_witness_out                  false
% 3.62/1.05  --bmc1_verbose                          false
% 3.62/1.05  --bmc1_dump_clauses_tptp                false
% 3.62/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.62/1.05  --bmc1_dump_file                        -
% 3.62/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.62/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.62/1.05  --bmc1_ucm_extend_mode                  1
% 3.62/1.05  --bmc1_ucm_init_mode                    2
% 3.62/1.05  --bmc1_ucm_cone_mode                    none
% 3.62/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.62/1.05  --bmc1_ucm_relax_model                  4
% 3.62/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.62/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/1.05  --bmc1_ucm_layered_model                none
% 3.62/1.05  --bmc1_ucm_max_lemma_size               10
% 3.62/1.05  
% 3.62/1.05  ------ AIG Options
% 3.62/1.05  
% 3.62/1.05  --aig_mode                              false
% 3.62/1.05  
% 3.62/1.05  ------ Instantiation Options
% 3.62/1.05  
% 3.62/1.05  --instantiation_flag                    true
% 3.62/1.05  --inst_sos_flag                         false
% 3.62/1.05  --inst_sos_phase                        true
% 3.62/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/1.05  --inst_lit_sel_side                     num_symb
% 3.62/1.05  --inst_solver_per_active                1400
% 3.62/1.05  --inst_solver_calls_frac                1.
% 3.62/1.05  --inst_passive_queue_type               priority_queues
% 3.62/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/1.05  --inst_passive_queues_freq              [25;2]
% 3.62/1.05  --inst_dismatching                      true
% 3.62/1.05  --inst_eager_unprocessed_to_passive     true
% 3.62/1.05  --inst_prop_sim_given                   true
% 3.62/1.05  --inst_prop_sim_new                     false
% 3.62/1.05  --inst_subs_new                         false
% 3.62/1.05  --inst_eq_res_simp                      false
% 3.62/1.05  --inst_subs_given                       false
% 3.62/1.05  --inst_orphan_elimination               true
% 3.62/1.05  --inst_learning_loop_flag               true
% 3.62/1.05  --inst_learning_start                   3000
% 3.62/1.05  --inst_learning_factor                  2
% 3.62/1.05  --inst_start_prop_sim_after_learn       3
% 3.62/1.05  --inst_sel_renew                        solver
% 3.62/1.05  --inst_lit_activity_flag                true
% 3.62/1.05  --inst_restr_to_given                   false
% 3.62/1.05  --inst_activity_threshold               500
% 3.62/1.05  --inst_out_proof                        true
% 3.62/1.05  
% 3.62/1.05  ------ Resolution Options
% 3.62/1.05  
% 3.62/1.05  --resolution_flag                       true
% 3.62/1.05  --res_lit_sel                           adaptive
% 3.62/1.05  --res_lit_sel_side                      none
% 3.62/1.05  --res_ordering                          kbo
% 3.62/1.05  --res_to_prop_solver                    active
% 3.62/1.05  --res_prop_simpl_new                    false
% 3.62/1.05  --res_prop_simpl_given                  true
% 3.62/1.05  --res_passive_queue_type                priority_queues
% 3.62/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/1.05  --res_passive_queues_freq               [15;5]
% 3.62/1.05  --res_forward_subs                      full
% 3.62/1.05  --res_backward_subs                     full
% 3.62/1.05  --res_forward_subs_resolution           true
% 3.62/1.05  --res_backward_subs_resolution          true
% 3.62/1.05  --res_orphan_elimination                true
% 3.62/1.05  --res_time_limit                        2.
% 3.62/1.05  --res_out_proof                         true
% 3.62/1.05  
% 3.62/1.05  ------ Superposition Options
% 3.62/1.05  
% 3.62/1.05  --superposition_flag                    true
% 3.62/1.05  --sup_passive_queue_type                priority_queues
% 3.62/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.62/1.05  --demod_completeness_check              fast
% 3.62/1.05  --demod_use_ground                      true
% 3.62/1.05  --sup_to_prop_solver                    passive
% 3.62/1.05  --sup_prop_simpl_new                    true
% 3.62/1.05  --sup_prop_simpl_given                  true
% 3.62/1.05  --sup_fun_splitting                     false
% 3.62/1.05  --sup_smt_interval                      50000
% 3.62/1.05  
% 3.62/1.05  ------ Superposition Simplification Setup
% 3.62/1.05  
% 3.62/1.05  --sup_indices_passive                   []
% 3.62/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.05  --sup_full_bw                           [BwDemod]
% 3.62/1.05  --sup_immed_triv                        [TrivRules]
% 3.62/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.05  --sup_immed_bw_main                     []
% 3.62/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.05  
% 3.62/1.05  ------ Combination Options
% 3.62/1.05  
% 3.62/1.05  --comb_res_mult                         3
% 3.62/1.05  --comb_sup_mult                         2
% 3.62/1.05  --comb_inst_mult                        10
% 3.62/1.05  
% 3.62/1.05  ------ Debug Options
% 3.62/1.05  
% 3.62/1.05  --dbg_backtrace                         false
% 3.62/1.05  --dbg_dump_prop_clauses                 false
% 3.62/1.05  --dbg_dump_prop_clauses_file            -
% 3.62/1.05  --dbg_out_stat                          false
% 3.62/1.05  ------ Parsing...
% 3.62/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/1.05  
% 3.62/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.62/1.05  
% 3.62/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/1.05  
% 3.62/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/1.05  ------ Proving...
% 3.62/1.05  ------ Problem Properties 
% 3.62/1.05  
% 3.62/1.05  
% 3.62/1.05  clauses                                 34
% 3.62/1.05  conjectures                             5
% 3.62/1.05  EPR                                     6
% 3.62/1.05  Horn                                    28
% 3.62/1.05  unary                                   9
% 3.62/1.05  binary                                  10
% 3.62/1.05  lits                                    83
% 3.62/1.05  lits eq                                 17
% 3.62/1.05  fd_pure                                 0
% 3.62/1.05  fd_pseudo                               0
% 3.62/1.05  fd_cond                                 1
% 3.62/1.05  fd_pseudo_cond                          4
% 3.62/1.05  AC symbols                              0
% 3.62/1.05  
% 3.62/1.05  ------ Schedule dynamic 5 is on 
% 3.62/1.05  
% 3.62/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.62/1.05  
% 3.62/1.05  
% 3.62/1.05  ------ 
% 3.62/1.05  Current options:
% 3.62/1.05  ------ 
% 3.62/1.05  
% 3.62/1.05  ------ Input Options
% 3.62/1.05  
% 3.62/1.05  --out_options                           all
% 3.62/1.05  --tptp_safe_out                         true
% 3.62/1.05  --problem_path                          ""
% 3.62/1.05  --include_path                          ""
% 3.62/1.05  --clausifier                            res/vclausify_rel
% 3.62/1.05  --clausifier_options                    --mode clausify
% 3.62/1.05  --stdin                                 false
% 3.62/1.05  --stats_out                             all
% 3.62/1.05  
% 3.62/1.05  ------ General Options
% 3.62/1.05  
% 3.62/1.05  --fof                                   false
% 3.62/1.05  --time_out_real                         305.
% 3.62/1.05  --time_out_virtual                      -1.
% 3.62/1.05  --symbol_type_check                     false
% 3.62/1.05  --clausify_out                          false
% 3.62/1.05  --sig_cnt_out                           false
% 3.62/1.05  --trig_cnt_out                          false
% 3.62/1.05  --trig_cnt_out_tolerance                1.
% 3.62/1.05  --trig_cnt_out_sk_spl                   false
% 3.62/1.05  --abstr_cl_out                          false
% 3.62/1.05  
% 3.62/1.05  ------ Global Options
% 3.62/1.05  
% 3.62/1.05  --schedule                              default
% 3.62/1.05  --add_important_lit                     false
% 3.62/1.05  --prop_solver_per_cl                    1000
% 3.62/1.05  --min_unsat_core                        false
% 3.62/1.05  --soft_assumptions                      false
% 3.62/1.05  --soft_lemma_size                       3
% 3.62/1.05  --prop_impl_unit_size                   0
% 3.62/1.05  --prop_impl_unit                        []
% 3.62/1.05  --share_sel_clauses                     true
% 3.62/1.05  --reset_solvers                         false
% 3.62/1.05  --bc_imp_inh                            [conj_cone]
% 3.62/1.05  --conj_cone_tolerance                   3.
% 3.62/1.05  --extra_neg_conj                        none
% 3.62/1.05  --large_theory_mode                     true
% 3.62/1.05  --prolific_symb_bound                   200
% 3.62/1.05  --lt_threshold                          2000
% 3.62/1.05  --clause_weak_htbl                      true
% 3.62/1.05  --gc_record_bc_elim                     false
% 3.62/1.05  
% 3.62/1.05  ------ Preprocessing Options
% 3.62/1.05  
% 3.62/1.05  --preprocessing_flag                    true
% 3.62/1.05  --time_out_prep_mult                    0.1
% 3.62/1.05  --splitting_mode                        input
% 3.62/1.05  --splitting_grd                         true
% 3.62/1.05  --splitting_cvd                         false
% 3.62/1.05  --splitting_cvd_svl                     false
% 3.62/1.05  --splitting_nvd                         32
% 3.62/1.05  --sub_typing                            true
% 3.62/1.05  --prep_gs_sim                           true
% 3.62/1.05  --prep_unflatten                        true
% 3.62/1.05  --prep_res_sim                          true
% 3.62/1.05  --prep_upred                            true
% 3.62/1.05  --prep_sem_filter                       exhaustive
% 3.62/1.05  --prep_sem_filter_out                   false
% 3.62/1.05  --pred_elim                             true
% 3.62/1.05  --res_sim_input                         true
% 3.62/1.05  --eq_ax_congr_red                       true
% 3.62/1.05  --pure_diseq_elim                       true
% 3.62/1.05  --brand_transform                       false
% 3.62/1.05  --non_eq_to_eq                          false
% 3.62/1.05  --prep_def_merge                        true
% 3.62/1.05  --prep_def_merge_prop_impl              false
% 3.62/1.05  --prep_def_merge_mbd                    true
% 3.62/1.05  --prep_def_merge_tr_red                 false
% 3.62/1.05  --prep_def_merge_tr_cl                  false
% 3.62/1.05  --smt_preprocessing                     true
% 3.62/1.05  --smt_ac_axioms                         fast
% 3.62/1.05  --preprocessed_out                      false
% 3.62/1.05  --preprocessed_stats                    false
% 3.62/1.05  
% 3.62/1.05  ------ Abstraction refinement Options
% 3.62/1.05  
% 3.62/1.05  --abstr_ref                             []
% 3.62/1.05  --abstr_ref_prep                        false
% 3.62/1.05  --abstr_ref_until_sat                   false
% 3.62/1.05  --abstr_ref_sig_restrict                funpre
% 3.62/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/1.05  --abstr_ref_under                       []
% 3.62/1.05  
% 3.62/1.05  ------ SAT Options
% 3.62/1.05  
% 3.62/1.05  --sat_mode                              false
% 3.62/1.05  --sat_fm_restart_options                ""
% 3.62/1.05  --sat_gr_def                            false
% 3.62/1.05  --sat_epr_types                         true
% 3.62/1.05  --sat_non_cyclic_types                  false
% 3.62/1.05  --sat_finite_models                     false
% 3.62/1.05  --sat_fm_lemmas                         false
% 3.62/1.05  --sat_fm_prep                           false
% 3.62/1.05  --sat_fm_uc_incr                        true
% 3.62/1.05  --sat_out_model                         small
% 3.62/1.05  --sat_out_clauses                       false
% 3.62/1.05  
% 3.62/1.05  ------ QBF Options
% 3.62/1.05  
% 3.62/1.05  --qbf_mode                              false
% 3.62/1.05  --qbf_elim_univ                         false
% 3.62/1.05  --qbf_dom_inst                          none
% 3.62/1.05  --qbf_dom_pre_inst                      false
% 3.62/1.05  --qbf_sk_in                             false
% 3.62/1.05  --qbf_pred_elim                         true
% 3.62/1.05  --qbf_split                             512
% 3.62/1.05  
% 3.62/1.05  ------ BMC1 Options
% 3.62/1.05  
% 3.62/1.05  --bmc1_incremental                      false
% 3.62/1.05  --bmc1_axioms                           reachable_all
% 3.62/1.05  --bmc1_min_bound                        0
% 3.62/1.05  --bmc1_max_bound                        -1
% 3.62/1.05  --bmc1_max_bound_default                -1
% 3.62/1.05  --bmc1_symbol_reachability              true
% 3.62/1.05  --bmc1_property_lemmas                  false
% 3.62/1.05  --bmc1_k_induction                      false
% 3.62/1.05  --bmc1_non_equiv_states                 false
% 3.62/1.05  --bmc1_deadlock                         false
% 3.62/1.05  --bmc1_ucm                              false
% 3.62/1.05  --bmc1_add_unsat_core                   none
% 3.62/1.05  --bmc1_unsat_core_children              false
% 3.62/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/1.05  --bmc1_out_stat                         full
% 3.62/1.05  --bmc1_ground_init                      false
% 3.62/1.05  --bmc1_pre_inst_next_state              false
% 3.62/1.05  --bmc1_pre_inst_state                   false
% 3.62/1.05  --bmc1_pre_inst_reach_state             false
% 3.62/1.05  --bmc1_out_unsat_core                   false
% 3.62/1.05  --bmc1_aig_witness_out                  false
% 3.62/1.05  --bmc1_verbose                          false
% 3.62/1.05  --bmc1_dump_clauses_tptp                false
% 3.62/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.62/1.05  --bmc1_dump_file                        -
% 3.62/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.62/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.62/1.05  --bmc1_ucm_extend_mode                  1
% 3.62/1.05  --bmc1_ucm_init_mode                    2
% 3.62/1.05  --bmc1_ucm_cone_mode                    none
% 3.62/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.62/1.05  --bmc1_ucm_relax_model                  4
% 3.62/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.62/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/1.05  --bmc1_ucm_layered_model                none
% 3.62/1.05  --bmc1_ucm_max_lemma_size               10
% 3.62/1.05  
% 3.62/1.05  ------ AIG Options
% 3.62/1.05  
% 3.62/1.05  --aig_mode                              false
% 3.62/1.05  
% 3.62/1.05  ------ Instantiation Options
% 3.62/1.05  
% 3.62/1.05  --instantiation_flag                    true
% 3.62/1.05  --inst_sos_flag                         false
% 3.62/1.05  --inst_sos_phase                        true
% 3.62/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/1.05  --inst_lit_sel_side                     none
% 3.62/1.05  --inst_solver_per_active                1400
% 3.62/1.05  --inst_solver_calls_frac                1.
% 3.62/1.05  --inst_passive_queue_type               priority_queues
% 3.62/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/1.05  --inst_passive_queues_freq              [25;2]
% 3.62/1.05  --inst_dismatching                      true
% 3.62/1.05  --inst_eager_unprocessed_to_passive     true
% 3.62/1.05  --inst_prop_sim_given                   true
% 3.62/1.05  --inst_prop_sim_new                     false
% 3.62/1.05  --inst_subs_new                         false
% 3.62/1.05  --inst_eq_res_simp                      false
% 3.62/1.05  --inst_subs_given                       false
% 3.62/1.05  --inst_orphan_elimination               true
% 3.62/1.05  --inst_learning_loop_flag               true
% 3.62/1.05  --inst_learning_start                   3000
% 3.62/1.05  --inst_learning_factor                  2
% 3.62/1.05  --inst_start_prop_sim_after_learn       3
% 3.62/1.05  --inst_sel_renew                        solver
% 3.62/1.05  --inst_lit_activity_flag                true
% 3.62/1.05  --inst_restr_to_given                   false
% 3.62/1.05  --inst_activity_threshold               500
% 3.62/1.05  --inst_out_proof                        true
% 3.62/1.05  
% 3.62/1.05  ------ Resolution Options
% 3.62/1.05  
% 3.62/1.05  --resolution_flag                       false
% 3.62/1.05  --res_lit_sel                           adaptive
% 3.62/1.05  --res_lit_sel_side                      none
% 3.62/1.05  --res_ordering                          kbo
% 3.62/1.05  --res_to_prop_solver                    active
% 3.62/1.05  --res_prop_simpl_new                    false
% 3.62/1.05  --res_prop_simpl_given                  true
% 3.62/1.05  --res_passive_queue_type                priority_queues
% 3.62/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/1.05  --res_passive_queues_freq               [15;5]
% 3.62/1.05  --res_forward_subs                      full
% 3.62/1.05  --res_backward_subs                     full
% 3.62/1.05  --res_forward_subs_resolution           true
% 3.62/1.05  --res_backward_subs_resolution          true
% 3.62/1.05  --res_orphan_elimination                true
% 3.62/1.05  --res_time_limit                        2.
% 3.62/1.05  --res_out_proof                         true
% 3.62/1.05  
% 3.62/1.05  ------ Superposition Options
% 3.62/1.05  
% 3.62/1.05  --superposition_flag                    true
% 3.62/1.05  --sup_passive_queue_type                priority_queues
% 3.62/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.62/1.05  --demod_completeness_check              fast
% 3.62/1.05  --demod_use_ground                      true
% 3.62/1.05  --sup_to_prop_solver                    passive
% 3.62/1.05  --sup_prop_simpl_new                    true
% 3.62/1.05  --sup_prop_simpl_given                  true
% 3.62/1.05  --sup_fun_splitting                     false
% 3.62/1.05  --sup_smt_interval                      50000
% 3.62/1.05  
% 3.62/1.05  ------ Superposition Simplification Setup
% 3.62/1.05  
% 3.62/1.05  --sup_indices_passive                   []
% 3.62/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.05  --sup_full_bw                           [BwDemod]
% 3.62/1.05  --sup_immed_triv                        [TrivRules]
% 3.62/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.05  --sup_immed_bw_main                     []
% 3.62/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.05  
% 3.62/1.05  ------ Combination Options
% 3.62/1.05  
% 3.62/1.05  --comb_res_mult                         3
% 3.62/1.05  --comb_sup_mult                         2
% 3.62/1.05  --comb_inst_mult                        10
% 3.62/1.05  
% 3.62/1.05  ------ Debug Options
% 3.62/1.05  
% 3.62/1.05  --dbg_backtrace                         false
% 3.62/1.05  --dbg_dump_prop_clauses                 false
% 3.62/1.05  --dbg_dump_prop_clauses_file            -
% 3.62/1.05  --dbg_out_stat                          false
% 3.62/1.05  
% 3.62/1.05  
% 3.62/1.05  
% 3.62/1.05  
% 3.62/1.05  ------ Proving...
% 3.62/1.05  
% 3.62/1.05  
% 3.62/1.05  % SZS status Theorem for theBenchmark.p
% 3.62/1.05  
% 3.62/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/1.05  
% 3.62/1.05  fof(f16,conjecture,(
% 3.62/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 3.62/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f17,negated_conjecture,(
% 3.62/1.05    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 3.62/1.05    inference(negated_conjecture,[],[f16])).
% 3.62/1.05  
% 3.62/1.05  fof(f29,plain,(
% 3.62/1.05    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.62/1.05    inference(ennf_transformation,[],[f17])).
% 3.62/1.05  
% 3.62/1.05  fof(f30,plain,(
% 3.62/1.05    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.62/1.05    inference(flattening,[],[f29])).
% 3.62/1.05  
% 3.62/1.05  fof(f51,plain,(
% 3.62/1.05    ( ! [X0,X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k1_tarski(sK6) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK6,X1) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 3.62/1.05    introduced(choice_axiom,[])).
% 3.62/1.05  
% 3.62/1.05  fof(f50,plain,(
% 3.62/1.05    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK5,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK5) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.62/1.05    introduced(choice_axiom,[])).
% 3.62/1.05  
% 3.62/1.05  fof(f49,plain,(
% 3.62/1.05    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK4))) & v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4))),
% 3.62/1.05    introduced(choice_axiom,[])).
% 3.62/1.05  
% 3.62/1.05  fof(f52,plain,(
% 3.62/1.05    ((! [X3] : (k1_tarski(sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(sK6,sK5) & m1_subset_1(sK6,u1_struct_0(sK4))) & v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4)),
% 3.62/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f30,f51,f50,f49])).
% 3.62/1.05  
% 3.62/1.05  fof(f88,plain,(
% 3.62/1.05    r2_hidden(sK6,sK5)),
% 3.62/1.05    inference(cnf_transformation,[],[f52])).
% 3.62/1.05  
% 3.62/1.05  fof(f7,axiom,(
% 3.62/1.05    ! [X0,X1] : (r2_hidden(X0,X1) => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0))),
% 3.62/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f19,plain,(
% 3.62/1.05    ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1))),
% 3.62/1.05    inference(ennf_transformation,[],[f7])).
% 3.62/1.05  
% 3.62/1.05  fof(f69,plain,(
% 3.62/1.05    ( ! [X0,X1] : (k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) | ~r2_hidden(X0,X1)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f19])).
% 3.62/1.05  
% 3.62/1.05  fof(f5,axiom,(
% 3.62/1.05    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.62/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f66,plain,(
% 3.62/1.05    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f5])).
% 3.62/1.05  
% 3.62/1.05  fof(f92,plain,(
% 3.62/1.05    ( ! [X0,X1] : (k3_xboole_0(X1,k2_tarski(X0,X0)) = k2_tarski(X0,X0) | ~r2_hidden(X0,X1)) )),
% 3.62/1.05    inference(definition_unfolding,[],[f69,f66,f66])).
% 3.62/1.05  
% 3.62/1.05  fof(f1,axiom,(
% 3.62/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.62/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f53,plain,(
% 3.62/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f1])).
% 3.62/1.05  
% 3.62/1.05  fof(f85,plain,(
% 3.62/1.05    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 3.62/1.05    inference(cnf_transformation,[],[f52])).
% 3.62/1.05  
% 3.62/1.05  fof(f12,axiom,(
% 3.62/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.62/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f43,plain,(
% 3.62/1.05    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.62/1.05    inference(nnf_transformation,[],[f12])).
% 3.62/1.05  
% 3.62/1.05  fof(f74,plain,(
% 3.62/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.62/1.05    inference(cnf_transformation,[],[f43])).
% 3.62/1.05  
% 3.62/1.05  fof(f9,axiom,(
% 3.62/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.62/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f21,plain,(
% 3.62/1.05    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.62/1.05    inference(ennf_transformation,[],[f9])).
% 3.62/1.05  
% 3.62/1.05  fof(f71,plain,(
% 3.62/1.05    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.62/1.05    inference(cnf_transformation,[],[f21])).
% 3.62/1.05  
% 3.62/1.05  fof(f75,plain,(
% 3.62/1.05    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f43])).
% 3.62/1.05  
% 3.62/1.05  fof(f8,axiom,(
% 3.62/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.62/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f20,plain,(
% 3.62/1.05    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.62/1.05    inference(ennf_transformation,[],[f8])).
% 3.62/1.05  
% 3.62/1.05  fof(f70,plain,(
% 3.62/1.05    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.62/1.05    inference(cnf_transformation,[],[f20])).
% 3.62/1.05  
% 3.62/1.05  fof(f15,axiom,(
% 3.62/1.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 3.62/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f27,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/1.05    inference(ennf_transformation,[],[f15])).
% 3.62/1.05  
% 3.62/1.05  fof(f28,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/1.05    inference(flattening,[],[f27])).
% 3.62/1.05  
% 3.62/1.05  fof(f44,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/1.05    inference(nnf_transformation,[],[f28])).
% 3.62/1.05  
% 3.62/1.05  fof(f45,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/1.05    inference(rectify,[],[f44])).
% 3.62/1.05  
% 3.62/1.05  fof(f47,plain,(
% 3.62/1.05    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v4_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.62/1.05    introduced(choice_axiom,[])).
% 3.62/1.05  
% 3.62/1.05  fof(f46,plain,(
% 3.62/1.05    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.62/1.05    introduced(choice_axiom,[])).
% 3.62/1.05  
% 3.62/1.05  fof(f48,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v4_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f45,f47,f46])).
% 3.62/1.05  
% 3.62/1.05  fof(f80,plain,(
% 3.62/1.05    ( ! [X4,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f48])).
% 3.62/1.05  
% 3.62/1.05  fof(f84,plain,(
% 3.62/1.05    l1_pre_topc(sK4)),
% 3.62/1.05    inference(cnf_transformation,[],[f52])).
% 3.62/1.05  
% 3.62/1.05  fof(f86,plain,(
% 3.62/1.05    v2_tex_2(sK5,sK4)),
% 3.62/1.05    inference(cnf_transformation,[],[f52])).
% 3.62/1.05  
% 3.62/1.05  fof(f6,axiom,(
% 3.62/1.05    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.62/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f42,plain,(
% 3.62/1.05    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.62/1.05    inference(nnf_transformation,[],[f6])).
% 3.62/1.05  
% 3.62/1.05  fof(f68,plain,(
% 3.62/1.05    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f42])).
% 3.62/1.05  
% 3.62/1.05  fof(f90,plain,(
% 3.62/1.05    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.62/1.05    inference(definition_unfolding,[],[f68,f66])).
% 3.62/1.05  
% 3.62/1.05  fof(f2,axiom,(
% 3.62/1.05    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.62/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f18,plain,(
% 3.62/1.05    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.62/1.05    inference(ennf_transformation,[],[f2])).
% 3.62/1.05  
% 3.62/1.05  fof(f31,plain,(
% 3.62/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.62/1.05    inference(nnf_transformation,[],[f18])).
% 3.62/1.05  
% 3.62/1.05  fof(f32,plain,(
% 3.62/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.62/1.05    inference(rectify,[],[f31])).
% 3.62/1.05  
% 3.62/1.05  fof(f33,plain,(
% 3.62/1.05    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.62/1.05    introduced(choice_axiom,[])).
% 3.62/1.05  
% 3.62/1.05  fof(f34,plain,(
% 3.62/1.05    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.62/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 3.62/1.05  
% 3.62/1.05  fof(f54,plain,(
% 3.62/1.05    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f34])).
% 3.62/1.05  
% 3.62/1.05  fof(f89,plain,(
% 3.62/1.05    ( ! [X3] : (k1_tarski(sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) )),
% 3.62/1.05    inference(cnf_transformation,[],[f52])).
% 3.62/1.05  
% 3.62/1.05  fof(f94,plain,(
% 3.62/1.05    ( ! [X3] : (k2_tarski(sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) )),
% 3.62/1.05    inference(definition_unfolding,[],[f89,f66])).
% 3.62/1.05  
% 3.62/1.05  fof(f78,plain,(
% 3.62/1.05    ( ! [X4,X0,X1] : (m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f48])).
% 3.62/1.05  
% 3.62/1.05  fof(f79,plain,(
% 3.62/1.05    ( ! [X4,X0,X1] : (v4_pre_topc(sK3(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f48])).
% 3.62/1.05  
% 3.62/1.05  cnf(c_31,negated_conjecture,
% 3.62/1.05      ( r2_hidden(sK6,sK5) ),
% 3.62/1.05      inference(cnf_transformation,[],[f88]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2494,plain,
% 3.62/1.05      ( r2_hidden(sK6,sK5) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_15,plain,
% 3.62/1.05      ( ~ r2_hidden(X0,X1)
% 3.62/1.05      | k3_xboole_0(X1,k2_tarski(X0,X0)) = k2_tarski(X0,X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f92]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2502,plain,
% 3.62/1.05      ( k3_xboole_0(X0,k2_tarski(X1,X1)) = k2_tarski(X1,X1)
% 3.62/1.05      | r2_hidden(X1,X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_6643,plain,
% 3.62/1.05      ( k3_xboole_0(sK5,k2_tarski(sK6,sK6)) = k2_tarski(sK6,sK6) ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_2494,c_2502]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_0,plain,
% 3.62/1.05      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f53]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_34,negated_conjecture,
% 3.62/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.62/1.05      inference(cnf_transformation,[],[f85]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2491,plain,
% 3.62/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_21,plain,
% 3.62/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.62/1.05      inference(cnf_transformation,[],[f74]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2498,plain,
% 3.62/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.62/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_4194,plain,
% 3.62/1.05      ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_2491,c_2498]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_17,plain,
% 3.62/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/1.05      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f71]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_20,plain,
% 3.62/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.62/1.05      inference(cnf_transformation,[],[f75]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_275,plain,
% 3.62/1.05      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.62/1.05      inference(prop_impl,[status(thm)],[c_20]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_276,plain,
% 3.62/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_275]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_345,plain,
% 3.62/1.05      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.62/1.05      inference(bin_hyper_res,[status(thm)],[c_17,c_276]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2489,plain,
% 3.62/1.05      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.62/1.05      | r1_tarski(X2,X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_4456,plain,
% 3.62/1.05      ( k9_subset_1(u1_struct_0(sK4),X0,sK5) = k3_xboole_0(X0,sK5) ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_4194,c_2489]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_16,plain,
% 3.62/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/1.05      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.62/1.05      inference(cnf_transformation,[],[f70]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_344,plain,
% 3.62/1.05      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 3.62/1.05      | ~ r1_tarski(X2,X0) ),
% 3.62/1.05      inference(bin_hyper_res,[status(thm)],[c_16,c_276]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2490,plain,
% 3.62/1.05      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 3.62/1.05      | r1_tarski(X2,X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_5186,plain,
% 3.62/1.05      ( m1_subset_1(k3_xboole_0(X0,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.62/1.05      | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_4456,c_2490]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_37,plain,
% 3.62/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2976,plain,
% 3.62/1.05      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0)) | r1_tarski(sK5,X0) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_21]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_3447,plain,
% 3.62/1.05      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | r1_tarski(sK5,u1_struct_0(sK4)) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_2976]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_3455,plain,
% 3.62/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.62/1.05      | r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_3447]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13735,plain,
% 3.62/1.05      ( m1_subset_1(k3_xboole_0(X0,sK5),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_5186,c_37,c_3455]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13742,plain,
% 3.62/1.05      ( m1_subset_1(k3_xboole_0(sK5,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_0,c_13735]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_15229,plain,
% 3.62/1.05      ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_6643,c_13742]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_27,plain,
% 3.62/1.05      ( ~ v2_tex_2(X0,X1)
% 3.62/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | ~ r1_tarski(X2,X0)
% 3.62/1.05      | ~ l1_pre_topc(X1)
% 3.62/1.05      | k9_subset_1(u1_struct_0(X1),X0,sK3(X1,X0,X2)) = X2 ),
% 3.62/1.05      inference(cnf_transformation,[],[f80]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_35,negated_conjecture,
% 3.62/1.05      ( l1_pre_topc(sK4) ),
% 3.62/1.05      inference(cnf_transformation,[],[f84]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_585,plain,
% 3.62/1.05      ( ~ v2_tex_2(X0,X1)
% 3.62/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | ~ r1_tarski(X2,X0)
% 3.62/1.05      | k9_subset_1(u1_struct_0(X1),X0,sK3(X1,X0,X2)) = X2
% 3.62/1.05      | sK4 != X1 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_27,c_35]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_586,plain,
% 3.62/1.05      ( ~ v2_tex_2(X0,sK4)
% 3.62/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ r1_tarski(X1,X0)
% 3.62/1.05      | k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1 ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_585]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2486,plain,
% 3.62/1.05      ( k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1
% 3.62/1.05      | v2_tex_2(X0,sK4) != iProver_top
% 3.62/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.62/1.05      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.62/1.05      | r1_tarski(X1,X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2932,plain,
% 3.62/1.05      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
% 3.62/1.05      | v2_tex_2(sK5,sK4) != iProver_top
% 3.62/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.62/1.05      | r1_tarski(X0,sK5) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_2491,c_2486]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_33,negated_conjecture,
% 3.62/1.05      ( v2_tex_2(sK5,sK4) ),
% 3.62/1.05      inference(cnf_transformation,[],[f86]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_874,plain,
% 3.62/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ r1_tarski(X1,X0)
% 3.62/1.05      | k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1
% 3.62/1.05      | sK5 != X0
% 3.62/1.05      | sK4 != sK4 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_33,c_586]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_875,plain,
% 3.62/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ r1_tarski(X0,sK5)
% 3.62/1.05      | k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0 ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_874]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_876,plain,
% 3.62/1.05      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
% 3.62/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.62/1.05      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.62/1.05      | r1_tarski(X0,sK5) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_875]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_3216,plain,
% 3.62/1.05      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
% 3.62/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.62/1.05      | r1_tarski(X0,sK5) != iProver_top ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_2932,c_37,c_876]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_16307,plain,
% 3.62/1.05      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k2_tarski(sK6,sK6))) = k2_tarski(sK6,sK6)
% 3.62/1.05      | r1_tarski(k2_tarski(sK6,sK6),sK5) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_15229,c_3216]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13,plain,
% 3.62/1.05      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1) ),
% 3.62/1.05      inference(cnf_transformation,[],[f90]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2805,plain,
% 3.62/1.05      ( ~ r2_hidden(sK6,sK5) | r1_tarski(k2_tarski(sK6,sK6),sK5) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_13]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_3,plain,
% 3.62/1.05      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.62/1.05      inference(cnf_transformation,[],[f54]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2837,plain,
% 3.62/1.05      ( r2_hidden(sK6,X0) | ~ r2_hidden(sK6,sK5) | ~ r1_tarski(sK5,X0) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_3]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_4780,plain,
% 3.62/1.05      ( r2_hidden(sK6,u1_struct_0(sK4))
% 3.62/1.05      | ~ r2_hidden(sK6,sK5)
% 3.62/1.05      | ~ r1_tarski(sK5,u1_struct_0(sK4)) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_2837]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_3238,plain,
% 3.62/1.05      ( ~ r2_hidden(sK6,X0) | r1_tarski(k2_tarski(sK6,sK6),X0) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_13]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_6233,plain,
% 3.62/1.05      ( ~ r2_hidden(sK6,u1_struct_0(sK4))
% 3.62/1.05      | r1_tarski(k2_tarski(sK6,sK6),u1_struct_0(sK4)) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_3238]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2777,plain,
% 3.62/1.05      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_20]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_6235,plain,
% 3.62/1.05      ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ r1_tarski(k2_tarski(sK6,sK6),u1_struct_0(sK4)) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_2777]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2765,plain,
% 3.62/1.05      ( ~ v2_tex_2(sK5,sK4)
% 3.62/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ r1_tarski(X0,sK5)
% 3.62/1.05      | k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0 ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_586]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_11618,plain,
% 3.62/1.05      ( ~ v2_tex_2(sK5,sK4)
% 3.62/1.05      | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ r1_tarski(k2_tarski(sK6,sK6),sK5)
% 3.62/1.05      | k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k2_tarski(sK6,sK6))) = k2_tarski(sK6,sK6) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_2765]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_16758,plain,
% 3.62/1.05      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k2_tarski(sK6,sK6))) = k2_tarski(sK6,sK6) ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_16307,c_34,c_33,c_31,c_2805,c_3447,c_4780,c_6233,
% 3.62/1.05                 c_6235,c_11618]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_30,negated_conjecture,
% 3.62/1.05      ( ~ v4_pre_topc(X0,sK4)
% 3.62/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | k2_tarski(sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f94]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2495,plain,
% 3.62/1.05      ( k2_tarski(sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X0)
% 3.62/1.05      | v4_pre_topc(X0,sK4) != iProver_top
% 3.62/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_16761,plain,
% 3.62/1.05      ( v4_pre_topc(sK3(sK4,sK5,k2_tarski(sK6,sK6)),sK4) != iProver_top
% 3.62/1.05      | m1_subset_1(sK3(sK4,sK5,k2_tarski(sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_16758,c_2495]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_29,plain,
% 3.62/1.05      ( ~ v2_tex_2(X0,X1)
% 3.62/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | ~ r1_tarski(X2,X0)
% 3.62/1.05      | ~ l1_pre_topc(X1) ),
% 3.62/1.05      inference(cnf_transformation,[],[f78]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_564,plain,
% 3.62/1.05      ( ~ v2_tex_2(X0,X1)
% 3.62/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | ~ r1_tarski(X2,X0)
% 3.62/1.05      | sK4 != X1 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_29,c_35]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_565,plain,
% 3.62/1.05      ( ~ v2_tex_2(X0,sK4)
% 3.62/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | m1_subset_1(sK3(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ r1_tarski(X1,X0) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_564]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2758,plain,
% 3.62/1.05      ( ~ v2_tex_2(sK5,sK4)
% 3.62/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | m1_subset_1(sK3(sK4,sK5,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ r1_tarski(X0,sK5) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_565]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_11619,plain,
% 3.62/1.05      ( ~ v2_tex_2(sK5,sK4)
% 3.62/1.05      | m1_subset_1(sK3(sK4,sK5,k2_tarski(sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ r1_tarski(k2_tarski(sK6,sK6),sK5) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_2758]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_11626,plain,
% 3.62/1.05      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.62/1.05      | m1_subset_1(sK3(sK4,sK5,k2_tarski(sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.62/1.05      | m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.62/1.05      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.62/1.05      | r1_tarski(k2_tarski(sK6,sK6),sK5) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_11619]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_6238,plain,
% 3.62/1.05      ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.62/1.05      | r1_tarski(k2_tarski(sK6,sK6),u1_struct_0(sK4)) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_6235]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_6236,plain,
% 3.62/1.05      ( r2_hidden(sK6,u1_struct_0(sK4)) != iProver_top
% 3.62/1.05      | r1_tarski(k2_tarski(sK6,sK6),u1_struct_0(sK4)) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_6233]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_4782,plain,
% 3.62/1.05      ( r2_hidden(sK6,u1_struct_0(sK4)) = iProver_top
% 3.62/1.05      | r2_hidden(sK6,sK5) != iProver_top
% 3.62/1.05      | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_4780]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_28,plain,
% 3.62/1.05      ( v4_pre_topc(sK3(X0,X1,X2),X0)
% 3.62/1.05      | ~ v2_tex_2(X1,X0)
% 3.62/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.62/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.62/1.05      | ~ r1_tarski(X2,X1)
% 3.62/1.05      | ~ l1_pre_topc(X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f79]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_543,plain,
% 3.62/1.05      ( v4_pre_topc(sK3(X0,X1,X2),X0)
% 3.62/1.05      | ~ v2_tex_2(X1,X0)
% 3.62/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.62/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.62/1.05      | ~ r1_tarski(X2,X1)
% 3.62/1.05      | sK4 != X0 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_28,c_35]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_544,plain,
% 3.62/1.05      ( v4_pre_topc(sK3(sK4,X0,X1),sK4)
% 3.62/1.05      | ~ v2_tex_2(X0,sK4)
% 3.62/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ r1_tarski(X1,X0) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_543]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2755,plain,
% 3.62/1.05      ( v4_pre_topc(sK3(sK4,sK5,X0),sK4)
% 3.62/1.05      | ~ v2_tex_2(sK5,sK4)
% 3.62/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ r1_tarski(X0,sK5) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_544]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_3025,plain,
% 3.62/1.05      ( v4_pre_topc(sK3(sK4,sK5,k2_tarski(sK6,sK6)),sK4)
% 3.62/1.05      | ~ v2_tex_2(sK5,sK4)
% 3.62/1.05      | ~ m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.62/1.05      | ~ r1_tarski(k2_tarski(sK6,sK6),sK5) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_2755]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_3026,plain,
% 3.62/1.05      ( v4_pre_topc(sK3(sK4,sK5,k2_tarski(sK6,sK6)),sK4) = iProver_top
% 3.62/1.05      | v2_tex_2(sK5,sK4) != iProver_top
% 3.62/1.05      | m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.62/1.05      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.62/1.05      | r1_tarski(k2_tarski(sK6,sK6),sK5) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_3025]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2806,plain,
% 3.62/1.05      ( r2_hidden(sK6,sK5) != iProver_top
% 3.62/1.05      | r1_tarski(k2_tarski(sK6,sK6),sK5) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_2805]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_40,plain,
% 3.62/1.05      ( r2_hidden(sK6,sK5) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_38,plain,
% 3.62/1.05      ( v2_tex_2(sK5,sK4) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(contradiction,plain,
% 3.62/1.05      ( $false ),
% 3.62/1.05      inference(minisat,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_16761,c_11626,c_6238,c_6236,c_4782,c_3455,c_3026,
% 3.62/1.05                 c_2806,c_40,c_38,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  
% 3.62/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/1.05  
% 3.62/1.05  ------                               Statistics
% 3.62/1.05  
% 3.62/1.05  ------ General
% 3.62/1.05  
% 3.62/1.05  abstr_ref_over_cycles:                  0
% 3.62/1.05  abstr_ref_under_cycles:                 0
% 3.62/1.05  gc_basic_clause_elim:                   0
% 3.62/1.05  forced_gc_time:                         0
% 3.62/1.05  parsing_time:                           0.008
% 3.62/1.05  unif_index_cands_time:                  0.
% 3.62/1.05  unif_index_add_time:                    0.
% 3.62/1.05  orderings_time:                         0.
% 3.62/1.05  out_proof_time:                         0.011
% 3.62/1.05  total_time:                             0.381
% 3.62/1.05  num_of_symbols:                         50
% 3.62/1.05  num_of_terms:                           17065
% 3.62/1.05  
% 3.62/1.05  ------ Preprocessing
% 3.62/1.05  
% 3.62/1.05  num_of_splits:                          0
% 3.62/1.05  num_of_split_atoms:                     0
% 3.62/1.05  num_of_reused_defs:                     0
% 3.62/1.05  num_eq_ax_congr_red:                    32
% 3.62/1.05  num_of_sem_filtered_clauses:            1
% 3.62/1.05  num_of_subtypes:                        0
% 3.62/1.05  monotx_restored_types:                  0
% 3.62/1.05  sat_num_of_epr_types:                   0
% 3.62/1.05  sat_num_of_non_cyclic_types:            0
% 3.62/1.05  sat_guarded_non_collapsed_types:        0
% 3.62/1.05  num_pure_diseq_elim:                    0
% 3.62/1.05  simp_replaced_by:                       0
% 3.62/1.05  res_preprocessed:                       166
% 3.62/1.05  prep_upred:                             0
% 3.62/1.05  prep_unflattend:                        26
% 3.62/1.05  smt_new_axioms:                         0
% 3.62/1.05  pred_elim_cands:                        5
% 3.62/1.05  pred_elim:                              1
% 3.62/1.05  pred_elim_cl:                           1
% 3.62/1.05  pred_elim_cycles:                       6
% 3.62/1.05  merged_defs:                            16
% 3.62/1.05  merged_defs_ncl:                        0
% 3.62/1.05  bin_hyper_res:                          18
% 3.62/1.05  prep_cycles:                            4
% 3.62/1.05  pred_elim_time:                         0.014
% 3.62/1.05  splitting_time:                         0.
% 3.62/1.05  sem_filter_time:                        0.
% 3.62/1.05  monotx_time:                            0.
% 3.62/1.05  subtype_inf_time:                       0.
% 3.62/1.05  
% 3.62/1.05  ------ Problem properties
% 3.62/1.05  
% 3.62/1.05  clauses:                                34
% 3.62/1.05  conjectures:                            5
% 3.62/1.05  epr:                                    6
% 3.62/1.05  horn:                                   28
% 3.62/1.05  ground:                                 4
% 3.62/1.05  unary:                                  9
% 3.62/1.05  binary:                                 10
% 3.62/1.05  lits:                                   83
% 3.62/1.05  lits_eq:                                17
% 3.62/1.05  fd_pure:                                0
% 3.62/1.05  fd_pseudo:                              0
% 3.62/1.05  fd_cond:                                1
% 3.62/1.05  fd_pseudo_cond:                         4
% 3.62/1.05  ac_symbols:                             0
% 3.62/1.05  
% 3.62/1.05  ------ Propositional Solver
% 3.62/1.05  
% 3.62/1.05  prop_solver_calls:                      27
% 3.62/1.05  prop_fast_solver_calls:                 1559
% 3.62/1.05  smt_solver_calls:                       0
% 3.62/1.05  smt_fast_solver_calls:                  0
% 3.62/1.05  prop_num_of_clauses:                    6165
% 3.62/1.05  prop_preprocess_simplified:             13746
% 3.62/1.05  prop_fo_subsumed:                       29
% 3.62/1.05  prop_solver_time:                       0.
% 3.62/1.05  smt_solver_time:                        0.
% 3.62/1.05  smt_fast_solver_time:                   0.
% 3.62/1.05  prop_fast_solver_time:                  0.
% 3.62/1.05  prop_unsat_core_time:                   0.
% 3.62/1.05  
% 3.62/1.05  ------ QBF
% 3.62/1.05  
% 3.62/1.05  qbf_q_res:                              0
% 3.62/1.05  qbf_num_tautologies:                    0
% 3.62/1.05  qbf_prep_cycles:                        0
% 3.62/1.05  
% 3.62/1.05  ------ BMC1
% 3.62/1.05  
% 3.62/1.05  bmc1_current_bound:                     -1
% 3.62/1.05  bmc1_last_solved_bound:                 -1
% 3.62/1.05  bmc1_unsat_core_size:                   -1
% 3.62/1.05  bmc1_unsat_core_parents_size:           -1
% 3.62/1.05  bmc1_merge_next_fun:                    0
% 3.62/1.05  bmc1_unsat_core_clauses_time:           0.
% 3.62/1.05  
% 3.62/1.05  ------ Instantiation
% 3.62/1.05  
% 3.62/1.05  inst_num_of_clauses:                    1666
% 3.62/1.05  inst_num_in_passive:                    314
% 3.62/1.05  inst_num_in_active:                     553
% 3.62/1.05  inst_num_in_unprocessed:                799
% 3.62/1.05  inst_num_of_loops:                      670
% 3.62/1.05  inst_num_of_learning_restarts:          0
% 3.62/1.05  inst_num_moves_active_passive:          115
% 3.62/1.05  inst_lit_activity:                      0
% 3.62/1.05  inst_lit_activity_moves:                0
% 3.62/1.05  inst_num_tautologies:                   0
% 3.62/1.05  inst_num_prop_implied:                  0
% 3.62/1.05  inst_num_existing_simplified:           0
% 3.62/1.05  inst_num_eq_res_simplified:             0
% 3.62/1.05  inst_num_child_elim:                    0
% 3.62/1.05  inst_num_of_dismatching_blockings:      1017
% 3.62/1.05  inst_num_of_non_proper_insts:           1629
% 3.62/1.05  inst_num_of_duplicates:                 0
% 3.62/1.05  inst_inst_num_from_inst_to_res:         0
% 3.62/1.05  inst_dismatching_checking_time:         0.
% 3.62/1.05  
% 3.62/1.05  ------ Resolution
% 3.62/1.05  
% 3.62/1.05  res_num_of_clauses:                     0
% 3.62/1.05  res_num_in_passive:                     0
% 3.62/1.05  res_num_in_active:                      0
% 3.62/1.05  res_num_of_loops:                       170
% 3.62/1.05  res_forward_subset_subsumed:            305
% 3.62/1.05  res_backward_subset_subsumed:           4
% 3.62/1.05  res_forward_subsumed:                   0
% 3.62/1.05  res_backward_subsumed:                  0
% 3.62/1.05  res_forward_subsumption_resolution:     2
% 3.62/1.05  res_backward_subsumption_resolution:    0
% 3.62/1.05  res_clause_to_clause_subsumption:       1943
% 3.62/1.05  res_orphan_elimination:                 0
% 3.62/1.05  res_tautology_del:                      89
% 3.62/1.05  res_num_eq_res_simplified:              0
% 3.62/1.05  res_num_sel_changes:                    0
% 3.62/1.05  res_moves_from_active_to_pass:          0
% 3.62/1.05  
% 3.62/1.05  ------ Superposition
% 3.62/1.05  
% 3.62/1.05  sup_time_total:                         0.
% 3.62/1.05  sup_time_generating:                    0.
% 3.62/1.05  sup_time_sim_full:                      0.
% 3.62/1.05  sup_time_sim_immed:                     0.
% 3.62/1.05  
% 3.62/1.05  sup_num_of_clauses:                     259
% 3.62/1.05  sup_num_in_active:                      132
% 3.62/1.05  sup_num_in_passive:                     127
% 3.62/1.05  sup_num_of_loops:                       132
% 3.62/1.05  sup_fw_superposition:                   189
% 3.62/1.05  sup_bw_superposition:                   142
% 3.62/1.05  sup_immediate_simplified:               34
% 3.62/1.05  sup_given_eliminated:                   0
% 3.62/1.05  comparisons_done:                       0
% 3.62/1.05  comparisons_avoided:                    18
% 3.62/1.05  
% 3.62/1.05  ------ Simplifications
% 3.62/1.05  
% 3.62/1.05  
% 3.62/1.05  sim_fw_subset_subsumed:                 15
% 3.62/1.05  sim_bw_subset_subsumed:                 5
% 3.62/1.05  sim_fw_subsumed:                        12
% 3.62/1.05  sim_bw_subsumed:                        0
% 3.62/1.05  sim_fw_subsumption_res:                 0
% 3.62/1.05  sim_bw_subsumption_res:                 0
% 3.62/1.05  sim_tautology_del:                      12
% 3.62/1.05  sim_eq_tautology_del:                   7
% 3.62/1.05  sim_eq_res_simp:                        0
% 3.62/1.05  sim_fw_demodulated:                     3
% 3.62/1.05  sim_bw_demodulated:                     0
% 3.62/1.05  sim_light_normalised:                   14
% 3.62/1.05  sim_joinable_taut:                      0
% 3.62/1.05  sim_joinable_simp:                      0
% 3.62/1.05  sim_ac_normalised:                      0
% 3.62/1.05  sim_smt_subsumption:                    0
% 3.62/1.05  
%------------------------------------------------------------------------------
