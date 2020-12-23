%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:11 EST 2020

% Result     : Theorem 7.34s
% Output     : CNFRefutation 7.34s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 403 expanded)
%              Number of clauses        :   59 (  95 expanded)
%              Number of leaves         :   13 ( 142 expanded)
%              Depth                    :   17
%              Number of atoms          :  435 (2939 expanded)
%              Number of equality atoms :   81 ( 103 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                   => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                     => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
          & m1_connsp_2(X3,X0,X1)
          & m1_connsp_2(X2,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK4),X0,X1)
        & m1_connsp_2(sK4,X0,X1)
        & m1_connsp_2(X2,X0,X1)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
              & m1_connsp_2(X3,X0,X1)
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK3,X3),X0,X1)
            & m1_connsp_2(X3,X0,X1)
            & m1_connsp_2(sK3,X0,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK2)
                & m1_connsp_2(X3,X0,sK2)
                & m1_connsp_2(X2,X0,sK2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    & m1_connsp_2(X3,X0,X1)
                    & m1_connsp_2(X2,X0,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1)
                  & m1_connsp_2(X3,sK1,X1)
                  & m1_connsp_2(X2,sK1,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    & m1_connsp_2(sK4,sK1,sK2)
    & m1_connsp_2(sK3,sK1,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f39,f38,f37,f36])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f68,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
    m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_980,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_981,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_982,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5285,plain,
    ( k4_subset_1(u1_struct_0(sK1),X0,sK4) = k2_xboole_0(X0,sK4)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_981,c_982])).

cnf(c_6094,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_980,c_5285])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_983,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6396,plain,
    ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6094,c_983])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_33,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8195,plain,
    ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6396,c_32,c_33])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_978,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_986,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1610,plain,
    ( k2_xboole_0(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = k1_tops_1(sK1,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_978,c_986])).

cnf(c_1756,plain,
    ( k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_1610])).

cnf(c_8210,plain,
    ( k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = k1_tops_1(sK1,k2_xboole_0(sK3,sK4))
    | r1_tarski(sK3,k2_xboole_0(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8195,c_1756])).

cnf(c_12,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_985,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8700,plain,
    ( k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = k1_tops_1(sK1,k2_xboole_0(sK3,sK4)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8210,c_985])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_992,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8713,plain,
    ( r2_hidden(X0,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = iProver_top
    | r2_hidden(X0,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8700,c_992])).

cnf(c_19,negated_conjecture,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_17,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_321,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_322,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_326,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_322,c_27,c_25])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_326])).

cnf(c_398,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_400,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_24])).

cnf(c_977,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_399,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_1156,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK1),X0,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1258,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1156])).

cnf(c_1259,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1258])).

cnf(c_1283,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_977,c_31,c_32,c_33,c_399,c_1259])).

cnf(c_6386,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6094,c_1283])).

cnf(c_26223,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8713,c_6386])).

cnf(c_21,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_18,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_297,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_298,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_302,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_298,c_27,c_25])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,k1_tops_1(sK1,X1))
    | sK2 != X0
    | sK3 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_302])).

cnf(c_423,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_424,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_423])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26223,c_424,c_32,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 7.34/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.34/1.49  
% 7.34/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.34/1.49  
% 7.34/1.49  ------  iProver source info
% 7.34/1.49  
% 7.34/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.34/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.34/1.49  git: non_committed_changes: false
% 7.34/1.49  git: last_make_outside_of_git: false
% 7.34/1.49  
% 7.34/1.49  ------ 
% 7.34/1.49  
% 7.34/1.49  ------ Input Options
% 7.34/1.49  
% 7.34/1.49  --out_options                           all
% 7.34/1.49  --tptp_safe_out                         true
% 7.34/1.49  --problem_path                          ""
% 7.34/1.49  --include_path                          ""
% 7.34/1.49  --clausifier                            res/vclausify_rel
% 7.34/1.49  --clausifier_options                    --mode clausify
% 7.34/1.49  --stdin                                 false
% 7.34/1.49  --stats_out                             all
% 7.34/1.49  
% 7.34/1.49  ------ General Options
% 7.34/1.49  
% 7.34/1.49  --fof                                   false
% 7.34/1.49  --time_out_real                         305.
% 7.34/1.49  --time_out_virtual                      -1.
% 7.34/1.49  --symbol_type_check                     false
% 7.34/1.49  --clausify_out                          false
% 7.34/1.49  --sig_cnt_out                           false
% 7.34/1.49  --trig_cnt_out                          false
% 7.34/1.49  --trig_cnt_out_tolerance                1.
% 7.34/1.49  --trig_cnt_out_sk_spl                   false
% 7.34/1.49  --abstr_cl_out                          false
% 7.34/1.49  
% 7.34/1.49  ------ Global Options
% 7.34/1.49  
% 7.34/1.49  --schedule                              default
% 7.34/1.49  --add_important_lit                     false
% 7.34/1.49  --prop_solver_per_cl                    1000
% 7.34/1.49  --min_unsat_core                        false
% 7.34/1.49  --soft_assumptions                      false
% 7.34/1.49  --soft_lemma_size                       3
% 7.34/1.49  --prop_impl_unit_size                   0
% 7.34/1.49  --prop_impl_unit                        []
% 7.34/1.49  --share_sel_clauses                     true
% 7.34/1.49  --reset_solvers                         false
% 7.34/1.49  --bc_imp_inh                            [conj_cone]
% 7.34/1.49  --conj_cone_tolerance                   3.
% 7.34/1.49  --extra_neg_conj                        none
% 7.34/1.49  --large_theory_mode                     true
% 7.34/1.49  --prolific_symb_bound                   200
% 7.34/1.49  --lt_threshold                          2000
% 7.34/1.49  --clause_weak_htbl                      true
% 7.34/1.49  --gc_record_bc_elim                     false
% 7.34/1.49  
% 7.34/1.49  ------ Preprocessing Options
% 7.34/1.49  
% 7.34/1.49  --preprocessing_flag                    true
% 7.34/1.49  --time_out_prep_mult                    0.1
% 7.34/1.49  --splitting_mode                        input
% 7.34/1.49  --splitting_grd                         true
% 7.34/1.49  --splitting_cvd                         false
% 7.34/1.49  --splitting_cvd_svl                     false
% 7.34/1.49  --splitting_nvd                         32
% 7.34/1.49  --sub_typing                            true
% 7.34/1.49  --prep_gs_sim                           true
% 7.34/1.49  --prep_unflatten                        true
% 7.34/1.49  --prep_res_sim                          true
% 7.34/1.49  --prep_upred                            true
% 7.34/1.49  --prep_sem_filter                       exhaustive
% 7.34/1.49  --prep_sem_filter_out                   false
% 7.34/1.49  --pred_elim                             true
% 7.34/1.49  --res_sim_input                         true
% 7.34/1.49  --eq_ax_congr_red                       true
% 7.34/1.49  --pure_diseq_elim                       true
% 7.34/1.49  --brand_transform                       false
% 7.34/1.49  --non_eq_to_eq                          false
% 7.34/1.49  --prep_def_merge                        true
% 7.34/1.49  --prep_def_merge_prop_impl              false
% 7.34/1.49  --prep_def_merge_mbd                    true
% 7.34/1.49  --prep_def_merge_tr_red                 false
% 7.34/1.49  --prep_def_merge_tr_cl                  false
% 7.34/1.49  --smt_preprocessing                     true
% 7.34/1.49  --smt_ac_axioms                         fast
% 7.34/1.49  --preprocessed_out                      false
% 7.34/1.49  --preprocessed_stats                    false
% 7.34/1.49  
% 7.34/1.49  ------ Abstraction refinement Options
% 7.34/1.49  
% 7.34/1.49  --abstr_ref                             []
% 7.34/1.49  --abstr_ref_prep                        false
% 7.34/1.49  --abstr_ref_until_sat                   false
% 7.34/1.49  --abstr_ref_sig_restrict                funpre
% 7.34/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.34/1.49  --abstr_ref_under                       []
% 7.34/1.49  
% 7.34/1.49  ------ SAT Options
% 7.34/1.49  
% 7.34/1.49  --sat_mode                              false
% 7.34/1.49  --sat_fm_restart_options                ""
% 7.34/1.49  --sat_gr_def                            false
% 7.34/1.49  --sat_epr_types                         true
% 7.34/1.49  --sat_non_cyclic_types                  false
% 7.34/1.49  --sat_finite_models                     false
% 7.34/1.49  --sat_fm_lemmas                         false
% 7.34/1.49  --sat_fm_prep                           false
% 7.34/1.49  --sat_fm_uc_incr                        true
% 7.34/1.49  --sat_out_model                         small
% 7.34/1.49  --sat_out_clauses                       false
% 7.34/1.49  
% 7.34/1.49  ------ QBF Options
% 7.34/1.49  
% 7.34/1.49  --qbf_mode                              false
% 7.34/1.49  --qbf_elim_univ                         false
% 7.34/1.49  --qbf_dom_inst                          none
% 7.34/1.49  --qbf_dom_pre_inst                      false
% 7.34/1.49  --qbf_sk_in                             false
% 7.34/1.49  --qbf_pred_elim                         true
% 7.34/1.49  --qbf_split                             512
% 7.34/1.49  
% 7.34/1.49  ------ BMC1 Options
% 7.34/1.49  
% 7.34/1.49  --bmc1_incremental                      false
% 7.34/1.49  --bmc1_axioms                           reachable_all
% 7.34/1.49  --bmc1_min_bound                        0
% 7.34/1.49  --bmc1_max_bound                        -1
% 7.34/1.49  --bmc1_max_bound_default                -1
% 7.34/1.49  --bmc1_symbol_reachability              true
% 7.34/1.49  --bmc1_property_lemmas                  false
% 7.34/1.49  --bmc1_k_induction                      false
% 7.34/1.49  --bmc1_non_equiv_states                 false
% 7.34/1.49  --bmc1_deadlock                         false
% 7.34/1.49  --bmc1_ucm                              false
% 7.34/1.49  --bmc1_add_unsat_core                   none
% 7.34/1.49  --bmc1_unsat_core_children              false
% 7.34/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.34/1.49  --bmc1_out_stat                         full
% 7.34/1.49  --bmc1_ground_init                      false
% 7.34/1.49  --bmc1_pre_inst_next_state              false
% 7.34/1.49  --bmc1_pre_inst_state                   false
% 7.34/1.49  --bmc1_pre_inst_reach_state             false
% 7.34/1.49  --bmc1_out_unsat_core                   false
% 7.34/1.49  --bmc1_aig_witness_out                  false
% 7.34/1.49  --bmc1_verbose                          false
% 7.34/1.49  --bmc1_dump_clauses_tptp                false
% 7.34/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.34/1.49  --bmc1_dump_file                        -
% 7.34/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.34/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.34/1.49  --bmc1_ucm_extend_mode                  1
% 7.34/1.49  --bmc1_ucm_init_mode                    2
% 7.34/1.49  --bmc1_ucm_cone_mode                    none
% 7.34/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.34/1.49  --bmc1_ucm_relax_model                  4
% 7.34/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.34/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.34/1.49  --bmc1_ucm_layered_model                none
% 7.34/1.49  --bmc1_ucm_max_lemma_size               10
% 7.34/1.49  
% 7.34/1.49  ------ AIG Options
% 7.34/1.49  
% 7.34/1.49  --aig_mode                              false
% 7.34/1.49  
% 7.34/1.49  ------ Instantiation Options
% 7.34/1.49  
% 7.34/1.49  --instantiation_flag                    true
% 7.34/1.49  --inst_sos_flag                         false
% 7.34/1.49  --inst_sos_phase                        true
% 7.34/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.34/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.34/1.49  --inst_lit_sel_side                     num_symb
% 7.34/1.49  --inst_solver_per_active                1400
% 7.34/1.49  --inst_solver_calls_frac                1.
% 7.34/1.49  --inst_passive_queue_type               priority_queues
% 7.34/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.34/1.49  --inst_passive_queues_freq              [25;2]
% 7.34/1.49  --inst_dismatching                      true
% 7.34/1.49  --inst_eager_unprocessed_to_passive     true
% 7.34/1.49  --inst_prop_sim_given                   true
% 7.34/1.49  --inst_prop_sim_new                     false
% 7.34/1.49  --inst_subs_new                         false
% 7.34/1.49  --inst_eq_res_simp                      false
% 7.34/1.49  --inst_subs_given                       false
% 7.34/1.49  --inst_orphan_elimination               true
% 7.34/1.49  --inst_learning_loop_flag               true
% 7.34/1.49  --inst_learning_start                   3000
% 7.34/1.49  --inst_learning_factor                  2
% 7.34/1.49  --inst_start_prop_sim_after_learn       3
% 7.34/1.49  --inst_sel_renew                        solver
% 7.34/1.49  --inst_lit_activity_flag                true
% 7.34/1.49  --inst_restr_to_given                   false
% 7.34/1.49  --inst_activity_threshold               500
% 7.34/1.49  --inst_out_proof                        true
% 7.34/1.49  
% 7.34/1.49  ------ Resolution Options
% 7.34/1.49  
% 7.34/1.49  --resolution_flag                       true
% 7.34/1.49  --res_lit_sel                           adaptive
% 7.34/1.49  --res_lit_sel_side                      none
% 7.34/1.49  --res_ordering                          kbo
% 7.34/1.49  --res_to_prop_solver                    active
% 7.34/1.49  --res_prop_simpl_new                    false
% 7.34/1.49  --res_prop_simpl_given                  true
% 7.34/1.49  --res_passive_queue_type                priority_queues
% 7.34/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.34/1.49  --res_passive_queues_freq               [15;5]
% 7.34/1.49  --res_forward_subs                      full
% 7.34/1.49  --res_backward_subs                     full
% 7.34/1.49  --res_forward_subs_resolution           true
% 7.34/1.49  --res_backward_subs_resolution          true
% 7.34/1.49  --res_orphan_elimination                true
% 7.34/1.49  --res_time_limit                        2.
% 7.34/1.49  --res_out_proof                         true
% 7.34/1.49  
% 7.34/1.49  ------ Superposition Options
% 7.34/1.49  
% 7.34/1.49  --superposition_flag                    true
% 7.34/1.49  --sup_passive_queue_type                priority_queues
% 7.34/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.34/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.34/1.49  --demod_completeness_check              fast
% 7.34/1.49  --demod_use_ground                      true
% 7.34/1.49  --sup_to_prop_solver                    passive
% 7.34/1.49  --sup_prop_simpl_new                    true
% 7.34/1.49  --sup_prop_simpl_given                  true
% 7.34/1.49  --sup_fun_splitting                     false
% 7.34/1.49  --sup_smt_interval                      50000
% 7.34/1.49  
% 7.34/1.49  ------ Superposition Simplification Setup
% 7.34/1.49  
% 7.34/1.49  --sup_indices_passive                   []
% 7.34/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.34/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.49  --sup_full_bw                           [BwDemod]
% 7.34/1.49  --sup_immed_triv                        [TrivRules]
% 7.34/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.34/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.49  --sup_immed_bw_main                     []
% 7.34/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.34/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.49  
% 7.34/1.49  ------ Combination Options
% 7.34/1.49  
% 7.34/1.49  --comb_res_mult                         3
% 7.34/1.49  --comb_sup_mult                         2
% 7.34/1.49  --comb_inst_mult                        10
% 7.34/1.49  
% 7.34/1.49  ------ Debug Options
% 7.34/1.49  
% 7.34/1.49  --dbg_backtrace                         false
% 7.34/1.49  --dbg_dump_prop_clauses                 false
% 7.34/1.49  --dbg_dump_prop_clauses_file            -
% 7.34/1.49  --dbg_out_stat                          false
% 7.34/1.49  ------ Parsing...
% 7.34/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.34/1.49  
% 7.34/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.34/1.49  
% 7.34/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.34/1.49  
% 7.34/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.34/1.49  ------ Proving...
% 7.34/1.49  ------ Problem Properties 
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  clauses                                 24
% 7.34/1.49  conjectures                             3
% 7.34/1.49  EPR                                     2
% 7.34/1.49  Horn                                    22
% 7.34/1.49  unary                                   9
% 7.34/1.49  binary                                  7
% 7.34/1.49  lits                                    49
% 7.34/1.49  lits eq                                 8
% 7.34/1.49  fd_pure                                 0
% 7.34/1.49  fd_pseudo                               0
% 7.34/1.49  fd_cond                                 0
% 7.34/1.49  fd_pseudo_cond                          4
% 7.34/1.49  AC symbols                              0
% 7.34/1.49  
% 7.34/1.49  ------ Schedule dynamic 5 is on 
% 7.34/1.49  
% 7.34/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  ------ 
% 7.34/1.49  Current options:
% 7.34/1.49  ------ 
% 7.34/1.49  
% 7.34/1.49  ------ Input Options
% 7.34/1.49  
% 7.34/1.49  --out_options                           all
% 7.34/1.49  --tptp_safe_out                         true
% 7.34/1.49  --problem_path                          ""
% 7.34/1.49  --include_path                          ""
% 7.34/1.49  --clausifier                            res/vclausify_rel
% 7.34/1.49  --clausifier_options                    --mode clausify
% 7.34/1.49  --stdin                                 false
% 7.34/1.49  --stats_out                             all
% 7.34/1.49  
% 7.34/1.49  ------ General Options
% 7.34/1.49  
% 7.34/1.49  --fof                                   false
% 7.34/1.49  --time_out_real                         305.
% 7.34/1.49  --time_out_virtual                      -1.
% 7.34/1.49  --symbol_type_check                     false
% 7.34/1.49  --clausify_out                          false
% 7.34/1.49  --sig_cnt_out                           false
% 7.34/1.49  --trig_cnt_out                          false
% 7.34/1.49  --trig_cnt_out_tolerance                1.
% 7.34/1.49  --trig_cnt_out_sk_spl                   false
% 7.34/1.49  --abstr_cl_out                          false
% 7.34/1.49  
% 7.34/1.49  ------ Global Options
% 7.34/1.49  
% 7.34/1.49  --schedule                              default
% 7.34/1.49  --add_important_lit                     false
% 7.34/1.49  --prop_solver_per_cl                    1000
% 7.34/1.49  --min_unsat_core                        false
% 7.34/1.49  --soft_assumptions                      false
% 7.34/1.49  --soft_lemma_size                       3
% 7.34/1.49  --prop_impl_unit_size                   0
% 7.34/1.49  --prop_impl_unit                        []
% 7.34/1.49  --share_sel_clauses                     true
% 7.34/1.49  --reset_solvers                         false
% 7.34/1.49  --bc_imp_inh                            [conj_cone]
% 7.34/1.49  --conj_cone_tolerance                   3.
% 7.34/1.49  --extra_neg_conj                        none
% 7.34/1.49  --large_theory_mode                     true
% 7.34/1.49  --prolific_symb_bound                   200
% 7.34/1.49  --lt_threshold                          2000
% 7.34/1.49  --clause_weak_htbl                      true
% 7.34/1.49  --gc_record_bc_elim                     false
% 7.34/1.49  
% 7.34/1.49  ------ Preprocessing Options
% 7.34/1.49  
% 7.34/1.49  --preprocessing_flag                    true
% 7.34/1.49  --time_out_prep_mult                    0.1
% 7.34/1.49  --splitting_mode                        input
% 7.34/1.49  --splitting_grd                         true
% 7.34/1.49  --splitting_cvd                         false
% 7.34/1.49  --splitting_cvd_svl                     false
% 7.34/1.49  --splitting_nvd                         32
% 7.34/1.49  --sub_typing                            true
% 7.34/1.49  --prep_gs_sim                           true
% 7.34/1.49  --prep_unflatten                        true
% 7.34/1.49  --prep_res_sim                          true
% 7.34/1.49  --prep_upred                            true
% 7.34/1.49  --prep_sem_filter                       exhaustive
% 7.34/1.49  --prep_sem_filter_out                   false
% 7.34/1.49  --pred_elim                             true
% 7.34/1.49  --res_sim_input                         true
% 7.34/1.49  --eq_ax_congr_red                       true
% 7.34/1.49  --pure_diseq_elim                       true
% 7.34/1.49  --brand_transform                       false
% 7.34/1.49  --non_eq_to_eq                          false
% 7.34/1.49  --prep_def_merge                        true
% 7.34/1.49  --prep_def_merge_prop_impl              false
% 7.34/1.49  --prep_def_merge_mbd                    true
% 7.34/1.49  --prep_def_merge_tr_red                 false
% 7.34/1.49  --prep_def_merge_tr_cl                  false
% 7.34/1.49  --smt_preprocessing                     true
% 7.34/1.49  --smt_ac_axioms                         fast
% 7.34/1.49  --preprocessed_out                      false
% 7.34/1.49  --preprocessed_stats                    false
% 7.34/1.49  
% 7.34/1.49  ------ Abstraction refinement Options
% 7.34/1.49  
% 7.34/1.49  --abstr_ref                             []
% 7.34/1.49  --abstr_ref_prep                        false
% 7.34/1.49  --abstr_ref_until_sat                   false
% 7.34/1.49  --abstr_ref_sig_restrict                funpre
% 7.34/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.34/1.49  --abstr_ref_under                       []
% 7.34/1.49  
% 7.34/1.49  ------ SAT Options
% 7.34/1.49  
% 7.34/1.49  --sat_mode                              false
% 7.34/1.49  --sat_fm_restart_options                ""
% 7.34/1.49  --sat_gr_def                            false
% 7.34/1.49  --sat_epr_types                         true
% 7.34/1.49  --sat_non_cyclic_types                  false
% 7.34/1.49  --sat_finite_models                     false
% 7.34/1.49  --sat_fm_lemmas                         false
% 7.34/1.49  --sat_fm_prep                           false
% 7.34/1.49  --sat_fm_uc_incr                        true
% 7.34/1.49  --sat_out_model                         small
% 7.34/1.49  --sat_out_clauses                       false
% 7.34/1.49  
% 7.34/1.49  ------ QBF Options
% 7.34/1.49  
% 7.34/1.49  --qbf_mode                              false
% 7.34/1.49  --qbf_elim_univ                         false
% 7.34/1.49  --qbf_dom_inst                          none
% 7.34/1.49  --qbf_dom_pre_inst                      false
% 7.34/1.49  --qbf_sk_in                             false
% 7.34/1.49  --qbf_pred_elim                         true
% 7.34/1.49  --qbf_split                             512
% 7.34/1.49  
% 7.34/1.49  ------ BMC1 Options
% 7.34/1.49  
% 7.34/1.49  --bmc1_incremental                      false
% 7.34/1.49  --bmc1_axioms                           reachable_all
% 7.34/1.49  --bmc1_min_bound                        0
% 7.34/1.49  --bmc1_max_bound                        -1
% 7.34/1.49  --bmc1_max_bound_default                -1
% 7.34/1.49  --bmc1_symbol_reachability              true
% 7.34/1.49  --bmc1_property_lemmas                  false
% 7.34/1.49  --bmc1_k_induction                      false
% 7.34/1.49  --bmc1_non_equiv_states                 false
% 7.34/1.49  --bmc1_deadlock                         false
% 7.34/1.49  --bmc1_ucm                              false
% 7.34/1.49  --bmc1_add_unsat_core                   none
% 7.34/1.49  --bmc1_unsat_core_children              false
% 7.34/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.34/1.49  --bmc1_out_stat                         full
% 7.34/1.49  --bmc1_ground_init                      false
% 7.34/1.49  --bmc1_pre_inst_next_state              false
% 7.34/1.49  --bmc1_pre_inst_state                   false
% 7.34/1.49  --bmc1_pre_inst_reach_state             false
% 7.34/1.49  --bmc1_out_unsat_core                   false
% 7.34/1.49  --bmc1_aig_witness_out                  false
% 7.34/1.49  --bmc1_verbose                          false
% 7.34/1.49  --bmc1_dump_clauses_tptp                false
% 7.34/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.34/1.49  --bmc1_dump_file                        -
% 7.34/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.34/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.34/1.49  --bmc1_ucm_extend_mode                  1
% 7.34/1.49  --bmc1_ucm_init_mode                    2
% 7.34/1.49  --bmc1_ucm_cone_mode                    none
% 7.34/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.34/1.49  --bmc1_ucm_relax_model                  4
% 7.34/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.34/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.34/1.49  --bmc1_ucm_layered_model                none
% 7.34/1.49  --bmc1_ucm_max_lemma_size               10
% 7.34/1.49  
% 7.34/1.49  ------ AIG Options
% 7.34/1.49  
% 7.34/1.49  --aig_mode                              false
% 7.34/1.49  
% 7.34/1.49  ------ Instantiation Options
% 7.34/1.49  
% 7.34/1.49  --instantiation_flag                    true
% 7.34/1.49  --inst_sos_flag                         false
% 7.34/1.49  --inst_sos_phase                        true
% 7.34/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.34/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.34/1.49  --inst_lit_sel_side                     none
% 7.34/1.49  --inst_solver_per_active                1400
% 7.34/1.49  --inst_solver_calls_frac                1.
% 7.34/1.49  --inst_passive_queue_type               priority_queues
% 7.34/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.34/1.49  --inst_passive_queues_freq              [25;2]
% 7.34/1.49  --inst_dismatching                      true
% 7.34/1.49  --inst_eager_unprocessed_to_passive     true
% 7.34/1.49  --inst_prop_sim_given                   true
% 7.34/1.49  --inst_prop_sim_new                     false
% 7.34/1.49  --inst_subs_new                         false
% 7.34/1.49  --inst_eq_res_simp                      false
% 7.34/1.49  --inst_subs_given                       false
% 7.34/1.49  --inst_orphan_elimination               true
% 7.34/1.49  --inst_learning_loop_flag               true
% 7.34/1.49  --inst_learning_start                   3000
% 7.34/1.49  --inst_learning_factor                  2
% 7.34/1.49  --inst_start_prop_sim_after_learn       3
% 7.34/1.49  --inst_sel_renew                        solver
% 7.34/1.49  --inst_lit_activity_flag                true
% 7.34/1.49  --inst_restr_to_given                   false
% 7.34/1.49  --inst_activity_threshold               500
% 7.34/1.49  --inst_out_proof                        true
% 7.34/1.49  
% 7.34/1.49  ------ Resolution Options
% 7.34/1.49  
% 7.34/1.49  --resolution_flag                       false
% 7.34/1.49  --res_lit_sel                           adaptive
% 7.34/1.49  --res_lit_sel_side                      none
% 7.34/1.49  --res_ordering                          kbo
% 7.34/1.49  --res_to_prop_solver                    active
% 7.34/1.49  --res_prop_simpl_new                    false
% 7.34/1.49  --res_prop_simpl_given                  true
% 7.34/1.49  --res_passive_queue_type                priority_queues
% 7.34/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.34/1.49  --res_passive_queues_freq               [15;5]
% 7.34/1.49  --res_forward_subs                      full
% 7.34/1.49  --res_backward_subs                     full
% 7.34/1.49  --res_forward_subs_resolution           true
% 7.34/1.49  --res_backward_subs_resolution          true
% 7.34/1.49  --res_orphan_elimination                true
% 7.34/1.49  --res_time_limit                        2.
% 7.34/1.49  --res_out_proof                         true
% 7.34/1.49  
% 7.34/1.49  ------ Superposition Options
% 7.34/1.49  
% 7.34/1.49  --superposition_flag                    true
% 7.34/1.49  --sup_passive_queue_type                priority_queues
% 7.34/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.34/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.34/1.49  --demod_completeness_check              fast
% 7.34/1.49  --demod_use_ground                      true
% 7.34/1.49  --sup_to_prop_solver                    passive
% 7.34/1.49  --sup_prop_simpl_new                    true
% 7.34/1.49  --sup_prop_simpl_given                  true
% 7.34/1.49  --sup_fun_splitting                     false
% 7.34/1.49  --sup_smt_interval                      50000
% 7.34/1.49  
% 7.34/1.49  ------ Superposition Simplification Setup
% 7.34/1.49  
% 7.34/1.49  --sup_indices_passive                   []
% 7.34/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.34/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.34/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.49  --sup_full_bw                           [BwDemod]
% 7.34/1.49  --sup_immed_triv                        [TrivRules]
% 7.34/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.34/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.49  --sup_immed_bw_main                     []
% 7.34/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.34/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.34/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.34/1.49  
% 7.34/1.49  ------ Combination Options
% 7.34/1.49  
% 7.34/1.49  --comb_res_mult                         3
% 7.34/1.49  --comb_sup_mult                         2
% 7.34/1.49  --comb_inst_mult                        10
% 7.34/1.49  
% 7.34/1.49  ------ Debug Options
% 7.34/1.49  
% 7.34/1.49  --dbg_backtrace                         false
% 7.34/1.49  --dbg_dump_prop_clauses                 false
% 7.34/1.49  --dbg_dump_prop_clauses_file            -
% 7.34/1.49  --dbg_out_stat                          false
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  ------ Proving...
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  % SZS status Theorem for theBenchmark.p
% 7.34/1.49  
% 7.34/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.34/1.49  
% 7.34/1.49  fof(f12,conjecture,(
% 7.34/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 7.34/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f13,negated_conjecture,(
% 7.34/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 7.34/1.49    inference(negated_conjecture,[],[f12])).
% 7.34/1.49  
% 7.34/1.49  fof(f26,plain,(
% 7.34/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.34/1.49    inference(ennf_transformation,[],[f13])).
% 7.34/1.49  
% 7.34/1.49  fof(f27,plain,(
% 7.34/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.34/1.49    inference(flattening,[],[f26])).
% 7.34/1.49  
% 7.34/1.49  fof(f39,plain,(
% 7.34/1.49    ( ! [X2,X0,X1] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK4),X0,X1) & m1_connsp_2(sK4,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.34/1.49    introduced(choice_axiom,[])).
% 7.34/1.49  
% 7.34/1.49  fof(f38,plain,(
% 7.34/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK3,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(sK3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.34/1.49    introduced(choice_axiom,[])).
% 7.34/1.49  
% 7.34/1.49  fof(f37,plain,(
% 7.34/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK2) & m1_connsp_2(X3,X0,sK2) & m1_connsp_2(X2,X0,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 7.34/1.49    introduced(choice_axiom,[])).
% 7.34/1.49  
% 7.34/1.49  fof(f36,plain,(
% 7.34/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1) & m1_connsp_2(X3,sK1,X1) & m1_connsp_2(X2,sK1,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 7.34/1.49    introduced(choice_axiom,[])).
% 7.34/1.49  
% 7.34/1.49  fof(f40,plain,(
% 7.34/1.49    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) & m1_connsp_2(sK4,sK1,sK2) & m1_connsp_2(sK3,sK1,sK2) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 7.34/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f39,f38,f37,f36])).
% 7.34/1.49  
% 7.34/1.49  fof(f64,plain,(
% 7.34/1.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.34/1.49    inference(cnf_transformation,[],[f40])).
% 7.34/1.49  
% 7.34/1.49  fof(f65,plain,(
% 7.34/1.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.34/1.49    inference(cnf_transformation,[],[f40])).
% 7.34/1.49  
% 7.34/1.49  fof(f9,axiom,(
% 7.34/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.34/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f20,plain,(
% 7.34/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.34/1.49    inference(ennf_transformation,[],[f9])).
% 7.34/1.49  
% 7.34/1.49  fof(f21,plain,(
% 7.34/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.34/1.49    inference(flattening,[],[f20])).
% 7.34/1.49  
% 7.34/1.49  fof(f56,plain,(
% 7.34/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.34/1.49    inference(cnf_transformation,[],[f21])).
% 7.34/1.49  
% 7.34/1.49  fof(f8,axiom,(
% 7.34/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.34/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f18,plain,(
% 7.34/1.49    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.34/1.49    inference(ennf_transformation,[],[f8])).
% 7.34/1.49  
% 7.34/1.49  fof(f19,plain,(
% 7.34/1.49    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.34/1.49    inference(flattening,[],[f18])).
% 7.34/1.49  
% 7.34/1.49  fof(f55,plain,(
% 7.34/1.49    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.34/1.49    inference(cnf_transformation,[],[f19])).
% 7.34/1.49  
% 7.34/1.49  fof(f10,axiom,(
% 7.34/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 7.34/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f22,plain,(
% 7.34/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.34/1.49    inference(ennf_transformation,[],[f10])).
% 7.34/1.49  
% 7.34/1.49  fof(f23,plain,(
% 7.34/1.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.34/1.49    inference(flattening,[],[f22])).
% 7.34/1.49  
% 7.34/1.49  fof(f57,plain,(
% 7.34/1.49    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f23])).
% 7.34/1.49  
% 7.34/1.49  fof(f62,plain,(
% 7.34/1.49    l1_pre_topc(sK1)),
% 7.34/1.49    inference(cnf_transformation,[],[f40])).
% 7.34/1.49  
% 7.34/1.49  fof(f5,axiom,(
% 7.34/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.34/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f16,plain,(
% 7.34/1.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.34/1.49    inference(ennf_transformation,[],[f5])).
% 7.34/1.49  
% 7.34/1.49  fof(f52,plain,(
% 7.34/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f16])).
% 7.34/1.49  
% 7.34/1.49  fof(f6,axiom,(
% 7.34/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.34/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f53,plain,(
% 7.34/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.34/1.49    inference(cnf_transformation,[],[f6])).
% 7.34/1.49  
% 7.34/1.49  fof(f1,axiom,(
% 7.34/1.49    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 7.34/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f28,plain,(
% 7.34/1.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.34/1.49    inference(nnf_transformation,[],[f1])).
% 7.34/1.49  
% 7.34/1.49  fof(f29,plain,(
% 7.34/1.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.34/1.49    inference(flattening,[],[f28])).
% 7.34/1.49  
% 7.34/1.49  fof(f30,plain,(
% 7.34/1.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.34/1.49    inference(rectify,[],[f29])).
% 7.34/1.49  
% 7.34/1.49  fof(f31,plain,(
% 7.34/1.49    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.34/1.49    introduced(choice_axiom,[])).
% 7.34/1.49  
% 7.34/1.49  fof(f32,plain,(
% 7.34/1.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.34/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 7.34/1.49  
% 7.34/1.49  fof(f42,plain,(
% 7.34/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 7.34/1.49    inference(cnf_transformation,[],[f32])).
% 7.34/1.49  
% 7.34/1.49  fof(f70,plain,(
% 7.34/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 7.34/1.49    inference(equality_resolution,[],[f42])).
% 7.34/1.49  
% 7.34/1.49  fof(f68,plain,(
% 7.34/1.49    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)),
% 7.34/1.49    inference(cnf_transformation,[],[f40])).
% 7.34/1.49  
% 7.34/1.49  fof(f11,axiom,(
% 7.34/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 7.34/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.34/1.49  
% 7.34/1.49  fof(f24,plain,(
% 7.34/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.34/1.49    inference(ennf_transformation,[],[f11])).
% 7.34/1.49  
% 7.34/1.49  fof(f25,plain,(
% 7.34/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.34/1.49    inference(flattening,[],[f24])).
% 7.34/1.49  
% 7.34/1.49  fof(f35,plain,(
% 7.34/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.34/1.49    inference(nnf_transformation,[],[f25])).
% 7.34/1.49  
% 7.34/1.49  fof(f59,plain,(
% 7.34/1.49    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f35])).
% 7.34/1.49  
% 7.34/1.49  fof(f61,plain,(
% 7.34/1.49    v2_pre_topc(sK1)),
% 7.34/1.49    inference(cnf_transformation,[],[f40])).
% 7.34/1.49  
% 7.34/1.49  fof(f60,plain,(
% 7.34/1.49    ~v2_struct_0(sK1)),
% 7.34/1.49    inference(cnf_transformation,[],[f40])).
% 7.34/1.49  
% 7.34/1.49  fof(f63,plain,(
% 7.34/1.49    m1_subset_1(sK2,u1_struct_0(sK1))),
% 7.34/1.49    inference(cnf_transformation,[],[f40])).
% 7.34/1.49  
% 7.34/1.49  fof(f66,plain,(
% 7.34/1.49    m1_connsp_2(sK3,sK1,sK2)),
% 7.34/1.49    inference(cnf_transformation,[],[f40])).
% 7.34/1.49  
% 7.34/1.49  fof(f58,plain,(
% 7.34/1.49    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.34/1.49    inference(cnf_transformation,[],[f35])).
% 7.34/1.49  
% 7.34/1.49  cnf(c_23,negated_conjecture,
% 7.34/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.34/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_980,plain,
% 7.34/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_22,negated_conjecture,
% 7.34/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.34/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_981,plain,
% 7.34/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_15,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.34/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.34/1.49      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 7.34/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_982,plain,
% 7.34/1.49      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 7.34/1.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 7.34/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_5285,plain,
% 7.34/1.49      ( k4_subset_1(u1_struct_0(sK1),X0,sK4) = k2_xboole_0(X0,sK4)
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_981,c_982]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_6094,plain,
% 7.34/1.49      ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_980,c_5285]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_14,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.34/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.34/1.49      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 7.34/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_983,plain,
% 7.34/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.34/1.49      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.34/1.49      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_6396,plain,
% 7.34/1.49      ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 7.34/1.49      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.34/1.49      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_6094,c_983]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_32,plain,
% 7.34/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_33,plain,
% 7.34/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_8195,plain,
% 7.34/1.49      ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_6396,c_32,c_33]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_16,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.34/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.34/1.49      | ~ r1_tarski(X2,X0)
% 7.34/1.49      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 7.34/1.49      | ~ l1_pre_topc(X1) ),
% 7.34/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_25,negated_conjecture,
% 7.34/1.49      ( l1_pre_topc(sK1) ),
% 7.34/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_355,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.34/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.34/1.49      | ~ r1_tarski(X2,X0)
% 7.34/1.49      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 7.34/1.49      | sK1 != X1 ),
% 7.34/1.49      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_356,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.34/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.34/1.49      | ~ r1_tarski(X1,X0)
% 7.34/1.49      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
% 7.34/1.49      inference(unflattening,[status(thm)],[c_355]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_978,plain,
% 7.34/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.34/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.34/1.49      | r1_tarski(X1,X0) != iProver_top
% 7.34/1.49      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_356]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_11,plain,
% 7.34/1.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.34/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_986,plain,
% 7.34/1.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_1610,plain,
% 7.34/1.49      ( k2_xboole_0(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = k1_tops_1(sK1,X1)
% 7.34/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.34/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_978,c_986]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_1756,plain,
% 7.34/1.49      ( k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,X0)) = k1_tops_1(sK1,X0)
% 7.34/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.34/1.49      | r1_tarski(sK3,X0) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_980,c_1610]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_8210,plain,
% 7.34/1.49      ( k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = k1_tops_1(sK1,k2_xboole_0(sK3,sK4))
% 7.34/1.49      | r1_tarski(sK3,k2_xboole_0(sK3,sK4)) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_8195,c_1756]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_12,plain,
% 7.34/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.34/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_985,plain,
% 7.34/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_8700,plain,
% 7.34/1.49      ( k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = k1_tops_1(sK1,k2_xboole_0(sK3,sK4)) ),
% 7.34/1.49      inference(forward_subsumption_resolution,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_8210,c_985]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_4,plain,
% 7.34/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 7.34/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_992,plain,
% 7.34/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.34/1.49      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_8713,plain,
% 7.34/1.49      ( r2_hidden(X0,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) = iProver_top
% 7.34/1.49      | r2_hidden(X0,k1_tops_1(sK1,sK3)) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_8700,c_992]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_19,negated_conjecture,
% 7.34/1.49      ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
% 7.34/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_17,plain,
% 7.34/1.49      ( m1_connsp_2(X0,X1,X2)
% 7.34/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.34/1.49      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 7.34/1.49      | v2_struct_0(X1)
% 7.34/1.49      | ~ v2_pre_topc(X1)
% 7.34/1.49      | ~ l1_pre_topc(X1) ),
% 7.34/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_26,negated_conjecture,
% 7.34/1.49      ( v2_pre_topc(sK1) ),
% 7.34/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_321,plain,
% 7.34/1.49      ( m1_connsp_2(X0,X1,X2)
% 7.34/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.34/1.49      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 7.34/1.49      | v2_struct_0(X1)
% 7.34/1.49      | ~ l1_pre_topc(X1)
% 7.34/1.49      | sK1 != X1 ),
% 7.34/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_322,plain,
% 7.34/1.49      ( m1_connsp_2(X0,sK1,X1)
% 7.34/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.34/1.49      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 7.34/1.49      | v2_struct_0(sK1)
% 7.34/1.49      | ~ l1_pre_topc(sK1) ),
% 7.34/1.49      inference(unflattening,[status(thm)],[c_321]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_27,negated_conjecture,
% 7.34/1.49      ( ~ v2_struct_0(sK1) ),
% 7.34/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_326,plain,
% 7.34/1.49      ( m1_connsp_2(X0,sK1,X1)
% 7.34/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.34/1.49      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_322,c_27,c_25]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_397,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.34/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.34/1.49      | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
% 7.34/1.49      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
% 7.34/1.49      | sK2 != X0
% 7.34/1.49      | sK1 != sK1 ),
% 7.34/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_326]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_398,plain,
% 7.34/1.49      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.34/1.49      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 7.34/1.49      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 7.34/1.49      inference(unflattening,[status(thm)],[c_397]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_24,negated_conjecture,
% 7.34/1.49      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 7.34/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_400,plain,
% 7.34/1.49      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.34/1.49      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_398,c_24]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_977,plain,
% 7.34/1.49      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.34/1.49      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_31,plain,
% 7.34/1.49      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_399,plain,
% 7.34/1.49      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.34/1.49      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 7.34/1.49      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_1156,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.34/1.49      | m1_subset_1(k4_subset_1(u1_struct_0(sK1),X0,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.34/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_1258,plain,
% 7.34/1.49      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.34/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.34/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.34/1.49      inference(instantiation,[status(thm)],[c_1156]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_1259,plain,
% 7.34/1.49      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 7.34/1.49      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.34/1.49      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_1258]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_1283,plain,
% 7.34/1.49      ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_977,c_31,c_32,c_33,c_399,c_1259]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_6386,plain,
% 7.34/1.49      ( r2_hidden(sK2,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) != iProver_top ),
% 7.34/1.49      inference(demodulation,[status(thm)],[c_6094,c_1283]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_26223,plain,
% 7.34/1.49      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) != iProver_top ),
% 7.34/1.49      inference(superposition,[status(thm)],[c_8713,c_6386]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_21,negated_conjecture,
% 7.34/1.49      ( m1_connsp_2(sK3,sK1,sK2) ),
% 7.34/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_18,plain,
% 7.34/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.34/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.34/1.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 7.34/1.49      | v2_struct_0(X1)
% 7.34/1.49      | ~ v2_pre_topc(X1)
% 7.34/1.49      | ~ l1_pre_topc(X1) ),
% 7.34/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_297,plain,
% 7.34/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.34/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.34/1.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 7.34/1.49      | v2_struct_0(X1)
% 7.34/1.49      | ~ l1_pre_topc(X1)
% 7.34/1.49      | sK1 != X1 ),
% 7.34/1.49      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_298,plain,
% 7.34/1.49      ( ~ m1_connsp_2(X0,sK1,X1)
% 7.34/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.34/1.49      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 7.34/1.49      | v2_struct_0(sK1)
% 7.34/1.49      | ~ l1_pre_topc(sK1) ),
% 7.34/1.49      inference(unflattening,[status(thm)],[c_297]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_302,plain,
% 7.34/1.49      ( ~ m1_connsp_2(X0,sK1,X1)
% 7.34/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.34/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.34/1.49      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 7.34/1.49      inference(global_propositional_subsumption,
% 7.34/1.49                [status(thm)],
% 7.34/1.49                [c_298,c_27,c_25]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_422,plain,
% 7.34/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.34/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.34/1.49      | r2_hidden(X0,k1_tops_1(sK1,X1))
% 7.34/1.49      | sK2 != X0
% 7.34/1.49      | sK3 != X1
% 7.34/1.49      | sK1 != sK1 ),
% 7.34/1.49      inference(resolution_lifted,[status(thm)],[c_21,c_302]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_423,plain,
% 7.34/1.49      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 7.34/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.34/1.49      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 7.34/1.49      inference(unflattening,[status(thm)],[c_422]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(c_424,plain,
% 7.34/1.49      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 7.34/1.49      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.34/1.49      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 7.34/1.49      inference(predicate_to_equality,[status(thm)],[c_423]) ).
% 7.34/1.49  
% 7.34/1.49  cnf(contradiction,plain,
% 7.34/1.49      ( $false ),
% 7.34/1.49      inference(minisat,[status(thm)],[c_26223,c_424,c_32,c_31]) ).
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.34/1.49  
% 7.34/1.49  ------                               Statistics
% 7.34/1.49  
% 7.34/1.49  ------ General
% 7.34/1.49  
% 7.34/1.49  abstr_ref_over_cycles:                  0
% 7.34/1.49  abstr_ref_under_cycles:                 0
% 7.34/1.49  gc_basic_clause_elim:                   0
% 7.34/1.49  forced_gc_time:                         0
% 7.34/1.49  parsing_time:                           0.011
% 7.34/1.49  unif_index_cands_time:                  0.
% 7.34/1.49  unif_index_add_time:                    0.
% 7.34/1.49  orderings_time:                         0.
% 7.34/1.49  out_proof_time:                         0.011
% 7.34/1.49  total_time:                             0.797
% 7.34/1.49  num_of_symbols:                         48
% 7.34/1.49  num_of_terms:                           38260
% 7.34/1.49  
% 7.34/1.49  ------ Preprocessing
% 7.34/1.49  
% 7.34/1.49  num_of_splits:                          0
% 7.34/1.49  num_of_split_atoms:                     0
% 7.34/1.49  num_of_reused_defs:                     0
% 7.34/1.49  num_eq_ax_congr_red:                    17
% 7.34/1.49  num_of_sem_filtered_clauses:            1
% 7.34/1.49  num_of_subtypes:                        0
% 7.34/1.49  monotx_restored_types:                  0
% 7.34/1.49  sat_num_of_epr_types:                   0
% 7.34/1.49  sat_num_of_non_cyclic_types:            0
% 7.34/1.49  sat_guarded_non_collapsed_types:        0
% 7.34/1.49  num_pure_diseq_elim:                    0
% 7.34/1.49  simp_replaced_by:                       0
% 7.34/1.49  res_preprocessed:                       118
% 7.34/1.49  prep_upred:                             0
% 7.34/1.49  prep_unflattend:                        9
% 7.34/1.49  smt_new_axioms:                         0
% 7.34/1.49  pred_elim_cands:                        3
% 7.34/1.49  pred_elim:                              4
% 7.34/1.49  pred_elim_cl:                           3
% 7.34/1.49  pred_elim_cycles:                       6
% 7.34/1.49  merged_defs:                            0
% 7.34/1.49  merged_defs_ncl:                        0
% 7.34/1.49  bin_hyper_res:                          0
% 7.34/1.49  prep_cycles:                            4
% 7.34/1.49  pred_elim_time:                         0.003
% 7.34/1.49  splitting_time:                         0.
% 7.34/1.49  sem_filter_time:                        0.
% 7.34/1.49  monotx_time:                            0.
% 7.34/1.49  subtype_inf_time:                       0.
% 7.34/1.49  
% 7.34/1.49  ------ Problem properties
% 7.34/1.49  
% 7.34/1.49  clauses:                                24
% 7.34/1.49  conjectures:                            3
% 7.34/1.49  epr:                                    2
% 7.34/1.49  horn:                                   22
% 7.34/1.49  ground:                                 8
% 7.34/1.49  unary:                                  9
% 7.34/1.49  binary:                                 7
% 7.34/1.49  lits:                                   49
% 7.34/1.49  lits_eq:                                8
% 7.34/1.49  fd_pure:                                0
% 7.34/1.49  fd_pseudo:                              0
% 7.34/1.49  fd_cond:                                0
% 7.34/1.49  fd_pseudo_cond:                         4
% 7.34/1.49  ac_symbols:                             0
% 7.34/1.49  
% 7.34/1.49  ------ Propositional Solver
% 7.34/1.49  
% 7.34/1.49  prop_solver_calls:                      31
% 7.34/1.49  prop_fast_solver_calls:                 948
% 7.34/1.49  smt_solver_calls:                       0
% 7.34/1.49  smt_fast_solver_calls:                  0
% 7.34/1.49  prop_num_of_clauses:                    9884
% 7.34/1.49  prop_preprocess_simplified:             16574
% 7.34/1.49  prop_fo_subsumed:                       23
% 7.34/1.49  prop_solver_time:                       0.
% 7.34/1.49  smt_solver_time:                        0.
% 7.34/1.49  smt_fast_solver_time:                   0.
% 7.34/1.49  prop_fast_solver_time:                  0.
% 7.34/1.49  prop_unsat_core_time:                   0.001
% 7.34/1.49  
% 7.34/1.49  ------ QBF
% 7.34/1.49  
% 7.34/1.49  qbf_q_res:                              0
% 7.34/1.49  qbf_num_tautologies:                    0
% 7.34/1.49  qbf_prep_cycles:                        0
% 7.34/1.49  
% 7.34/1.49  ------ BMC1
% 7.34/1.49  
% 7.34/1.49  bmc1_current_bound:                     -1
% 7.34/1.49  bmc1_last_solved_bound:                 -1
% 7.34/1.49  bmc1_unsat_core_size:                   -1
% 7.34/1.49  bmc1_unsat_core_parents_size:           -1
% 7.34/1.49  bmc1_merge_next_fun:                    0
% 7.34/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.34/1.49  
% 7.34/1.49  ------ Instantiation
% 7.34/1.49  
% 7.34/1.49  inst_num_of_clauses:                    2343
% 7.34/1.49  inst_num_in_passive:                    1543
% 7.34/1.49  inst_num_in_active:                     758
% 7.34/1.49  inst_num_in_unprocessed:                42
% 7.34/1.49  inst_num_of_loops:                      810
% 7.34/1.49  inst_num_of_learning_restarts:          0
% 7.34/1.49  inst_num_moves_active_passive:          51
% 7.34/1.49  inst_lit_activity:                      0
% 7.34/1.49  inst_lit_activity_moves:                2
% 7.34/1.49  inst_num_tautologies:                   0
% 7.34/1.49  inst_num_prop_implied:                  0
% 7.34/1.49  inst_num_existing_simplified:           0
% 7.34/1.49  inst_num_eq_res_simplified:             0
% 7.34/1.49  inst_num_child_elim:                    0
% 7.34/1.49  inst_num_of_dismatching_blockings:      2378
% 7.34/1.49  inst_num_of_non_proper_insts:           2476
% 7.34/1.49  inst_num_of_duplicates:                 0
% 7.34/1.49  inst_inst_num_from_inst_to_res:         0
% 7.34/1.49  inst_dismatching_checking_time:         0.
% 7.34/1.49  
% 7.34/1.49  ------ Resolution
% 7.34/1.49  
% 7.34/1.49  res_num_of_clauses:                     0
% 7.34/1.49  res_num_in_passive:                     0
% 7.34/1.49  res_num_in_active:                      0
% 7.34/1.49  res_num_of_loops:                       122
% 7.34/1.49  res_forward_subset_subsumed:            30
% 7.34/1.49  res_backward_subset_subsumed:           0
% 7.34/1.49  res_forward_subsumed:                   0
% 7.34/1.49  res_backward_subsumed:                  0
% 7.34/1.49  res_forward_subsumption_resolution:     0
% 7.34/1.49  res_backward_subsumption_resolution:    0
% 7.34/1.49  res_clause_to_clause_subsumption:       12987
% 7.34/1.49  res_orphan_elimination:                 0
% 7.34/1.49  res_tautology_del:                      12
% 7.34/1.49  res_num_eq_res_simplified:              2
% 7.34/1.49  res_num_sel_changes:                    0
% 7.34/1.49  res_moves_from_active_to_pass:          0
% 7.34/1.49  
% 7.34/1.49  ------ Superposition
% 7.34/1.49  
% 7.34/1.49  sup_time_total:                         0.
% 7.34/1.49  sup_time_generating:                    0.
% 7.34/1.49  sup_time_sim_full:                      0.
% 7.34/1.49  sup_time_sim_immed:                     0.
% 7.34/1.49  
% 7.34/1.49  sup_num_of_clauses:                     1019
% 7.34/1.49  sup_num_in_active:                      156
% 7.34/1.49  sup_num_in_passive:                     863
% 7.34/1.49  sup_num_of_loops:                       161
% 7.34/1.49  sup_fw_superposition:                   1144
% 7.34/1.49  sup_bw_superposition:                   948
% 7.34/1.49  sup_immediate_simplified:               708
% 7.34/1.49  sup_given_eliminated:                   0
% 7.34/1.49  comparisons_done:                       0
% 7.34/1.49  comparisons_avoided:                    0
% 7.34/1.49  
% 7.34/1.49  ------ Simplifications
% 7.34/1.49  
% 7.34/1.49  
% 7.34/1.49  sim_fw_subset_subsumed:                 23
% 7.34/1.49  sim_bw_subset_subsumed:                 8
% 7.34/1.49  sim_fw_subsumed:                        291
% 7.34/1.49  sim_bw_subsumed:                        27
% 7.34/1.49  sim_fw_subsumption_res:                 11
% 7.34/1.49  sim_bw_subsumption_res:                 0
% 7.34/1.49  sim_tautology_del:                      74
% 7.34/1.49  sim_eq_tautology_del:                   58
% 7.34/1.49  sim_eq_res_simp:                        6
% 7.34/1.49  sim_fw_demodulated:                     147
% 7.34/1.49  sim_bw_demodulated:                     5
% 7.34/1.49  sim_light_normalised:                   274
% 7.34/1.49  sim_joinable_taut:                      0
% 7.34/1.49  sim_joinable_simp:                      0
% 7.34/1.49  sim_ac_normalised:                      0
% 7.34/1.49  sim_smt_subsumption:                    0
% 7.34/1.49  
%------------------------------------------------------------------------------
