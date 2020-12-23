%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:12 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 383 expanded)
%              Number of clauses        :  107 ( 132 expanded)
%              Number of leaves         :   20 ( 115 expanded)
%              Depth                    :   17
%              Number of atoms          :  622 (2336 expanded)
%              Number of equality atoms :   65 (  70 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f43,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    & m1_connsp_2(sK4,sK1,sK2)
    & m1_connsp_2(sK3,sK1,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f42,f41,f40,f39])).

fof(f60,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    m1_connsp_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_750,plain,
    ( ~ r1_tarski(X0_46,X1_46)
    | r1_tarski(X2_46,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    theory(equality)).

cnf(c_1543,plain,
    ( ~ r1_tarski(X0_46,X1_46)
    | r1_tarski(k4_subset_1(u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK1))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X0_46
    | u1_struct_0(sK1) != X1_46 ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_4233,plain,
    ( ~ r1_tarski(X0_46,u1_struct_0(sK1))
    | r1_tarski(k4_subset_1(u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK1))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X0_46
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_21038,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK1))
    | ~ r1_tarski(k2_xboole_0(sK3,sK4),u1_struct_0(sK1))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != k2_xboole_0(sK3,sK4)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4233])).

cnf(c_1452,plain,
    ( ~ r1_tarski(X0_46,X1_46)
    | r1_tarski(k1_tops_1(sK1,X2_46),X3_46)
    | X3_46 != X1_46
    | k1_tops_1(sK1,X2_46) != X0_46 ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_1795,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,X0_46),X1_46)
    | r1_tarski(k1_tops_1(sK1,X0_46),X2_46)
    | X2_46 != X1_46
    | k1_tops_1(sK1,X0_46) != k1_tops_1(sK1,X0_46) ),
    inference(instantiation,[status(thm)],[c_1452])).

cnf(c_3052,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK4),X0_46)
    | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
    | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != X0_46
    | k1_tops_1(sK1,sK4) != k1_tops_1(sK1,sK4) ),
    inference(instantiation,[status(thm)],[c_1795])).

cnf(c_21030,plain,
    ( r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
    | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k2_xboole_0(sK3,sK4)))
    | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != k1_tops_1(sK1,k2_xboole_0(sK3,sK4))
    | k1_tops_1(sK1,sK4) != k1_tops_1(sK1,sK4) ),
    inference(instantiation,[status(thm)],[c_3052])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_743,plain,
    ( ~ r1_tarski(X0_46,X1_46)
    | r1_tarski(X0_46,k2_xboole_0(X2_46,X1_46)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1401,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,X0_46),X1_46)
    | r1_tarski(k1_tops_1(sK1,X0_46),k2_xboole_0(X2_46,X1_46)) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_1750,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK4),X0_46)
    | r1_tarski(k1_tops_1(sK1,sK4),k2_xboole_0(X1_46,X0_46)) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_4540,plain,
    ( r1_tarski(k1_tops_1(sK1,sK4),k2_xboole_0(X0_46,sK4))
    | ~ r1_tarski(k1_tops_1(sK1,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1750])).

cnf(c_17877,plain,
    ( r1_tarski(k1_tops_1(sK1,sK4),k2_xboole_0(sK3,sK4))
    | ~ r1_tarski(k1_tops_1(sK1,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_4540])).

cnf(c_9,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_11,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(X2,X4)
    | r1_tarski(X2,k1_tops_1(X3,X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | k1_tops_1(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X0),X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_324,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X0),X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_320,c_8])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X0),X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_324])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_435,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X0),X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_325,c_22])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k1_tops_1(sK1,X0),X1)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_440,plain,
    ( r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
    | ~ r1_tarski(k1_tops_1(sK1,X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_21])).

cnf(c_441,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k1_tops_1(sK1,X0),X1)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) ),
    inference(renaming,[status(thm)],[c_440])).

cnf(c_736,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k1_tops_1(sK1,X0_46),X1_46)
    | r1_tarski(k1_tops_1(sK1,X0_46),k1_tops_1(sK1,X1_46)) ),
    inference(subtyping,[status(esa)],[c_441])).

cnf(c_1402,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k2_xboole_0(X1_46,X2_46),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0_46),k1_tops_1(sK1,k2_xboole_0(X1_46,X2_46)))
    | ~ r1_tarski(k1_tops_1(sK1,X0_46),k2_xboole_0(X1_46,X2_46)) ),
    inference(instantiation,[status(thm)],[c_736])).

cnf(c_7911,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0_46),k1_tops_1(sK1,k2_xboole_0(sK3,sK4)))
    | ~ r1_tarski(k1_tops_1(sK1,X0_46),k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_17876,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k2_xboole_0(sK3,sK4)))
    | ~ r1_tarski(k1_tops_1(sK1,sK4),k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_7911])).

cnf(c_755,plain,
    ( X0_46 != X1_46
    | k1_tops_1(X0_47,X0_46) = k1_tops_1(X0_47,X1_46) ),
    theory(equality)).

cnf(c_1802,plain,
    ( X0_46 != X1_46
    | k1_tops_1(sK1,X0_46) = k1_tops_1(sK1,X1_46) ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_3543,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X0_46
    | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) = k1_tops_1(sK1,X0_46) ),
    inference(instantiation,[status(thm)],[c_1802])).

cnf(c_9034,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) != k2_xboole_0(sK3,sK4)
    | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) = k1_tops_1(sK1,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3543])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_741,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ r1_tarski(X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1376,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0_46,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_741])).

cnf(c_1638,plain,
    ( m1_subset_1(k2_xboole_0(X0_46,X1_46),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k2_xboole_0(X0_46,X1_46),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_5309,plain,
    ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k2_xboole_0(sK3,sK4),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_738,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1204,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_740,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | r1_tarski(X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1202,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
    | r1_tarski(X0_46,X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_1879,plain,
    ( r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_1202])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_739,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1203,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_1878,plain,
    ( r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1203,c_1202])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_185,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_186,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_185])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_186])).

cnf(c_632,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_633,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_632])).

cnf(c_664,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_230,c_633])).

cnf(c_728,plain,
    ( ~ r1_tarski(X0_46,X1_46)
    | ~ r1_tarski(X2_46,X1_46)
    | k4_subset_1(X1_46,X0_46,X2_46) = k2_xboole_0(X0_46,X2_46) ),
    inference(subtyping,[status(esa)],[c_664])).

cnf(c_1212,plain,
    ( k4_subset_1(X0_46,X1_46,X2_46) = k2_xboole_0(X1_46,X2_46)
    | r1_tarski(X1_46,X0_46) != iProver_top
    | r1_tarski(X2_46,X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_2439,plain,
    ( k4_subset_1(u1_struct_0(sK1),X0_46,sK4) = k2_xboole_0(X0_46,sK4)
    | r1_tarski(X0_46,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1878,c_1212])).

cnf(c_3321,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1879,c_2439])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_742,plain,
    ( ~ r1_tarski(X0_46,X1_46)
    | ~ r1_tarski(X2_46,X1_46)
    | r1_tarski(k2_xboole_0(X0_46,X2_46),X1_46) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1639,plain,
    ( ~ r1_tarski(X0_46,u1_struct_0(sK1))
    | ~ r1_tarski(X1_46,u1_struct_0(sK1))
    | r1_tarski(k2_xboole_0(X0_46,X1_46),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_2785,plain,
    ( ~ r1_tarski(X0_46,u1_struct_0(sK1))
    | r1_tarski(k2_xboole_0(X0_46,sK4),u1_struct_0(sK1))
    | ~ r1_tarski(sK4,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1639])).

cnf(c_3237,plain,
    ( r1_tarski(k2_xboole_0(sK3,sK4),u1_struct_0(sK1))
    | ~ r1_tarski(sK4,u1_struct_0(sK1))
    | ~ r1_tarski(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2785])).

cnf(c_1201,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) = iProver_top
    | r1_tarski(X0_46,X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_15,negated_conjecture,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_12,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_398,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_399,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_403,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_22,c_21])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_403])).

cnf(c_517,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_519,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_20])).

cnf(c_733,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(subtyping,[status(esa)],[c_519])).

cnf(c_1209,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_2320,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top
    | r1_tarski(k4_subset_1(u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_1209])).

cnf(c_2321,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
    | ~ r1_tarski(k4_subset_1(u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2320])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_744,plain,
    ( ~ r2_hidden(X0_46,X1_46)
    | r2_hidden(X0_46,X2_46)
    | ~ r1_tarski(X1_46,X2_46) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1438,plain,
    ( r2_hidden(sK2,X0_46)
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | ~ r1_tarski(k1_tops_1(sK1,sK4),X0_46) ),
    inference(instantiation,[status(thm)],[c_744])).

cnf(c_2275,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
    | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1438])).

cnf(c_748,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_1702,plain,
    ( k1_tops_1(sK1,sK4) = k1_tops_1(sK1,sK4) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_1609,plain,
    ( r1_tarski(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_740,c_738])).

cnf(c_1607,plain,
    ( r1_tarski(sK4,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_740,c_739])).

cnf(c_1532,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_465,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_735,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0_46),X0_46) ),
    inference(subtyping,[status(esa)],[c_465])).

cnf(c_1340,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_16,negated_conjecture,
    ( m1_connsp_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_13,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_14,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_135,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_14])).

cnf(c_136,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_135])).

cnf(c_356,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_136,c_23])).

cnf(c_357,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_361,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_22,c_21])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r2_hidden(X0,k1_tops_1(sK1,X1))
    | sK2 != X0
    | sK4 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_361])).

cnf(c_533,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,k1_tops_1(sK1,sK4)) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21038,c_21030,c_17877,c_17876,c_9034,c_5309,c_3321,c_3237,c_2321,c_2275,c_1702,c_1609,c_1607,c_1532,c_1340,c_533,c_18,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:15:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.59/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.59/1.49  
% 7.59/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.59/1.49  
% 7.59/1.49  ------  iProver source info
% 7.59/1.49  
% 7.59/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.59/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.59/1.49  git: non_committed_changes: false
% 7.59/1.49  git: last_make_outside_of_git: false
% 7.59/1.49  
% 7.59/1.49  ------ 
% 7.59/1.49  ------ Parsing...
% 7.59/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.59/1.49  
% 7.59/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.59/1.49  ------ Proving...
% 7.59/1.49  ------ Problem Properties 
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  clauses                                 19
% 7.59/1.49  conjectures                             3
% 7.59/1.49  EPR                                     1
% 7.59/1.49  Horn                                    18
% 7.59/1.49  unary                                   7
% 7.59/1.49  binary                                  8
% 7.59/1.49  lits                                    36
% 7.59/1.49  lits eq                                 3
% 7.59/1.49  fd_pure                                 0
% 7.59/1.49  fd_pseudo                               0
% 7.59/1.49  fd_cond                                 0
% 7.59/1.49  fd_pseudo_cond                          0
% 7.59/1.49  AC symbols                              0
% 7.59/1.49  
% 7.59/1.49  ------ Input Options Time Limit: Unbounded
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  ------ 
% 7.59/1.49  Current options:
% 7.59/1.49  ------ 
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  ------ Proving...
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  % SZS status Theorem for theBenchmark.p
% 7.59/1.49  
% 7.59/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.59/1.49  
% 7.59/1.49  fof(f2,axiom,(
% 7.59/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.59/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f15,plain,(
% 7.59/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.59/1.49    inference(ennf_transformation,[],[f2])).
% 7.59/1.49  
% 7.59/1.49  fof(f47,plain,(
% 7.59/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f15])).
% 7.59/1.49  
% 7.59/1.49  fof(f7,axiom,(
% 7.59/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 7.59/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f22,plain,(
% 7.59/1.49    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.59/1.49    inference(ennf_transformation,[],[f7])).
% 7.59/1.49  
% 7.59/1.49  fof(f23,plain,(
% 7.59/1.49    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.59/1.49    inference(flattening,[],[f22])).
% 7.59/1.49  
% 7.59/1.49  fof(f53,plain,(
% 7.59/1.49    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f23])).
% 7.59/1.49  
% 7.59/1.49  fof(f9,axiom,(
% 7.59/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 7.59/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f25,plain,(
% 7.59/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.59/1.49    inference(ennf_transformation,[],[f9])).
% 7.59/1.49  
% 7.59/1.49  fof(f26,plain,(
% 7.59/1.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.59/1.49    inference(flattening,[],[f25])).
% 7.59/1.49  
% 7.59/1.49  fof(f55,plain,(
% 7.59/1.49    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f26])).
% 7.59/1.49  
% 7.59/1.49  fof(f6,axiom,(
% 7.59/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.59/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f20,plain,(
% 7.59/1.49    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.59/1.49    inference(ennf_transformation,[],[f6])).
% 7.59/1.49  
% 7.59/1.49  fof(f21,plain,(
% 7.59/1.49    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.59/1.49    inference(flattening,[],[f20])).
% 7.59/1.49  
% 7.59/1.49  fof(f52,plain,(
% 7.59/1.49    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f21])).
% 7.59/1.49  
% 7.59/1.49  fof(f12,conjecture,(
% 7.59/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 7.59/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f13,negated_conjecture,(
% 7.59/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 7.59/1.49    inference(negated_conjecture,[],[f12])).
% 7.59/1.49  
% 7.59/1.49  fof(f31,plain,(
% 7.59/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.59/1.49    inference(ennf_transformation,[],[f13])).
% 7.59/1.49  
% 7.59/1.49  fof(f32,plain,(
% 7.59/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.59/1.49    inference(flattening,[],[f31])).
% 7.59/1.49  
% 7.59/1.49  fof(f42,plain,(
% 7.59/1.49    ( ! [X2,X0,X1] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK4),X0,X1) & m1_connsp_2(sK4,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.59/1.49    introduced(choice_axiom,[])).
% 7.59/1.49  
% 7.59/1.49  fof(f41,plain,(
% 7.59/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK3,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(sK3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.59/1.49    introduced(choice_axiom,[])).
% 7.59/1.49  
% 7.59/1.49  fof(f40,plain,(
% 7.59/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK2) & m1_connsp_2(X3,X0,sK2) & m1_connsp_2(X2,X0,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 7.59/1.49    introduced(choice_axiom,[])).
% 7.59/1.49  
% 7.59/1.49  fof(f39,plain,(
% 7.59/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1) & m1_connsp_2(X3,sK1,X1) & m1_connsp_2(X2,sK1,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 7.59/1.49    introduced(choice_axiom,[])).
% 7.59/1.49  
% 7.59/1.49  fof(f43,plain,(
% 7.59/1.49    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) & m1_connsp_2(sK4,sK1,sK2) & m1_connsp_2(sK3,sK1,sK2) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 7.59/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f42,f41,f40,f39])).
% 7.59/1.49  
% 7.59/1.49  fof(f60,plain,(
% 7.59/1.49    v2_pre_topc(sK1)),
% 7.59/1.49    inference(cnf_transformation,[],[f43])).
% 7.59/1.49  
% 7.59/1.49  fof(f61,plain,(
% 7.59/1.49    l1_pre_topc(sK1)),
% 7.59/1.49    inference(cnf_transformation,[],[f43])).
% 7.59/1.49  
% 7.59/1.49  fof(f5,axiom,(
% 7.59/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.59/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f37,plain,(
% 7.59/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.59/1.49    inference(nnf_transformation,[],[f5])).
% 7.59/1.49  
% 7.59/1.49  fof(f51,plain,(
% 7.59/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f37])).
% 7.59/1.49  
% 7.59/1.49  fof(f63,plain,(
% 7.59/1.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.59/1.49    inference(cnf_transformation,[],[f43])).
% 7.59/1.49  
% 7.59/1.49  fof(f50,plain,(
% 7.59/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.59/1.49    inference(cnf_transformation,[],[f37])).
% 7.59/1.49  
% 7.59/1.49  fof(f64,plain,(
% 7.59/1.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.59/1.49    inference(cnf_transformation,[],[f43])).
% 7.59/1.49  
% 7.59/1.49  fof(f4,axiom,(
% 7.59/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.59/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f18,plain,(
% 7.59/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.59/1.49    inference(ennf_transformation,[],[f4])).
% 7.59/1.49  
% 7.59/1.49  fof(f19,plain,(
% 7.59/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.59/1.49    inference(flattening,[],[f18])).
% 7.59/1.49  
% 7.59/1.49  fof(f49,plain,(
% 7.59/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.59/1.49    inference(cnf_transformation,[],[f19])).
% 7.59/1.49  
% 7.59/1.49  fof(f3,axiom,(
% 7.59/1.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.59/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f16,plain,(
% 7.59/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.59/1.49    inference(ennf_transformation,[],[f3])).
% 7.59/1.49  
% 7.59/1.49  fof(f17,plain,(
% 7.59/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.59/1.49    inference(flattening,[],[f16])).
% 7.59/1.49  
% 7.59/1.49  fof(f48,plain,(
% 7.59/1.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f17])).
% 7.59/1.49  
% 7.59/1.49  fof(f67,plain,(
% 7.59/1.49    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)),
% 7.59/1.49    inference(cnf_transformation,[],[f43])).
% 7.59/1.49  
% 7.59/1.49  fof(f10,axiom,(
% 7.59/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 7.59/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f27,plain,(
% 7.59/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.59/1.49    inference(ennf_transformation,[],[f10])).
% 7.59/1.49  
% 7.59/1.49  fof(f28,plain,(
% 7.59/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.59/1.49    inference(flattening,[],[f27])).
% 7.59/1.49  
% 7.59/1.49  fof(f38,plain,(
% 7.59/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.59/1.49    inference(nnf_transformation,[],[f28])).
% 7.59/1.49  
% 7.59/1.49  fof(f57,plain,(
% 7.59/1.49    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f38])).
% 7.59/1.49  
% 7.59/1.49  fof(f59,plain,(
% 7.59/1.49    ~v2_struct_0(sK1)),
% 7.59/1.49    inference(cnf_transformation,[],[f43])).
% 7.59/1.49  
% 7.59/1.49  fof(f62,plain,(
% 7.59/1.49    m1_subset_1(sK2,u1_struct_0(sK1))),
% 7.59/1.49    inference(cnf_transformation,[],[f43])).
% 7.59/1.49  
% 7.59/1.49  fof(f1,axiom,(
% 7.59/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.59/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f14,plain,(
% 7.59/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.59/1.49    inference(ennf_transformation,[],[f1])).
% 7.59/1.49  
% 7.59/1.49  fof(f33,plain,(
% 7.59/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.59/1.49    inference(nnf_transformation,[],[f14])).
% 7.59/1.49  
% 7.59/1.49  fof(f34,plain,(
% 7.59/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.59/1.49    inference(rectify,[],[f33])).
% 7.59/1.49  
% 7.59/1.49  fof(f35,plain,(
% 7.59/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.59/1.49    introduced(choice_axiom,[])).
% 7.59/1.49  
% 7.59/1.49  fof(f36,plain,(
% 7.59/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.59/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 7.59/1.49  
% 7.59/1.49  fof(f44,plain,(
% 7.59/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f36])).
% 7.59/1.49  
% 7.59/1.49  fof(f8,axiom,(
% 7.59/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 7.59/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f24,plain,(
% 7.59/1.49    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.59/1.49    inference(ennf_transformation,[],[f8])).
% 7.59/1.49  
% 7.59/1.49  fof(f54,plain,(
% 7.59/1.49    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f24])).
% 7.59/1.49  
% 7.59/1.49  fof(f66,plain,(
% 7.59/1.49    m1_connsp_2(sK4,sK1,sK2)),
% 7.59/1.49    inference(cnf_transformation,[],[f43])).
% 7.59/1.49  
% 7.59/1.49  fof(f56,plain,(
% 7.59/1.49    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f38])).
% 7.59/1.49  
% 7.59/1.49  fof(f11,axiom,(
% 7.59/1.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.59/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.59/1.49  
% 7.59/1.49  fof(f29,plain,(
% 7.59/1.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.59/1.49    inference(ennf_transformation,[],[f11])).
% 7.59/1.49  
% 7.59/1.49  fof(f30,plain,(
% 7.59/1.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.59/1.49    inference(flattening,[],[f29])).
% 7.59/1.49  
% 7.59/1.49  fof(f58,plain,(
% 7.59/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.59/1.49    inference(cnf_transformation,[],[f30])).
% 7.59/1.49  
% 7.59/1.49  cnf(c_750,plain,
% 7.59/1.49      ( ~ r1_tarski(X0_46,X1_46)
% 7.59/1.49      | r1_tarski(X2_46,X3_46)
% 7.59/1.49      | X2_46 != X0_46
% 7.59/1.49      | X3_46 != X1_46 ),
% 7.59/1.49      theory(equality) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1543,plain,
% 7.59/1.49      ( ~ r1_tarski(X0_46,X1_46)
% 7.59/1.49      | r1_tarski(k4_subset_1(u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK1))
% 7.59/1.49      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X0_46
% 7.59/1.49      | u1_struct_0(sK1) != X1_46 ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_750]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_4233,plain,
% 7.59/1.49      ( ~ r1_tarski(X0_46,u1_struct_0(sK1))
% 7.59/1.49      | r1_tarski(k4_subset_1(u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK1))
% 7.59/1.49      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X0_46
% 7.59/1.49      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_1543]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_21038,plain,
% 7.59/1.49      ( r1_tarski(k4_subset_1(u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK1))
% 7.59/1.49      | ~ r1_tarski(k2_xboole_0(sK3,sK4),u1_struct_0(sK1))
% 7.59/1.49      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != k2_xboole_0(sK3,sK4)
% 7.59/1.49      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_4233]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1452,plain,
% 7.59/1.49      ( ~ r1_tarski(X0_46,X1_46)
% 7.59/1.49      | r1_tarski(k1_tops_1(sK1,X2_46),X3_46)
% 7.59/1.49      | X3_46 != X1_46
% 7.59/1.49      | k1_tops_1(sK1,X2_46) != X0_46 ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_750]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1795,plain,
% 7.59/1.49      ( ~ r1_tarski(k1_tops_1(sK1,X0_46),X1_46)
% 7.59/1.49      | r1_tarski(k1_tops_1(sK1,X0_46),X2_46)
% 7.59/1.49      | X2_46 != X1_46
% 7.59/1.49      | k1_tops_1(sK1,X0_46) != k1_tops_1(sK1,X0_46) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_1452]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3052,plain,
% 7.59/1.49      ( ~ r1_tarski(k1_tops_1(sK1,sK4),X0_46)
% 7.59/1.49      | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
% 7.59/1.49      | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != X0_46
% 7.59/1.49      | k1_tops_1(sK1,sK4) != k1_tops_1(sK1,sK4) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_1795]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_21030,plain,
% 7.59/1.49      ( r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k2_xboole_0(sK3,sK4)))
% 7.59/1.49      | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != k1_tops_1(sK1,k2_xboole_0(sK3,sK4))
% 7.59/1.49      | k1_tops_1(sK1,sK4) != k1_tops_1(sK1,sK4) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_3052]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3,plain,
% 7.59/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 7.59/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_743,plain,
% 7.59/1.49      ( ~ r1_tarski(X0_46,X1_46)
% 7.59/1.49      | r1_tarski(X0_46,k2_xboole_0(X2_46,X1_46)) ),
% 7.59/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1401,plain,
% 7.59/1.49      ( ~ r1_tarski(k1_tops_1(sK1,X0_46),X1_46)
% 7.59/1.49      | r1_tarski(k1_tops_1(sK1,X0_46),k2_xboole_0(X2_46,X1_46)) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_743]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1750,plain,
% 7.59/1.49      ( ~ r1_tarski(k1_tops_1(sK1,sK4),X0_46)
% 7.59/1.49      | r1_tarski(k1_tops_1(sK1,sK4),k2_xboole_0(X1_46,X0_46)) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_1401]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_4540,plain,
% 7.59/1.49      ( r1_tarski(k1_tops_1(sK1,sK4),k2_xboole_0(X0_46,sK4))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(sK1,sK4),sK4) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_1750]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_17877,plain,
% 7.59/1.49      ( r1_tarski(k1_tops_1(sK1,sK4),k2_xboole_0(sK3,sK4))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(sK1,sK4),sK4) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_4540]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_9,plain,
% 7.59/1.49      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 7.59/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.59/1.49      | ~ v2_pre_topc(X0)
% 7.59/1.49      | ~ l1_pre_topc(X0) ),
% 7.59/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_11,plain,
% 7.59/1.49      ( ~ v3_pre_topc(X0,X1)
% 7.59/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | ~ r1_tarski(X0,X2)
% 7.59/1.49      | r1_tarski(X0,k1_tops_1(X1,X2))
% 7.59/1.49      | ~ l1_pre_topc(X1) ),
% 7.59/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_319,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 7.59/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
% 7.59/1.49      | ~ r1_tarski(X2,X4)
% 7.59/1.49      | r1_tarski(X2,k1_tops_1(X3,X4))
% 7.59/1.49      | ~ v2_pre_topc(X1)
% 7.59/1.49      | ~ l1_pre_topc(X1)
% 7.59/1.49      | ~ l1_pre_topc(X3)
% 7.59/1.49      | X3 != X1
% 7.59/1.49      | k1_tops_1(X1,X0) != X2 ),
% 7.59/1.49      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_320,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | ~ m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(X1,X0),X2)
% 7.59/1.49      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 7.59/1.49      | ~ v2_pre_topc(X1)
% 7.59/1.49      | ~ l1_pre_topc(X1) ),
% 7.59/1.49      inference(unflattening,[status(thm)],[c_319]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_8,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | ~ l1_pre_topc(X1) ),
% 7.59/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_324,plain,
% 7.59/1.49      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(X1,X0),X2)
% 7.59/1.49      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 7.59/1.49      | ~ v2_pre_topc(X1)
% 7.59/1.49      | ~ l1_pre_topc(X1) ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_320,c_8]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_325,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(X1,X0),X2)
% 7.59/1.49      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 7.59/1.49      | ~ v2_pre_topc(X1)
% 7.59/1.49      | ~ l1_pre_topc(X1) ),
% 7.59/1.49      inference(renaming,[status(thm)],[c_324]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_22,negated_conjecture,
% 7.59/1.49      ( v2_pre_topc(sK1) ),
% 7.59/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_435,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(X1,X0),X2)
% 7.59/1.49      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 7.59/1.49      | ~ l1_pre_topc(X1)
% 7.59/1.49      | sK1 != X1 ),
% 7.59/1.49      inference(resolution_lifted,[status(thm)],[c_325,c_22]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_436,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(sK1,X0),X1)
% 7.59/1.49      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
% 7.59/1.49      | ~ l1_pre_topc(sK1) ),
% 7.59/1.49      inference(unflattening,[status(thm)],[c_435]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_21,negated_conjecture,
% 7.59/1.49      ( l1_pre_topc(sK1) ),
% 7.59/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_440,plain,
% 7.59/1.49      ( r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(sK1,X0),X1)
% 7.59/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_436,c_21]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_441,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(sK1,X0),X1)
% 7.59/1.49      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) ),
% 7.59/1.49      inference(renaming,[status(thm)],[c_440]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_736,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(sK1,X0_46),X1_46)
% 7.59/1.49      | r1_tarski(k1_tops_1(sK1,X0_46),k1_tops_1(sK1,X1_46)) ),
% 7.59/1.49      inference(subtyping,[status(esa)],[c_441]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1402,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ m1_subset_1(k2_xboole_0(X1_46,X2_46),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | r1_tarski(k1_tops_1(sK1,X0_46),k1_tops_1(sK1,k2_xboole_0(X1_46,X2_46)))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(sK1,X0_46),k2_xboole_0(X1_46,X2_46)) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_736]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_7911,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | r1_tarski(k1_tops_1(sK1,X0_46),k1_tops_1(sK1,k2_xboole_0(sK3,sK4)))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(sK1,X0_46),k2_xboole_0(sK3,sK4)) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_1402]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_17876,plain,
% 7.59/1.49      ( ~ m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k2_xboole_0(sK3,sK4)))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(sK1,sK4),k2_xboole_0(sK3,sK4)) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_7911]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_755,plain,
% 7.59/1.49      ( X0_46 != X1_46
% 7.59/1.49      | k1_tops_1(X0_47,X0_46) = k1_tops_1(X0_47,X1_46) ),
% 7.59/1.49      theory(equality) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1802,plain,
% 7.59/1.49      ( X0_46 != X1_46 | k1_tops_1(sK1,X0_46) = k1_tops_1(sK1,X1_46) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_755]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3543,plain,
% 7.59/1.49      ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X0_46
% 7.59/1.49      | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) = k1_tops_1(sK1,X0_46) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_1802]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_9034,plain,
% 7.59/1.49      ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) != k2_xboole_0(sK3,sK4)
% 7.59/1.49      | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) = k1_tops_1(sK1,k2_xboole_0(sK3,sK4)) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_3543]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_6,plain,
% 7.59/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.59/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_741,plain,
% 7.59/1.49      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 7.59/1.49      | ~ r1_tarski(X0_46,X1_46) ),
% 7.59/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1376,plain,
% 7.59/1.49      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ r1_tarski(X0_46,u1_struct_0(sK1)) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_741]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1638,plain,
% 7.59/1.49      ( m1_subset_1(k2_xboole_0(X0_46,X1_46),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ r1_tarski(k2_xboole_0(X0_46,X1_46),u1_struct_0(sK1)) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_1376]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_5309,plain,
% 7.59/1.49      ( m1_subset_1(k2_xboole_0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ r1_tarski(k2_xboole_0(sK3,sK4),u1_struct_0(sK1)) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_1638]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_19,negated_conjecture,
% 7.59/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.59/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_738,negated_conjecture,
% 7.59/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.59/1.49      inference(subtyping,[status(esa)],[c_19]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1204,plain,
% 7.59/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_7,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.59/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_740,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 7.59/1.49      | r1_tarski(X0_46,X1_46) ),
% 7.59/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1202,plain,
% 7.59/1.49      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
% 7.59/1.49      | r1_tarski(X0_46,X1_46) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_740]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1879,plain,
% 7.59/1.49      ( r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1204,c_1202]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_18,negated_conjecture,
% 7.59/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.59/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_739,negated_conjecture,
% 7.59/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.59/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1203,plain,
% 7.59/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1878,plain,
% 7.59/1.49      ( r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1203,c_1202]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_5,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.59/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.59/1.49      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 7.59/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_185,plain,
% 7.59/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.59/1.49      inference(prop_impl,[status(thm)],[c_6]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_186,plain,
% 7.59/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.59/1.49      inference(renaming,[status(thm)],[c_185]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_230,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.59/1.49      | ~ r1_tarski(X2,X1)
% 7.59/1.49      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 7.59/1.49      inference(bin_hyper_res,[status(thm)],[c_5,c_186]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_632,plain,
% 7.59/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.59/1.49      inference(prop_impl,[status(thm)],[c_6]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_633,plain,
% 7.59/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.59/1.49      inference(renaming,[status(thm)],[c_632]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_664,plain,
% 7.59/1.49      ( ~ r1_tarski(X0,X1)
% 7.59/1.49      | ~ r1_tarski(X2,X1)
% 7.59/1.49      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 7.59/1.49      inference(bin_hyper_res,[status(thm)],[c_230,c_633]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_728,plain,
% 7.59/1.49      ( ~ r1_tarski(X0_46,X1_46)
% 7.59/1.49      | ~ r1_tarski(X2_46,X1_46)
% 7.59/1.49      | k4_subset_1(X1_46,X0_46,X2_46) = k2_xboole_0(X0_46,X2_46) ),
% 7.59/1.49      inference(subtyping,[status(esa)],[c_664]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1212,plain,
% 7.59/1.49      ( k4_subset_1(X0_46,X1_46,X2_46) = k2_xboole_0(X1_46,X2_46)
% 7.59/1.49      | r1_tarski(X1_46,X0_46) != iProver_top
% 7.59/1.49      | r1_tarski(X2_46,X0_46) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2439,plain,
% 7.59/1.49      ( k4_subset_1(u1_struct_0(sK1),X0_46,sK4) = k2_xboole_0(X0_46,sK4)
% 7.59/1.49      | r1_tarski(X0_46,u1_struct_0(sK1)) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1878,c_1212]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3321,plain,
% 7.59/1.49      ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1879,c_2439]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_4,plain,
% 7.59/1.49      ( ~ r1_tarski(X0,X1)
% 7.59/1.49      | ~ r1_tarski(X2,X1)
% 7.59/1.49      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 7.59/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_742,plain,
% 7.59/1.49      ( ~ r1_tarski(X0_46,X1_46)
% 7.59/1.49      | ~ r1_tarski(X2_46,X1_46)
% 7.59/1.49      | r1_tarski(k2_xboole_0(X0_46,X2_46),X1_46) ),
% 7.59/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1639,plain,
% 7.59/1.49      ( ~ r1_tarski(X0_46,u1_struct_0(sK1))
% 7.59/1.49      | ~ r1_tarski(X1_46,u1_struct_0(sK1))
% 7.59/1.49      | r1_tarski(k2_xboole_0(X0_46,X1_46),u1_struct_0(sK1)) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_742]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2785,plain,
% 7.59/1.49      ( ~ r1_tarski(X0_46,u1_struct_0(sK1))
% 7.59/1.49      | r1_tarski(k2_xboole_0(X0_46,sK4),u1_struct_0(sK1))
% 7.59/1.49      | ~ r1_tarski(sK4,u1_struct_0(sK1)) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_1639]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_3237,plain,
% 7.59/1.49      ( r1_tarski(k2_xboole_0(sK3,sK4),u1_struct_0(sK1))
% 7.59/1.49      | ~ r1_tarski(sK4,u1_struct_0(sK1))
% 7.59/1.49      | ~ r1_tarski(sK3,u1_struct_0(sK1)) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_2785]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1201,plain,
% 7.59/1.49      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) = iProver_top
% 7.59/1.49      | r1_tarski(X0_46,X1_46) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_15,negated_conjecture,
% 7.59/1.49      ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
% 7.59/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_12,plain,
% 7.59/1.49      ( m1_connsp_2(X0,X1,X2)
% 7.59/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.59/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 7.59/1.49      | v2_struct_0(X1)
% 7.59/1.49      | ~ v2_pre_topc(X1)
% 7.59/1.49      | ~ l1_pre_topc(X1) ),
% 7.59/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_23,negated_conjecture,
% 7.59/1.49      ( ~ v2_struct_0(sK1) ),
% 7.59/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_398,plain,
% 7.59/1.49      ( m1_connsp_2(X0,X1,X2)
% 7.59/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.59/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 7.59/1.49      | ~ v2_pre_topc(X1)
% 7.59/1.49      | ~ l1_pre_topc(X1)
% 7.59/1.49      | sK1 != X1 ),
% 7.59/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_399,plain,
% 7.59/1.49      ( m1_connsp_2(X0,sK1,X1)
% 7.59/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.59/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 7.59/1.49      | ~ v2_pre_topc(sK1)
% 7.59/1.49      | ~ l1_pre_topc(sK1) ),
% 7.59/1.49      inference(unflattening,[status(thm)],[c_398]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_403,plain,
% 7.59/1.49      ( m1_connsp_2(X0,sK1,X1)
% 7.59/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.59/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_399,c_22,c_21]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_516,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.59/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
% 7.59/1.49      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
% 7.59/1.49      | sK2 != X0
% 7.59/1.49      | sK1 != sK1 ),
% 7.59/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_403]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_517,plain,
% 7.59/1.49      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 7.59/1.49      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 7.59/1.49      inference(unflattening,[status(thm)],[c_516]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_20,negated_conjecture,
% 7.59/1.49      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 7.59/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_519,plain,
% 7.59/1.49      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_517,c_20]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_733,plain,
% 7.59/1.49      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 7.59/1.49      inference(subtyping,[status(esa)],[c_519]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1209,plain,
% 7.59/1.49      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.59/1.49      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
% 7.59/1.49      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2320,plain,
% 7.59/1.49      ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top
% 7.59/1.49      | r1_tarski(k4_subset_1(u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK1)) != iProver_top ),
% 7.59/1.49      inference(superposition,[status(thm)],[c_1201,c_1209]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2321,plain,
% 7.59/1.49      ( ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
% 7.59/1.49      | ~ r1_tarski(k4_subset_1(u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK1)) ),
% 7.59/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_2320]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2,plain,
% 7.59/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.59/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_744,plain,
% 7.59/1.49      ( ~ r2_hidden(X0_46,X1_46)
% 7.59/1.49      | r2_hidden(X0_46,X2_46)
% 7.59/1.49      | ~ r1_tarski(X1_46,X2_46) ),
% 7.59/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1438,plain,
% 7.59/1.49      ( r2_hidden(sK2,X0_46)
% 7.59/1.49      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(sK1,sK4),X0_46) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_744]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_2275,plain,
% 7.59/1.49      ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
% 7.59/1.49      | ~ r2_hidden(sK2,k1_tops_1(sK1,sK4))
% 7.59/1.49      | ~ r1_tarski(k1_tops_1(sK1,sK4),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_1438]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_748,plain,( X0_46 = X0_46 ),theory(equality) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1702,plain,
% 7.59/1.49      ( k1_tops_1(sK1,sK4) = k1_tops_1(sK1,sK4) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_748]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1609,plain,
% 7.59/1.49      ( r1_tarski(sK3,u1_struct_0(sK1)) ),
% 7.59/1.49      inference(resolution,[status(thm)],[c_740,c_738]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1607,plain,
% 7.59/1.49      ( r1_tarski(sK4,u1_struct_0(sK1)) ),
% 7.59/1.49      inference(resolution,[status(thm)],[c_740,c_739]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1532,plain,
% 7.59/1.49      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_748]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_10,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | r1_tarski(k1_tops_1(X1,X0),X0)
% 7.59/1.49      | ~ l1_pre_topc(X1) ),
% 7.59/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_464,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | r1_tarski(k1_tops_1(X1,X0),X0)
% 7.59/1.49      | sK1 != X1 ),
% 7.59/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_465,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | r1_tarski(k1_tops_1(sK1,X0),X0) ),
% 7.59/1.49      inference(unflattening,[status(thm)],[c_464]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_735,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | r1_tarski(k1_tops_1(sK1,X0_46),X0_46) ),
% 7.59/1.49      inference(subtyping,[status(esa)],[c_465]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_1340,plain,
% 7.59/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.59/1.49      | r1_tarski(k1_tops_1(sK1,sK4),sK4) ),
% 7.59/1.49      inference(instantiation,[status(thm)],[c_735]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_16,negated_conjecture,
% 7.59/1.49      ( m1_connsp_2(sK4,sK1,sK2) ),
% 7.59/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_13,plain,
% 7.59/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.59/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.59/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 7.59/1.49      | v2_struct_0(X1)
% 7.59/1.49      | ~ v2_pre_topc(X1)
% 7.59/1.49      | ~ l1_pre_topc(X1) ),
% 7.59/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_14,plain,
% 7.59/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.59/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.59/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.59/1.49      | v2_struct_0(X1)
% 7.59/1.49      | ~ v2_pre_topc(X1)
% 7.59/1.49      | ~ l1_pre_topc(X1) ),
% 7.59/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_135,plain,
% 7.59/1.49      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.59/1.49      | ~ m1_connsp_2(X0,X1,X2)
% 7.59/1.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 7.59/1.49      | v2_struct_0(X1)
% 7.59/1.49      | ~ v2_pre_topc(X1)
% 7.59/1.49      | ~ l1_pre_topc(X1) ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_13,c_14]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_136,plain,
% 7.59/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.59/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.59/1.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 7.59/1.49      | v2_struct_0(X1)
% 7.59/1.49      | ~ v2_pre_topc(X1)
% 7.59/1.49      | ~ l1_pre_topc(X1) ),
% 7.59/1.49      inference(renaming,[status(thm)],[c_135]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_356,plain,
% 7.59/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 7.59/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 7.59/1.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 7.59/1.49      | ~ v2_pre_topc(X1)
% 7.59/1.49      | ~ l1_pre_topc(X1)
% 7.59/1.49      | sK1 != X1 ),
% 7.59/1.49      inference(resolution_lifted,[status(thm)],[c_136,c_23]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_357,plain,
% 7.59/1.49      ( ~ m1_connsp_2(X0,sK1,X1)
% 7.59/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.59/1.49      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 7.59/1.49      | ~ v2_pre_topc(sK1)
% 7.59/1.49      | ~ l1_pre_topc(sK1) ),
% 7.59/1.49      inference(unflattening,[status(thm)],[c_356]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_361,plain,
% 7.59/1.49      ( ~ m1_connsp_2(X0,sK1,X1)
% 7.59/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 7.59/1.49      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 7.59/1.49      inference(global_propositional_subsumption,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_357,c_22,c_21]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_532,plain,
% 7.59/1.49      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 7.59/1.49      | r2_hidden(X0,k1_tops_1(sK1,X1))
% 7.59/1.49      | sK2 != X0
% 7.59/1.49      | sK4 != X1
% 7.59/1.49      | sK1 != sK1 ),
% 7.59/1.49      inference(resolution_lifted,[status(thm)],[c_16,c_361]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(c_533,plain,
% 7.59/1.49      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 7.59/1.49      | r2_hidden(sK2,k1_tops_1(sK1,sK4)) ),
% 7.59/1.49      inference(unflattening,[status(thm)],[c_532]) ).
% 7.59/1.49  
% 7.59/1.49  cnf(contradiction,plain,
% 7.59/1.49      ( $false ),
% 7.59/1.49      inference(minisat,
% 7.59/1.49                [status(thm)],
% 7.59/1.49                [c_21038,c_21030,c_17877,c_17876,c_9034,c_5309,c_3321,
% 7.59/1.49                 c_3237,c_2321,c_2275,c_1702,c_1609,c_1607,c_1532,c_1340,
% 7.59/1.49                 c_533,c_18,c_20]) ).
% 7.59/1.49  
% 7.59/1.49  
% 7.59/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.59/1.49  
% 7.59/1.49  ------                               Statistics
% 7.59/1.49  
% 7.59/1.49  ------ Selected
% 7.59/1.49  
% 7.59/1.49  total_time:                             0.845
% 7.59/1.49  
%------------------------------------------------------------------------------
