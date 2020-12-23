%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1392+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:37 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  227 ( 866 expanded)
%              Number of clauses        :  137 ( 248 expanded)
%              Number of leaves         :   23 ( 213 expanded)
%              Depth                    :   24
%              Number of atoms          : 1008 (4699 expanded)
%              Number of equality atoms :  154 ( 232 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_connsp_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_connsp_1(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_connsp_2(X0)
         => ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_connsp_1(X1,X0)
               => v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v3_connsp_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & v1_connsp_2(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v3_connsp_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & v1_connsp_2(X0)
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v3_connsp_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK5,X0)
        & v3_connsp_1(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_pre_topc(X1,X0)
            & v3_connsp_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & v1_connsp_2(X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v3_pre_topc(X1,sK4)
          & v3_connsp_1(X1,sK4)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & v1_connsp_2(sK4)
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ~ v3_pre_topc(sK5,sK4)
    & v3_connsp_1(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v1_connsp_2(sK4)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f59,f58])).

fof(f94,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f60])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f91,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f92,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f75,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_connsp_2(X0,X1)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r2_hidden(X1,X3)
                        & r3_connsp_1(X0,X2,X3)
                        & m1_connsp_2(X2,X0,X1) )
                     => m1_connsp_2(X3,X0,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_connsp_2(X0,X1)
          <=> ! [X2] :
                ( ! [X3] :
                    ( m1_connsp_2(X3,X0,X1)
                    | ~ r2_hidden(X1,X3)
                    | ~ r3_connsp_1(X0,X2,X3)
                    | ~ m1_connsp_2(X2,X0,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_connsp_2(X0,X1)
          <=> ! [X2] :
                ( ! [X3] :
                    ( m1_connsp_2(X3,X0,X1)
                    | ~ r2_hidden(X1,X3)
                    | ~ r3_connsp_1(X0,X2,X3)
                    | ~ m1_connsp_2(X2,X0,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_connsp_2(X0,X1)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ m1_connsp_2(X3,X0,X1)
                      & r2_hidden(X1,X3)
                      & r3_connsp_1(X0,X2,X3)
                      & m1_connsp_2(X2,X0,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( m1_connsp_2(X3,X0,X1)
                      | ~ r2_hidden(X1,X3)
                      | ~ r3_connsp_1(X0,X2,X3)
                      | ~ m1_connsp_2(X2,X0,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r1_connsp_2(X0,X1) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_connsp_2(X0,X1)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ m1_connsp_2(X3,X0,X1)
                      & r2_hidden(X1,X3)
                      & r3_connsp_1(X0,X2,X3)
                      & m1_connsp_2(X2,X0,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( m1_connsp_2(X5,X0,X1)
                      | ~ r2_hidden(X1,X5)
                      | ~ r3_connsp_1(X0,X4,X5)
                      | ~ m1_connsp_2(X4,X0,X1)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r1_connsp_2(X0,X1) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f52])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ m1_connsp_2(X3,X0,X1)
          & r2_hidden(X1,X3)
          & r3_connsp_1(X0,X2,X3)
          & m1_connsp_2(X2,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ m1_connsp_2(sK3(X0,X1),X0,X1)
        & r2_hidden(X1,sK3(X0,X1))
        & r3_connsp_1(X0,X2,sK3(X0,X1))
        & m1_connsp_2(X2,X0,X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_connsp_2(X3,X0,X1)
              & r2_hidden(X1,X3)
              & r3_connsp_1(X0,X2,X3)
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ m1_connsp_2(X3,X0,X1)
            & r2_hidden(X1,X3)
            & r3_connsp_1(X0,sK2(X0,X1),X3)
            & m1_connsp_2(sK2(X0,X1),X0,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_connsp_2(X0,X1)
              | ( ~ m1_connsp_2(sK3(X0,X1),X0,X1)
                & r2_hidden(X1,sK3(X0,X1))
                & r3_connsp_1(X0,sK2(X0,X1),sK3(X0,X1))
                & m1_connsp_2(sK2(X0,X1),X0,X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( m1_connsp_2(X5,X0,X1)
                      | ~ r2_hidden(X1,X5)
                      | ~ r3_connsp_1(X0,X4,X5)
                      | ~ m1_connsp_2(X4,X0,X1)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r1_connsp_2(X0,X1) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f53,f55,f54])).

fof(f78,plain,(
    ! [X4,X0,X5,X1] :
      ( m1_connsp_2(X5,X0,X1)
      | ~ r2_hidden(X1,X5)
      | ~ r3_connsp_1(X0,X4,X5)
      | ~ m1_connsp_2(X4,X0,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_connsp_2(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_connsp_2(X0,X1)
      | r3_connsp_1(X0,sK2(X0,X1),sK3(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_connsp_2(X0,X1)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_connsp_2(X0,X1)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_connsp_2(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r1_connsp_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_connsp_2(X0)
      <=> ! [X1] :
            ( r1_connsp_2(X0,X1)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_connsp_2(X0)
      <=> ! [X1] :
            ( r1_connsp_2(X0,X1)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v1_connsp_2(X0)
          | ? [X1] :
              ( ~ r1_connsp_2(X0,X1)
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( r1_connsp_2(X0,X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_connsp_2(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v1_connsp_2(X0)
          | ? [X1] :
              ( ~ r1_connsp_2(X0,X1)
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X2] :
              ( r1_connsp_2(X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v1_connsp_2(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_connsp_2(X0,X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ r1_connsp_2(X0,sK1(X0))
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_connsp_2(X0)
          | ( ~ r1_connsp_2(X0,sK1(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) )
        & ( ! [X2] :
              ( r1_connsp_2(X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v1_connsp_2(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).

fof(f70,plain,(
    ! [X2,X0] :
      ( r1_connsp_2(X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_connsp_2(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f93,plain,(
    v1_connsp_2(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_connsp_1(X1,X0) )
               => r3_connsp_1(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_connsp_1(X0,X2,X1)
              | ~ r1_tarski(X1,X2)
              | ~ v3_connsp_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_connsp_1(X0,X2,X1)
              | ~ r1_tarski(X1,X2)
              | ~ v3_connsp_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r3_connsp_1(X0,X2,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v3_connsp_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f95,plain,(
    v3_connsp_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f96,plain,(
    ~ v3_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1737,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1740,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2388,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_1740])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1743,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1742,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3101,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1743,c_1742])).

cnf(c_4396,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3101,c_1742])).

cnf(c_5260,plain,
    ( r2_hidden(sK0(sK5,X0),X1) = iProver_top
    | r1_tarski(u1_struct_0(sK4),X1) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2388,c_4396])).

cnf(c_3,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_872,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_35])).

cnf(c_873,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k1_tops_1(sK4,X0))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_872])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_877,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,k1_tops_1(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_873,c_34,c_33])).

cnf(c_1734,plain,
    ( m1_connsp_2(X0,sK4,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK4,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_877])).

cnf(c_2540,plain,
    ( m1_connsp_2(sK5,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_1734])).

cnf(c_40,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_964,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_33])).

cnf(c_965,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_tops_1(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_964])).

cnf(c_1803,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_tops_1(sK4,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_1804,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k1_tops_1(sK4,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1803])).

cnf(c_27,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1812,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X0) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1920,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_1812])).

cnf(c_1921,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1920])).

cnf(c_1831,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,sK5)
    | ~ r1_tarski(X1,sK5) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1961,plain,
    ( ~ r2_hidden(X0,k1_tops_1(sK4,sK5))
    | r2_hidden(X0,sK5)
    | ~ r1_tarski(k1_tops_1(sK4,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_1831])).

cnf(c_1962,plain,
    ( r2_hidden(X0,k1_tops_1(sK4,sK5)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r1_tarski(k1_tops_1(sK4,sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1961])).

cnf(c_2629,plain,
    ( m1_connsp_2(sK5,sK4,X0) = iProver_top
    | r2_hidden(X0,k1_tops_1(sK4,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2540,c_40,c_1804,c_1921,c_1962])).

cnf(c_5375,plain,
    ( m1_connsp_2(sK5,sK4,sK0(sK5,X0)) = iProver_top
    | r1_tarski(u1_struct_0(sK4),k1_tops_1(sK4,sK5)) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5260,c_2629])).

cnf(c_13,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_12,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_464,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_13,c_12])).

cnf(c_957,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_464,c_33])).

cnf(c_958,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_957])).

cnf(c_1730,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_958])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_475,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_13,c_5])).

cnf(c_952,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_475,c_33])).

cnf(c_953,plain,
    ( k2_struct_0(sK4) = u1_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_952])).

cnf(c_1748,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1730,c_953])).

cnf(c_2047,plain,
    ( r2_hidden(sK0(sK5,X0),sK5)
    | r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2053,plain,
    ( r2_hidden(sK0(sK5,X0),sK5) = iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2047])).

cnf(c_1876,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2135,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1876])).

cnf(c_2141,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2135])).

cnf(c_28,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_819,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_35])).

cnf(c_820,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_819])).

cnf(c_824,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_820,c_34,c_33])).

cnf(c_840,plain,
    ( m1_connsp_2(X0,sK4,X1)
    | ~ v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_824,c_27])).

cnf(c_1736,plain,
    ( m1_connsp_2(X0,sK4,X1) = iProver_top
    | v3_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(c_2814,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK4,X0) = iProver_top
    | v3_pre_topc(u1_struct_0(sK4),sK4) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_1736])).

cnf(c_14,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_936,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_34])).

cnf(c_937,plain,
    ( v3_pre_topc(k2_struct_0(sK4),sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_936])).

cnf(c_84,plain,
    ( v3_pre_topc(k2_struct_0(sK4),sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_939,plain,
    ( v3_pre_topc(k2_struct_0(sK4),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_937,c_34,c_33,c_84])).

cnf(c_1731,plain,
    ( v3_pre_topc(k2_struct_0(sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_939])).

cnf(c_1747,plain,
    ( v3_pre_topc(u1_struct_0(sK4),sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1731,c_953])).

cnf(c_3485,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK4,X0) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2814,c_1747])).

cnf(c_23,plain,
    ( ~ r3_connsp_1(X0,X1,X2)
    | ~ m1_connsp_2(X1,X0,X3)
    | m1_connsp_2(X2,X0,X3)
    | ~ r1_connsp_2(X0,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X2)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_19,plain,
    ( r3_connsp_1(X0,sK2(X0,X1),sK3(X0,X1))
    | r1_connsp_2(X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_699,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(X3,X1,X2)
    | ~ r1_connsp_2(X1,X2)
    | r1_connsp_2(X4,X5)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ r2_hidden(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | X4 != X1
    | sK2(X4,X5) != X0
    | sK3(X4,X5) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_19])).

cnf(c_700,plain,
    ( ~ m1_connsp_2(sK2(X0,X1),X0,X2)
    | m1_connsp_2(sK3(X0,X1),X0,X2)
    | ~ r1_connsp_2(X0,X2)
    | r1_connsp_2(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,sK3(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_22,plain,
    ( r1_connsp_2(X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_21,plain,
    ( r1_connsp_2(X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_702,plain,
    ( ~ m1_connsp_2(sK2(X0,X1),X0,X2)
    | m1_connsp_2(sK3(X0,X1),X0,X2)
    | ~ r1_connsp_2(X0,X2)
    | r1_connsp_2(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(X2,sK3(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_700,c_22,c_21])).

cnf(c_703,plain,
    ( ~ m1_connsp_2(sK2(X0,X1),X0,X2)
    | m1_connsp_2(sK3(X0,X1),X0,X2)
    | ~ r1_connsp_2(X0,X2)
    | r1_connsp_2(X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,sK3(X0,X1))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_702])).

cnf(c_789,plain,
    ( ~ m1_connsp_2(sK2(X0,X1),X0,X2)
    | m1_connsp_2(sK3(X0,X1),X0,X2)
    | ~ r1_connsp_2(X0,X2)
    | r1_connsp_2(X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,sK3(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_703,c_35])).

cnf(c_790,plain,
    ( ~ m1_connsp_2(sK2(sK4,X0),sK4,X1)
    | m1_connsp_2(sK3(sK4,X0),sK4,X1)
    | ~ r1_connsp_2(sK4,X1)
    | r1_connsp_2(sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,sK3(sK4,X0))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_789])).

cnf(c_11,plain,
    ( r1_connsp_2(X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_connsp_2(X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,negated_conjecture,
    ( v1_connsp_2(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_563,plain,
    ( r1_connsp_2(X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_32])).

cnf(c_564,plain,
    ( r1_connsp_2(sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r1_connsp_2(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_564,c_35,c_34,c_33])).

cnf(c_569,plain,
    ( r1_connsp_2(sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(renaming,[status(thm)],[c_568])).

cnf(c_792,plain,
    ( r1_connsp_2(sK4,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_790,c_569])).

cnf(c_16,plain,
    ( r3_connsp_1(X0,X1,X2)
    | ~ v3_connsp_1(X2,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_30,negated_conjecture,
    ( v3_connsp_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_492,plain,
    ( r3_connsp_1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_30])).

cnf(c_493,plain,
    ( r3_connsp_1(sK4,X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(sK5,X0)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_497,plain,
    ( ~ r1_tarski(sK5,X0)
    | r3_connsp_1(sK4,X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_35,c_34,c_33,c_31])).

cnf(c_498,plain,
    ( r3_connsp_1(sK4,X0,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(sK5,X0) ),
    inference(renaming,[status(thm)],[c_497])).

cnf(c_737,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | m1_connsp_2(X3,X1,X2)
    | ~ r1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(sK5,X4)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | X4 != X0
    | sK4 != X1
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_498])).

cnf(c_738,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | m1_connsp_2(sK5,sK4,X1)
    | ~ r1_connsp_2(sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X1,sK5)
    | ~ r1_tarski(sK5,X0)
    | v2_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_737])).

cnf(c_742,plain,
    ( ~ r1_tarski(sK5,X0)
    | ~ r2_hidden(X1,sK5)
    | ~ m1_connsp_2(X0,sK4,X1)
    | m1_connsp_2(sK5,sK4,X1)
    | ~ r1_connsp_2(sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_738,c_35,c_34,c_33,c_31])).

cnf(c_743,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | m1_connsp_2(sK5,sK4,X1)
    | ~ r1_connsp_2(sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,sK5)
    | ~ r1_tarski(sK5,X0) ),
    inference(renaming,[status(thm)],[c_742])).

cnf(c_897,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | m1_connsp_2(sK5,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ r2_hidden(X1,sK5)
    | ~ r1_tarski(sK5,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_792,c_743])).

cnf(c_1733,plain,
    ( m1_connsp_2(X0,sK4,X1) != iProver_top
    | m1_connsp_2(sK5,sK4,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_897])).

cnf(c_2236,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK4,X0) != iProver_top
    | m1_connsp_2(sK5,sK4,X0) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_1733])).

cnf(c_1739,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3109,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_1739])).

cnf(c_3492,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | m1_connsp_2(u1_struct_0(sK4),sK4,X0) != iProver_top
    | m1_connsp_2(sK5,sK4,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2236,c_2388,c_3109])).

cnf(c_3493,plain,
    ( m1_connsp_2(u1_struct_0(sK4),sK4,X0) != iProver_top
    | m1_connsp_2(sK5,sK4,X0) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_3492])).

cnf(c_3498,plain,
    ( m1_connsp_2(sK5,sK4,X0) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3485,c_3493])).

cnf(c_5376,plain,
    ( m1_connsp_2(sK5,sK4,sK0(sK5,X0)) = iProver_top
    | r2_hidden(sK0(sK5,X0),sK5) != iProver_top
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5260,c_3498])).

cnf(c_5506,plain,
    ( m1_connsp_2(sK5,sK4,sK0(sK5,X0)) = iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5375,c_1748,c_2053,c_2141,c_5376])).

cnf(c_4,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_848,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_35])).

cnf(c_849,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k1_tops_1(sK4,X0))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_848])).

cnf(c_853,plain,
    ( ~ m1_connsp_2(X0,sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | r2_hidden(X1,k1_tops_1(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_849,c_34,c_33])).

cnf(c_1735,plain,
    ( m1_connsp_2(X0,sK4,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X1,k1_tops_1(sK4,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_2641,plain,
    ( m1_connsp_2(sK5,sK4,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0,k1_tops_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_1735])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1744,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2928,plain,
    ( m1_connsp_2(sK5,sK4,sK0(X0,k1_tops_1(sK4,sK5))) != iProver_top
    | m1_subset_1(sK0(X0,k1_tops_1(sK4,sK5)),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2641,c_1744])).

cnf(c_5514,plain,
    ( m1_subset_1(sK0(sK5,k1_tops_1(sK4,sK5)),u1_struct_0(sK4)) != iProver_top
    | r1_tarski(sK5,k1_tops_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5506,c_2928])).

cnf(c_1282,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1777,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(sK5,sK4)
    | sK4 != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_3617,plain,
    ( ~ v3_pre_topc(k1_tops_1(X0,X1),sK4)
    | v3_pre_topc(sK5,sK4)
    | sK4 != sK4
    | sK5 != k1_tops_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1777])).

cnf(c_4885,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK4,sK5),sK4)
    | v3_pre_topc(sK5,sK4)
    | sK4 != sK4
    | sK5 != k1_tops_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3617])).

cnf(c_3869,plain,
    ( m1_subset_1(sK0(sK5,k1_tops_1(sK4,sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK5,k1_tops_1(sK4,sK5)),sK5) ),
    inference(instantiation,[status(thm)],[c_1920])).

cnf(c_3870,plain,
    ( m1_subset_1(sK0(sK5,k1_tops_1(sK4,sK5)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK0(sK5,k1_tops_1(sK4,sK5)),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3869])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1860,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3187,plain,
    ( ~ r1_tarski(k1_tops_1(sK4,sK5),sK5)
    | ~ r1_tarski(sK5,k1_tops_1(sK4,sK5))
    | sK5 = k1_tops_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1860])).

cnf(c_3188,plain,
    ( sK5 = k1_tops_1(sK4,sK5)
    | r1_tarski(k1_tops_1(sK4,sK5),sK5) != iProver_top
    | r1_tarski(sK5,k1_tops_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3187])).

cnf(c_2554,plain,
    ( r2_hidden(sK0(sK5,k1_tops_1(sK4,sK5)),sK5)
    | r1_tarski(sK5,k1_tops_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_2047])).

cnf(c_2559,plain,
    ( r2_hidden(sK0(sK5,k1_tops_1(sK4,sK5)),sK5) = iProver_top
    | r1_tarski(sK5,k1_tops_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2554])).

cnf(c_15,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_918,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_34])).

cnf(c_919,plain,
    ( v3_pre_topc(k1_tops_1(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_918])).

cnf(c_923,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v3_pre_topc(k1_tops_1(sK4,X0),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_919,c_33])).

cnf(c_924,plain,
    ( v3_pre_topc(k1_tops_1(sK4,X0),sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_923])).

cnf(c_1782,plain,
    ( v3_pre_topc(k1_tops_1(sK4,sK5),sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_924])).

cnf(c_118,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_114,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_29,negated_conjecture,
    ( ~ v3_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5514,c_4885,c_3870,c_3188,c_2559,c_1804,c_1782,c_118,c_114,c_29,c_40,c_31])).


%------------------------------------------------------------------------------
