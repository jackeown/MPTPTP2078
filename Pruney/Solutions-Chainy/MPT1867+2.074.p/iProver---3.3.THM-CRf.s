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
% DateTime   : Thu Dec  3 12:26:20 EST 2020

% Result     : Theorem 15.62s
% Output     : CNFRefutation 15.62s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 219 expanded)
%              Number of clauses        :   63 (  89 expanded)
%              Number of leaves         :   16 (  45 expanded)
%              Depth                    :   20
%              Number of atoms          :  379 ( 809 expanded)
%              Number of equality atoms :  124 ( 164 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK0(X0),X0)
        & ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK0(X0),X0)
        & ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f35])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f40,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
        & v4_pre_topc(sK2(X0,X1,X4),X0)
        & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
                    & v4_pre_topc(sK2(X0,X1,X4),X0)
                    & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f40,f39])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ~ v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f43,f42])).

fof(f71,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    ! [X0] :
      ( v4_pre_topc(sK0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1170,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1175,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1173,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1970,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1175,c_1173])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_196,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_197,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_196])).

cnf(c_241,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_197])).

cnf(c_1157,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_5122,plain,
    ( k9_subset_1(X0,k1_xboole_0,X1) = k9_subset_1(X0,X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1970,c_1157])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_244,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_197])).

cnf(c_1154,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_244])).

cnf(c_4407,plain,
    ( k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1970,c_1154])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1179,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4405,plain,
    ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1179,c_1154])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_242,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_197])).

cnf(c_1156,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_242])).

cnf(c_4555,plain,
    ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4405,c_1156])).

cnf(c_23895,plain,
    ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4555,c_1179])).

cnf(c_23899,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_23895,c_1173])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1177,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_24034,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_23899,c_1177])).

cnf(c_77075,plain,
    ( k9_subset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4407,c_24034])).

cnf(c_78953,plain,
    ( k9_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5122,c_77075])).

cnf(c_17,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1169,plain,
    ( k9_subset_1(u1_struct_0(X0),X1,X2) != sK1(X0,X1)
    | v2_tex_2(X1,X0) = iProver_top
    | v4_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_79141,plain,
    ( sK1(X0,k1_xboole_0) != k1_xboole_0
    | v2_tex_2(k1_xboole_0,X0) = iProver_top
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_78953,c_1169])).

cnf(c_1466,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1471,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1466])).

cnf(c_18,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1168,plain,
    ( v2_tex_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(sK1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2707,plain,
    ( v2_tex_2(k1_xboole_0,X0) = iProver_top
    | r1_tarski(sK1(X0,k1_xboole_0),k1_xboole_0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1175,c_1168])).

cnf(c_5181,plain,
    ( sK1(X0,k1_xboole_0) = k1_xboole_0
    | v2_tex_2(k1_xboole_0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2707,c_1177])).

cnf(c_79239,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v4_pre_topc(X1,X0) != iProver_top
    | v2_tex_2(k1_xboole_0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_79141,c_1471,c_5181])).

cnf(c_79240,plain,
    ( v2_tex_2(k1_xboole_0,X0) = iProver_top
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_79239])).

cnf(c_79253,plain,
    ( v2_tex_2(k1_xboole_0,X0) = iProver_top
    | v4_pre_topc(sK0(X0),X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_79240])).

cnf(c_79345,plain,
    ( v2_tex_2(k1_xboole_0,sK3) = iProver_top
    | v4_pre_topc(sK0(sK3),sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_79253])).

cnf(c_25,negated_conjecture,
    ( v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1161,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1181,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1704,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1161,c_1181])).

cnf(c_23,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1163,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3110,plain,
    ( v2_tex_2(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1704,c_1163])).

cnf(c_14,plain,
    ( v4_pre_topc(sK0(X0),X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_59,plain,
    ( v4_pre_topc(sK0(X0),X0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_61,plain,
    ( v4_pre_topc(sK0(sK3),sK3) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_31,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_30,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79345,c_3110,c_61,c_31,c_30,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:51:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 15.62/2.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.62/2.48  
% 15.62/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.62/2.48  
% 15.62/2.48  ------  iProver source info
% 15.62/2.48  
% 15.62/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.62/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.62/2.48  git: non_committed_changes: false
% 15.62/2.48  git: last_make_outside_of_git: false
% 15.62/2.48  
% 15.62/2.48  ------ 
% 15.62/2.48  
% 15.62/2.48  ------ Input Options
% 15.62/2.48  
% 15.62/2.48  --out_options                           all
% 15.62/2.48  --tptp_safe_out                         true
% 15.62/2.48  --problem_path                          ""
% 15.62/2.48  --include_path                          ""
% 15.62/2.48  --clausifier                            res/vclausify_rel
% 15.62/2.48  --clausifier_options                    --mode clausify
% 15.62/2.48  --stdin                                 false
% 15.62/2.48  --stats_out                             sel
% 15.62/2.48  
% 15.62/2.48  ------ General Options
% 15.62/2.48  
% 15.62/2.48  --fof                                   false
% 15.62/2.48  --time_out_real                         604.99
% 15.62/2.48  --time_out_virtual                      -1.
% 15.62/2.48  --symbol_type_check                     false
% 15.62/2.48  --clausify_out                          false
% 15.62/2.48  --sig_cnt_out                           false
% 15.62/2.48  --trig_cnt_out                          false
% 15.62/2.48  --trig_cnt_out_tolerance                1.
% 15.62/2.48  --trig_cnt_out_sk_spl                   false
% 15.62/2.48  --abstr_cl_out                          false
% 15.62/2.48  
% 15.62/2.48  ------ Global Options
% 15.62/2.48  
% 15.62/2.48  --schedule                              none
% 15.62/2.48  --add_important_lit                     false
% 15.62/2.48  --prop_solver_per_cl                    1000
% 15.62/2.48  --min_unsat_core                        false
% 15.62/2.48  --soft_assumptions                      false
% 15.62/2.48  --soft_lemma_size                       3
% 15.62/2.48  --prop_impl_unit_size                   0
% 15.62/2.48  --prop_impl_unit                        []
% 15.62/2.48  --share_sel_clauses                     true
% 15.62/2.48  --reset_solvers                         false
% 15.62/2.48  --bc_imp_inh                            [conj_cone]
% 15.62/2.48  --conj_cone_tolerance                   3.
% 15.62/2.48  --extra_neg_conj                        none
% 15.62/2.48  --large_theory_mode                     true
% 15.62/2.48  --prolific_symb_bound                   200
% 15.62/2.48  --lt_threshold                          2000
% 15.62/2.48  --clause_weak_htbl                      true
% 15.62/2.48  --gc_record_bc_elim                     false
% 15.62/2.48  
% 15.62/2.48  ------ Preprocessing Options
% 15.62/2.48  
% 15.62/2.48  --preprocessing_flag                    true
% 15.62/2.48  --time_out_prep_mult                    0.1
% 15.62/2.48  --splitting_mode                        input
% 15.62/2.48  --splitting_grd                         true
% 15.62/2.48  --splitting_cvd                         false
% 15.62/2.48  --splitting_cvd_svl                     false
% 15.62/2.48  --splitting_nvd                         32
% 15.62/2.48  --sub_typing                            true
% 15.62/2.48  --prep_gs_sim                           false
% 15.62/2.48  --prep_unflatten                        true
% 15.62/2.48  --prep_res_sim                          true
% 15.62/2.48  --prep_upred                            true
% 15.62/2.48  --prep_sem_filter                       exhaustive
% 15.62/2.48  --prep_sem_filter_out                   false
% 15.62/2.48  --pred_elim                             false
% 15.62/2.48  --res_sim_input                         true
% 15.62/2.48  --eq_ax_congr_red                       true
% 15.62/2.48  --pure_diseq_elim                       true
% 15.62/2.48  --brand_transform                       false
% 15.62/2.48  --non_eq_to_eq                          false
% 15.62/2.48  --prep_def_merge                        true
% 15.62/2.48  --prep_def_merge_prop_impl              false
% 15.62/2.48  --prep_def_merge_mbd                    true
% 15.62/2.48  --prep_def_merge_tr_red                 false
% 15.62/2.48  --prep_def_merge_tr_cl                  false
% 15.62/2.48  --smt_preprocessing                     true
% 15.62/2.48  --smt_ac_axioms                         fast
% 15.62/2.48  --preprocessed_out                      false
% 15.62/2.48  --preprocessed_stats                    false
% 15.62/2.48  
% 15.62/2.48  ------ Abstraction refinement Options
% 15.62/2.48  
% 15.62/2.48  --abstr_ref                             []
% 15.62/2.48  --abstr_ref_prep                        false
% 15.62/2.48  --abstr_ref_until_sat                   false
% 15.62/2.48  --abstr_ref_sig_restrict                funpre
% 15.62/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.62/2.48  --abstr_ref_under                       []
% 15.62/2.48  
% 15.62/2.48  ------ SAT Options
% 15.62/2.48  
% 15.62/2.48  --sat_mode                              false
% 15.62/2.48  --sat_fm_restart_options                ""
% 15.62/2.48  --sat_gr_def                            false
% 15.62/2.48  --sat_epr_types                         true
% 15.62/2.48  --sat_non_cyclic_types                  false
% 15.62/2.48  --sat_finite_models                     false
% 15.62/2.48  --sat_fm_lemmas                         false
% 15.62/2.48  --sat_fm_prep                           false
% 15.62/2.48  --sat_fm_uc_incr                        true
% 15.62/2.48  --sat_out_model                         small
% 15.62/2.48  --sat_out_clauses                       false
% 15.62/2.48  
% 15.62/2.48  ------ QBF Options
% 15.62/2.48  
% 15.62/2.48  --qbf_mode                              false
% 15.62/2.48  --qbf_elim_univ                         false
% 15.62/2.48  --qbf_dom_inst                          none
% 15.62/2.48  --qbf_dom_pre_inst                      false
% 15.62/2.48  --qbf_sk_in                             false
% 15.62/2.48  --qbf_pred_elim                         true
% 15.62/2.48  --qbf_split                             512
% 15.62/2.48  
% 15.62/2.48  ------ BMC1 Options
% 15.62/2.48  
% 15.62/2.48  --bmc1_incremental                      false
% 15.62/2.48  --bmc1_axioms                           reachable_all
% 15.62/2.48  --bmc1_min_bound                        0
% 15.62/2.48  --bmc1_max_bound                        -1
% 15.62/2.48  --bmc1_max_bound_default                -1
% 15.62/2.48  --bmc1_symbol_reachability              true
% 15.62/2.48  --bmc1_property_lemmas                  false
% 15.62/2.48  --bmc1_k_induction                      false
% 15.62/2.48  --bmc1_non_equiv_states                 false
% 15.62/2.48  --bmc1_deadlock                         false
% 15.62/2.48  --bmc1_ucm                              false
% 15.62/2.48  --bmc1_add_unsat_core                   none
% 15.62/2.48  --bmc1_unsat_core_children              false
% 15.62/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.62/2.48  --bmc1_out_stat                         full
% 15.62/2.48  --bmc1_ground_init                      false
% 15.62/2.48  --bmc1_pre_inst_next_state              false
% 15.62/2.48  --bmc1_pre_inst_state                   false
% 15.62/2.48  --bmc1_pre_inst_reach_state             false
% 15.62/2.48  --bmc1_out_unsat_core                   false
% 15.62/2.48  --bmc1_aig_witness_out                  false
% 15.62/2.48  --bmc1_verbose                          false
% 15.62/2.48  --bmc1_dump_clauses_tptp                false
% 15.62/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.62/2.48  --bmc1_dump_file                        -
% 15.62/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.62/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.62/2.48  --bmc1_ucm_extend_mode                  1
% 15.62/2.48  --bmc1_ucm_init_mode                    2
% 15.62/2.48  --bmc1_ucm_cone_mode                    none
% 15.62/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.62/2.48  --bmc1_ucm_relax_model                  4
% 15.62/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.62/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.62/2.48  --bmc1_ucm_layered_model                none
% 15.62/2.48  --bmc1_ucm_max_lemma_size               10
% 15.62/2.48  
% 15.62/2.48  ------ AIG Options
% 15.62/2.48  
% 15.62/2.48  --aig_mode                              false
% 15.62/2.48  
% 15.62/2.48  ------ Instantiation Options
% 15.62/2.48  
% 15.62/2.48  --instantiation_flag                    true
% 15.62/2.48  --inst_sos_flag                         false
% 15.62/2.48  --inst_sos_phase                        true
% 15.62/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.62/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.62/2.48  --inst_lit_sel_side                     num_symb
% 15.62/2.48  --inst_solver_per_active                1400
% 15.62/2.48  --inst_solver_calls_frac                1.
% 15.62/2.48  --inst_passive_queue_type               priority_queues
% 15.62/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.62/2.48  --inst_passive_queues_freq              [25;2]
% 15.62/2.48  --inst_dismatching                      true
% 15.62/2.48  --inst_eager_unprocessed_to_passive     true
% 15.62/2.48  --inst_prop_sim_given                   true
% 15.62/2.48  --inst_prop_sim_new                     false
% 15.62/2.48  --inst_subs_new                         false
% 15.62/2.48  --inst_eq_res_simp                      false
% 15.62/2.48  --inst_subs_given                       false
% 15.62/2.48  --inst_orphan_elimination               true
% 15.62/2.48  --inst_learning_loop_flag               true
% 15.62/2.48  --inst_learning_start                   3000
% 15.62/2.48  --inst_learning_factor                  2
% 15.62/2.48  --inst_start_prop_sim_after_learn       3
% 15.62/2.48  --inst_sel_renew                        solver
% 15.62/2.48  --inst_lit_activity_flag                true
% 15.62/2.48  --inst_restr_to_given                   false
% 15.62/2.48  --inst_activity_threshold               500
% 15.62/2.48  --inst_out_proof                        true
% 15.62/2.48  
% 15.62/2.48  ------ Resolution Options
% 15.62/2.48  
% 15.62/2.48  --resolution_flag                       true
% 15.62/2.48  --res_lit_sel                           adaptive
% 15.62/2.48  --res_lit_sel_side                      none
% 15.62/2.48  --res_ordering                          kbo
% 15.62/2.48  --res_to_prop_solver                    active
% 15.62/2.48  --res_prop_simpl_new                    false
% 15.62/2.48  --res_prop_simpl_given                  true
% 15.62/2.48  --res_passive_queue_type                priority_queues
% 15.62/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.62/2.48  --res_passive_queues_freq               [15;5]
% 15.62/2.48  --res_forward_subs                      full
% 15.62/2.48  --res_backward_subs                     full
% 15.62/2.48  --res_forward_subs_resolution           true
% 15.62/2.48  --res_backward_subs_resolution          true
% 15.62/2.48  --res_orphan_elimination                true
% 15.62/2.48  --res_time_limit                        2.
% 15.62/2.48  --res_out_proof                         true
% 15.62/2.48  
% 15.62/2.48  ------ Superposition Options
% 15.62/2.48  
% 15.62/2.48  --superposition_flag                    true
% 15.62/2.48  --sup_passive_queue_type                priority_queues
% 15.62/2.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.62/2.48  --sup_passive_queues_freq               [1;4]
% 15.62/2.48  --demod_completeness_check              fast
% 15.62/2.48  --demod_use_ground                      true
% 15.62/2.48  --sup_to_prop_solver                    passive
% 15.62/2.48  --sup_prop_simpl_new                    true
% 15.62/2.48  --sup_prop_simpl_given                  true
% 15.62/2.48  --sup_fun_splitting                     false
% 15.62/2.48  --sup_smt_interval                      50000
% 15.62/2.48  
% 15.62/2.48  ------ Superposition Simplification Setup
% 15.62/2.48  
% 15.62/2.48  --sup_indices_passive                   []
% 15.62/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.62/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.62/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.62/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.62/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.62/2.48  --sup_full_bw                           [BwDemod]
% 15.62/2.48  --sup_immed_triv                        [TrivRules]
% 15.62/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.62/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.62/2.48  --sup_immed_bw_main                     []
% 15.62/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.62/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.62/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.62/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.62/2.48  
% 15.62/2.48  ------ Combination Options
% 15.62/2.48  
% 15.62/2.48  --comb_res_mult                         3
% 15.62/2.48  --comb_sup_mult                         2
% 15.62/2.48  --comb_inst_mult                        10
% 15.62/2.48  
% 15.62/2.48  ------ Debug Options
% 15.62/2.48  
% 15.62/2.48  --dbg_backtrace                         false
% 15.62/2.48  --dbg_dump_prop_clauses                 false
% 15.62/2.48  --dbg_dump_prop_clauses_file            -
% 15.62/2.48  --dbg_out_stat                          false
% 15.62/2.48  ------ Parsing...
% 15.62/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.62/2.48  
% 15.62/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.62/2.48  
% 15.62/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.62/2.48  
% 15.62/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.62/2.48  ------ Proving...
% 15.62/2.48  ------ Problem Properties 
% 15.62/2.48  
% 15.62/2.48  
% 15.62/2.48  clauses                                 28
% 15.62/2.48  conjectures                             6
% 15.62/2.48  EPR                                     10
% 15.62/2.48  Horn                                    24
% 15.62/2.48  unary                                   9
% 15.62/2.48  binary                                  8
% 15.62/2.48  lits                                    75
% 15.62/2.48  lits eq                                 8
% 15.62/2.48  fd_pure                                 0
% 15.62/2.48  fd_pseudo                               0
% 15.62/2.48  fd_cond                                 2
% 15.62/2.48  fd_pseudo_cond                          1
% 15.62/2.48  AC symbols                              0
% 15.62/2.48  
% 15.62/2.48  ------ Input Options Time Limit: Unbounded
% 15.62/2.48  
% 15.62/2.48  
% 15.62/2.48  ------ 
% 15.62/2.48  Current options:
% 15.62/2.48  ------ 
% 15.62/2.48  
% 15.62/2.48  ------ Input Options
% 15.62/2.48  
% 15.62/2.48  --out_options                           all
% 15.62/2.48  --tptp_safe_out                         true
% 15.62/2.48  --problem_path                          ""
% 15.62/2.48  --include_path                          ""
% 15.62/2.48  --clausifier                            res/vclausify_rel
% 15.62/2.48  --clausifier_options                    --mode clausify
% 15.62/2.48  --stdin                                 false
% 15.62/2.48  --stats_out                             sel
% 15.62/2.48  
% 15.62/2.48  ------ General Options
% 15.62/2.48  
% 15.62/2.48  --fof                                   false
% 15.62/2.48  --time_out_real                         604.99
% 15.62/2.48  --time_out_virtual                      -1.
% 15.62/2.48  --symbol_type_check                     false
% 15.62/2.48  --clausify_out                          false
% 15.62/2.48  --sig_cnt_out                           false
% 15.62/2.48  --trig_cnt_out                          false
% 15.62/2.48  --trig_cnt_out_tolerance                1.
% 15.62/2.48  --trig_cnt_out_sk_spl                   false
% 15.62/2.48  --abstr_cl_out                          false
% 15.62/2.48  
% 15.62/2.48  ------ Global Options
% 15.62/2.48  
% 15.62/2.48  --schedule                              none
% 15.62/2.48  --add_important_lit                     false
% 15.62/2.48  --prop_solver_per_cl                    1000
% 15.62/2.48  --min_unsat_core                        false
% 15.62/2.48  --soft_assumptions                      false
% 15.62/2.48  --soft_lemma_size                       3
% 15.62/2.48  --prop_impl_unit_size                   0
% 15.62/2.48  --prop_impl_unit                        []
% 15.62/2.48  --share_sel_clauses                     true
% 15.62/2.48  --reset_solvers                         false
% 15.62/2.48  --bc_imp_inh                            [conj_cone]
% 15.62/2.48  --conj_cone_tolerance                   3.
% 15.62/2.48  --extra_neg_conj                        none
% 15.62/2.48  --large_theory_mode                     true
% 15.62/2.48  --prolific_symb_bound                   200
% 15.62/2.48  --lt_threshold                          2000
% 15.62/2.48  --clause_weak_htbl                      true
% 15.62/2.48  --gc_record_bc_elim                     false
% 15.62/2.48  
% 15.62/2.48  ------ Preprocessing Options
% 15.62/2.48  
% 15.62/2.48  --preprocessing_flag                    true
% 15.62/2.48  --time_out_prep_mult                    0.1
% 15.62/2.48  --splitting_mode                        input
% 15.62/2.48  --splitting_grd                         true
% 15.62/2.48  --splitting_cvd                         false
% 15.62/2.48  --splitting_cvd_svl                     false
% 15.62/2.48  --splitting_nvd                         32
% 15.62/2.48  --sub_typing                            true
% 15.62/2.48  --prep_gs_sim                           false
% 15.62/2.48  --prep_unflatten                        true
% 15.62/2.48  --prep_res_sim                          true
% 15.62/2.48  --prep_upred                            true
% 15.62/2.48  --prep_sem_filter                       exhaustive
% 15.62/2.48  --prep_sem_filter_out                   false
% 15.62/2.48  --pred_elim                             false
% 15.62/2.48  --res_sim_input                         true
% 15.62/2.48  --eq_ax_congr_red                       true
% 15.62/2.48  --pure_diseq_elim                       true
% 15.62/2.48  --brand_transform                       false
% 15.62/2.48  --non_eq_to_eq                          false
% 15.62/2.48  --prep_def_merge                        true
% 15.62/2.48  --prep_def_merge_prop_impl              false
% 15.62/2.48  --prep_def_merge_mbd                    true
% 15.62/2.48  --prep_def_merge_tr_red                 false
% 15.62/2.48  --prep_def_merge_tr_cl                  false
% 15.62/2.48  --smt_preprocessing                     true
% 15.62/2.48  --smt_ac_axioms                         fast
% 15.62/2.48  --preprocessed_out                      false
% 15.62/2.48  --preprocessed_stats                    false
% 15.62/2.48  
% 15.62/2.48  ------ Abstraction refinement Options
% 15.62/2.48  
% 15.62/2.48  --abstr_ref                             []
% 15.62/2.48  --abstr_ref_prep                        false
% 15.62/2.48  --abstr_ref_until_sat                   false
% 15.62/2.48  --abstr_ref_sig_restrict                funpre
% 15.62/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.62/2.48  --abstr_ref_under                       []
% 15.62/2.48  
% 15.62/2.48  ------ SAT Options
% 15.62/2.48  
% 15.62/2.48  --sat_mode                              false
% 15.62/2.48  --sat_fm_restart_options                ""
% 15.62/2.48  --sat_gr_def                            false
% 15.62/2.48  --sat_epr_types                         true
% 15.62/2.48  --sat_non_cyclic_types                  false
% 15.62/2.48  --sat_finite_models                     false
% 15.62/2.48  --sat_fm_lemmas                         false
% 15.62/2.48  --sat_fm_prep                           false
% 15.62/2.48  --sat_fm_uc_incr                        true
% 15.62/2.48  --sat_out_model                         small
% 15.62/2.48  --sat_out_clauses                       false
% 15.62/2.48  
% 15.62/2.48  ------ QBF Options
% 15.62/2.48  
% 15.62/2.48  --qbf_mode                              false
% 15.62/2.48  --qbf_elim_univ                         false
% 15.62/2.48  --qbf_dom_inst                          none
% 15.62/2.48  --qbf_dom_pre_inst                      false
% 15.62/2.48  --qbf_sk_in                             false
% 15.62/2.48  --qbf_pred_elim                         true
% 15.62/2.48  --qbf_split                             512
% 15.62/2.48  
% 15.62/2.48  ------ BMC1 Options
% 15.62/2.48  
% 15.62/2.48  --bmc1_incremental                      false
% 15.62/2.48  --bmc1_axioms                           reachable_all
% 15.62/2.48  --bmc1_min_bound                        0
% 15.62/2.48  --bmc1_max_bound                        -1
% 15.62/2.48  --bmc1_max_bound_default                -1
% 15.62/2.48  --bmc1_symbol_reachability              true
% 15.62/2.48  --bmc1_property_lemmas                  false
% 15.62/2.48  --bmc1_k_induction                      false
% 15.62/2.48  --bmc1_non_equiv_states                 false
% 15.62/2.48  --bmc1_deadlock                         false
% 15.62/2.48  --bmc1_ucm                              false
% 15.62/2.48  --bmc1_add_unsat_core                   none
% 15.62/2.48  --bmc1_unsat_core_children              false
% 15.62/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.62/2.48  --bmc1_out_stat                         full
% 15.62/2.48  --bmc1_ground_init                      false
% 15.62/2.48  --bmc1_pre_inst_next_state              false
% 15.62/2.48  --bmc1_pre_inst_state                   false
% 15.62/2.48  --bmc1_pre_inst_reach_state             false
% 15.62/2.48  --bmc1_out_unsat_core                   false
% 15.62/2.48  --bmc1_aig_witness_out                  false
% 15.62/2.48  --bmc1_verbose                          false
% 15.62/2.48  --bmc1_dump_clauses_tptp                false
% 15.62/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.62/2.48  --bmc1_dump_file                        -
% 15.62/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.62/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.62/2.48  --bmc1_ucm_extend_mode                  1
% 15.62/2.48  --bmc1_ucm_init_mode                    2
% 15.62/2.48  --bmc1_ucm_cone_mode                    none
% 15.62/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.62/2.48  --bmc1_ucm_relax_model                  4
% 15.62/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.62/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.62/2.48  --bmc1_ucm_layered_model                none
% 15.62/2.48  --bmc1_ucm_max_lemma_size               10
% 15.62/2.48  
% 15.62/2.48  ------ AIG Options
% 15.62/2.48  
% 15.62/2.48  --aig_mode                              false
% 15.62/2.48  
% 15.62/2.48  ------ Instantiation Options
% 15.62/2.48  
% 15.62/2.48  --instantiation_flag                    true
% 15.62/2.48  --inst_sos_flag                         false
% 15.62/2.48  --inst_sos_phase                        true
% 15.62/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.62/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.62/2.48  --inst_lit_sel_side                     num_symb
% 15.62/2.48  --inst_solver_per_active                1400
% 15.62/2.48  --inst_solver_calls_frac                1.
% 15.62/2.48  --inst_passive_queue_type               priority_queues
% 15.62/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.62/2.48  --inst_passive_queues_freq              [25;2]
% 15.62/2.48  --inst_dismatching                      true
% 15.62/2.48  --inst_eager_unprocessed_to_passive     true
% 15.62/2.48  --inst_prop_sim_given                   true
% 15.62/2.48  --inst_prop_sim_new                     false
% 15.62/2.48  --inst_subs_new                         false
% 15.62/2.48  --inst_eq_res_simp                      false
% 15.62/2.48  --inst_subs_given                       false
% 15.62/2.48  --inst_orphan_elimination               true
% 15.62/2.48  --inst_learning_loop_flag               true
% 15.62/2.48  --inst_learning_start                   3000
% 15.62/2.48  --inst_learning_factor                  2
% 15.62/2.48  --inst_start_prop_sim_after_learn       3
% 15.62/2.48  --inst_sel_renew                        solver
% 15.62/2.48  --inst_lit_activity_flag                true
% 15.62/2.48  --inst_restr_to_given                   false
% 15.62/2.48  --inst_activity_threshold               500
% 15.62/2.48  --inst_out_proof                        true
% 15.62/2.48  
% 15.62/2.48  ------ Resolution Options
% 15.62/2.48  
% 15.62/2.48  --resolution_flag                       true
% 15.62/2.48  --res_lit_sel                           adaptive
% 15.62/2.48  --res_lit_sel_side                      none
% 15.62/2.48  --res_ordering                          kbo
% 15.62/2.48  --res_to_prop_solver                    active
% 15.62/2.48  --res_prop_simpl_new                    false
% 15.62/2.48  --res_prop_simpl_given                  true
% 15.62/2.48  --res_passive_queue_type                priority_queues
% 15.62/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.62/2.48  --res_passive_queues_freq               [15;5]
% 15.62/2.48  --res_forward_subs                      full
% 15.62/2.48  --res_backward_subs                     full
% 15.62/2.48  --res_forward_subs_resolution           true
% 15.62/2.48  --res_backward_subs_resolution          true
% 15.62/2.48  --res_orphan_elimination                true
% 15.62/2.48  --res_time_limit                        2.
% 15.62/2.48  --res_out_proof                         true
% 15.62/2.48  
% 15.62/2.48  ------ Superposition Options
% 15.62/2.48  
% 15.62/2.48  --superposition_flag                    true
% 15.62/2.48  --sup_passive_queue_type                priority_queues
% 15.62/2.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.62/2.48  --sup_passive_queues_freq               [1;4]
% 15.62/2.48  --demod_completeness_check              fast
% 15.62/2.48  --demod_use_ground                      true
% 15.62/2.48  --sup_to_prop_solver                    passive
% 15.62/2.48  --sup_prop_simpl_new                    true
% 15.62/2.48  --sup_prop_simpl_given                  true
% 15.62/2.48  --sup_fun_splitting                     false
% 15.62/2.48  --sup_smt_interval                      50000
% 15.62/2.48  
% 15.62/2.48  ------ Superposition Simplification Setup
% 15.62/2.48  
% 15.62/2.48  --sup_indices_passive                   []
% 15.62/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.62/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.62/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.62/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.62/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.62/2.48  --sup_full_bw                           [BwDemod]
% 15.62/2.48  --sup_immed_triv                        [TrivRules]
% 15.62/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.62/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.62/2.48  --sup_immed_bw_main                     []
% 15.62/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.62/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.62/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.62/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.62/2.48  
% 15.62/2.48  ------ Combination Options
% 15.62/2.48  
% 15.62/2.48  --comb_res_mult                         3
% 15.62/2.48  --comb_sup_mult                         2
% 15.62/2.48  --comb_inst_mult                        10
% 15.62/2.48  
% 15.62/2.48  ------ Debug Options
% 15.62/2.48  
% 15.62/2.48  --dbg_backtrace                         false
% 15.62/2.48  --dbg_dump_prop_clauses                 false
% 15.62/2.48  --dbg_dump_prop_clauses_file            -
% 15.62/2.48  --dbg_out_stat                          false
% 15.62/2.48  
% 15.62/2.48  
% 15.62/2.48  
% 15.62/2.48  
% 15.62/2.48  ------ Proving...
% 15.62/2.48  
% 15.62/2.48  
% 15.62/2.48  % SZS status Theorem for theBenchmark.p
% 15.62/2.48  
% 15.62/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.62/2.48  
% 15.62/2.48  fof(f13,axiom,(
% 15.62/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f26,plain,(
% 15.62/2.48    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.62/2.48    inference(ennf_transformation,[],[f13])).
% 15.62/2.48  
% 15.62/2.48  fof(f27,plain,(
% 15.62/2.48    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.62/2.48    inference(flattening,[],[f26])).
% 15.62/2.48  
% 15.62/2.48  fof(f35,plain,(
% 15.62/2.48    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK0(X0),X0) & ~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.62/2.48    introduced(choice_axiom,[])).
% 15.62/2.48  
% 15.62/2.48  fof(f36,plain,(
% 15.62/2.48    ! [X0] : ((v4_pre_topc(sK0(X0),X0) & ~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.62/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f35])).
% 15.62/2.48  
% 15.62/2.48  fof(f59,plain,(
% 15.62/2.48    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.62/2.48    inference(cnf_transformation,[],[f36])).
% 15.62/2.48  
% 15.62/2.48  fof(f10,axiom,(
% 15.62/2.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f56,plain,(
% 15.62/2.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 15.62/2.48    inference(cnf_transformation,[],[f10])).
% 15.62/2.48  
% 15.62/2.48  fof(f11,axiom,(
% 15.62/2.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f34,plain,(
% 15.62/2.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.62/2.48    inference(nnf_transformation,[],[f11])).
% 15.62/2.48  
% 15.62/2.48  fof(f57,plain,(
% 15.62/2.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.62/2.48    inference(cnf_transformation,[],[f34])).
% 15.62/2.48  
% 15.62/2.48  fof(f5,axiom,(
% 15.62/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f22,plain,(
% 15.62/2.48    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.62/2.48    inference(ennf_transformation,[],[f5])).
% 15.62/2.48  
% 15.62/2.48  fof(f51,plain,(
% 15.62/2.48    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.62/2.48    inference(cnf_transformation,[],[f22])).
% 15.62/2.48  
% 15.62/2.48  fof(f58,plain,(
% 15.62/2.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.62/2.48    inference(cnf_transformation,[],[f34])).
% 15.62/2.48  
% 15.62/2.48  fof(f9,axiom,(
% 15.62/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f25,plain,(
% 15.62/2.48    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.62/2.48    inference(ennf_transformation,[],[f9])).
% 15.62/2.48  
% 15.62/2.48  fof(f55,plain,(
% 15.62/2.48    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.62/2.48    inference(cnf_transformation,[],[f25])).
% 15.62/2.48  
% 15.62/2.48  fof(f2,axiom,(
% 15.62/2.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f32,plain,(
% 15.62/2.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.62/2.48    inference(nnf_transformation,[],[f2])).
% 15.62/2.48  
% 15.62/2.48  fof(f33,plain,(
% 15.62/2.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.62/2.48    inference(flattening,[],[f32])).
% 15.62/2.48  
% 15.62/2.48  fof(f46,plain,(
% 15.62/2.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.62/2.48    inference(cnf_transformation,[],[f33])).
% 15.62/2.48  
% 15.62/2.48  fof(f75,plain,(
% 15.62/2.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.62/2.48    inference(equality_resolution,[],[f46])).
% 15.62/2.48  
% 15.62/2.48  fof(f7,axiom,(
% 15.62/2.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f23,plain,(
% 15.62/2.48    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.62/2.48    inference(ennf_transformation,[],[f7])).
% 15.62/2.48  
% 15.62/2.48  fof(f53,plain,(
% 15.62/2.48    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.62/2.48    inference(cnf_transformation,[],[f23])).
% 15.62/2.48  
% 15.62/2.48  fof(f4,axiom,(
% 15.62/2.48    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f21,plain,(
% 15.62/2.48    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 15.62/2.48    inference(ennf_transformation,[],[f4])).
% 15.62/2.48  
% 15.62/2.48  fof(f50,plain,(
% 15.62/2.48    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 15.62/2.48    inference(cnf_transformation,[],[f21])).
% 15.62/2.48  
% 15.62/2.48  fof(f14,axiom,(
% 15.62/2.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f28,plain,(
% 15.62/2.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.62/2.48    inference(ennf_transformation,[],[f14])).
% 15.62/2.48  
% 15.62/2.48  fof(f29,plain,(
% 15.62/2.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.62/2.48    inference(flattening,[],[f28])).
% 15.62/2.48  
% 15.62/2.48  fof(f37,plain,(
% 15.62/2.48    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.62/2.48    inference(nnf_transformation,[],[f29])).
% 15.62/2.48  
% 15.62/2.48  fof(f38,plain,(
% 15.62/2.48    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.62/2.48    inference(rectify,[],[f37])).
% 15.62/2.48  
% 15.62/2.48  fof(f40,plain,(
% 15.62/2.48    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v4_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.62/2.48    introduced(choice_axiom,[])).
% 15.62/2.48  
% 15.62/2.48  fof(f39,plain,(
% 15.62/2.48    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.62/2.48    introduced(choice_axiom,[])).
% 15.62/2.48  
% 15.62/2.48  fof(f41,plain,(
% 15.62/2.48    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v4_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.62/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f40,f39])).
% 15.62/2.48  
% 15.62/2.48  fof(f67,plain,(
% 15.62/2.48    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.62/2.48    inference(cnf_transformation,[],[f41])).
% 15.62/2.48  
% 15.62/2.48  fof(f66,plain,(
% 15.62/2.48    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.62/2.48    inference(cnf_transformation,[],[f41])).
% 15.62/2.48  
% 15.62/2.48  fof(f15,conjecture,(
% 15.62/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f16,negated_conjecture,(
% 15.62/2.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 15.62/2.48    inference(negated_conjecture,[],[f15])).
% 15.62/2.48  
% 15.62/2.48  fof(f30,plain,(
% 15.62/2.48    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 15.62/2.48    inference(ennf_transformation,[],[f16])).
% 15.62/2.48  
% 15.62/2.48  fof(f31,plain,(
% 15.62/2.48    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 15.62/2.48    inference(flattening,[],[f30])).
% 15.62/2.48  
% 15.62/2.48  fof(f43,plain,(
% 15.62/2.48    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK4))) )),
% 15.62/2.48    introduced(choice_axiom,[])).
% 15.62/2.48  
% 15.62/2.48  fof(f42,plain,(
% 15.62/2.48    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 15.62/2.48    introduced(choice_axiom,[])).
% 15.62/2.48  
% 15.62/2.48  fof(f44,plain,(
% 15.62/2.48    (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 15.62/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f43,f42])).
% 15.62/2.48  
% 15.62/2.48  fof(f71,plain,(
% 15.62/2.48    v1_xboole_0(sK4)),
% 15.62/2.48    inference(cnf_transformation,[],[f44])).
% 15.62/2.48  
% 15.62/2.48  fof(f1,axiom,(
% 15.62/2.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 15.62/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.62/2.48  
% 15.62/2.48  fof(f18,plain,(
% 15.62/2.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 15.62/2.48    inference(ennf_transformation,[],[f1])).
% 15.62/2.48  
% 15.62/2.48  fof(f45,plain,(
% 15.62/2.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 15.62/2.48    inference(cnf_transformation,[],[f18])).
% 15.62/2.48  
% 15.62/2.48  fof(f73,plain,(
% 15.62/2.48    ~v2_tex_2(sK4,sK3)),
% 15.62/2.48    inference(cnf_transformation,[],[f44])).
% 15.62/2.48  
% 15.62/2.48  fof(f61,plain,(
% 15.62/2.48    ( ! [X0] : (v4_pre_topc(sK0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.62/2.48    inference(cnf_transformation,[],[f36])).
% 15.62/2.48  
% 15.62/2.48  fof(f70,plain,(
% 15.62/2.48    l1_pre_topc(sK3)),
% 15.62/2.48    inference(cnf_transformation,[],[f44])).
% 15.62/2.48  
% 15.62/2.48  fof(f69,plain,(
% 15.62/2.48    v2_pre_topc(sK3)),
% 15.62/2.48    inference(cnf_transformation,[],[f44])).
% 15.62/2.48  
% 15.62/2.48  fof(f68,plain,(
% 15.62/2.48    ~v2_struct_0(sK3)),
% 15.62/2.48    inference(cnf_transformation,[],[f44])).
% 15.62/2.48  
% 15.62/2.48  cnf(c_16,plain,
% 15.62/2.48      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 15.62/2.48      | v2_struct_0(X0)
% 15.62/2.48      | ~ v2_pre_topc(X0)
% 15.62/2.48      | ~ l1_pre_topc(X0) ),
% 15.62/2.48      inference(cnf_transformation,[],[f59]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1170,plain,
% 15.62/2.48      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.62/2.48      | v2_struct_0(X0) = iProver_top
% 15.62/2.48      | v2_pre_topc(X0) != iProver_top
% 15.62/2.48      | l1_pre_topc(X0) != iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_11,plain,
% 15.62/2.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 15.62/2.48      inference(cnf_transformation,[],[f56]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1175,plain,
% 15.62/2.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_13,plain,
% 15.62/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.62/2.48      inference(cnf_transformation,[],[f57]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1173,plain,
% 15.62/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.62/2.48      | r1_tarski(X0,X1) = iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1970,plain,
% 15.62/2.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_1175,c_1173]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_6,plain,
% 15.62/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.62/2.48      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 15.62/2.48      inference(cnf_transformation,[],[f51]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_12,plain,
% 15.62/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.62/2.48      inference(cnf_transformation,[],[f58]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_196,plain,
% 15.62/2.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.62/2.48      inference(prop_impl,[status(thm)],[c_12]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_197,plain,
% 15.62/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.62/2.48      inference(renaming,[status(thm)],[c_196]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_241,plain,
% 15.62/2.48      ( ~ r1_tarski(X0,X1)
% 15.62/2.48      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 15.62/2.48      inference(bin_hyper_res,[status(thm)],[c_6,c_197]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1157,plain,
% 15.62/2.48      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 15.62/2.48      | r1_tarski(X1,X0) != iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_241]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_5122,plain,
% 15.62/2.48      ( k9_subset_1(X0,k1_xboole_0,X1) = k9_subset_1(X0,X1,k1_xboole_0) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_1970,c_1157]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_10,plain,
% 15.62/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.62/2.48      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 15.62/2.48      inference(cnf_transformation,[],[f55]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_244,plain,
% 15.62/2.48      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 15.62/2.48      inference(bin_hyper_res,[status(thm)],[c_10,c_197]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1154,plain,
% 15.62/2.48      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 15.62/2.48      | r1_tarski(X2,X0) != iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_244]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_4407,plain,
% 15.62/2.48      ( k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_1970,c_1154]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_3,plain,
% 15.62/2.48      ( r1_tarski(X0,X0) ),
% 15.62/2.48      inference(cnf_transformation,[],[f75]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1179,plain,
% 15.62/2.48      ( r1_tarski(X0,X0) = iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_4405,plain,
% 15.62/2.48      ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_1179,c_1154]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_8,plain,
% 15.62/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.62/2.48      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 15.62/2.48      inference(cnf_transformation,[],[f53]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_242,plain,
% 15.62/2.48      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 15.62/2.48      | ~ r1_tarski(X2,X0) ),
% 15.62/2.48      inference(bin_hyper_res,[status(thm)],[c_8,c_197]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1156,plain,
% 15.62/2.48      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 15.62/2.48      | r1_tarski(X2,X0) != iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_242]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_4555,plain,
% 15.62/2.48      ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top
% 15.62/2.48      | r1_tarski(X1,X1) != iProver_top ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_4405,c_1156]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_23895,plain,
% 15.62/2.48      ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top ),
% 15.62/2.48      inference(forward_subsumption_resolution,
% 15.62/2.48                [status(thm)],
% 15.62/2.48                [c_4555,c_1179]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_23899,plain,
% 15.62/2.48      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_23895,c_1173]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_5,plain,
% 15.62/2.48      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 15.62/2.48      inference(cnf_transformation,[],[f50]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1177,plain,
% 15.62/2.48      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_24034,plain,
% 15.62/2.48      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_23899,c_1177]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_77075,plain,
% 15.62/2.48      ( k9_subset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_4407,c_24034]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_78953,plain,
% 15.62/2.48      ( k9_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0 ),
% 15.62/2.48      inference(light_normalisation,[status(thm)],[c_5122,c_77075]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_17,plain,
% 15.62/2.48      ( v2_tex_2(X0,X1)
% 15.62/2.48      | ~ v4_pre_topc(X2,X1)
% 15.62/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.62/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.62/2.48      | ~ l1_pre_topc(X1)
% 15.62/2.48      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
% 15.62/2.48      inference(cnf_transformation,[],[f67]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1169,plain,
% 15.62/2.48      ( k9_subset_1(u1_struct_0(X0),X1,X2) != sK1(X0,X1)
% 15.62/2.48      | v2_tex_2(X1,X0) = iProver_top
% 15.62/2.48      | v4_pre_topc(X2,X0) != iProver_top
% 15.62/2.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.62/2.48      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.62/2.48      | l1_pre_topc(X0) != iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_79141,plain,
% 15.62/2.48      ( sK1(X0,k1_xboole_0) != k1_xboole_0
% 15.62/2.48      | v2_tex_2(k1_xboole_0,X0) = iProver_top
% 15.62/2.48      | v4_pre_topc(X1,X0) != iProver_top
% 15.62/2.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.62/2.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.62/2.48      | l1_pre_topc(X0) != iProver_top ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_78953,c_1169]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1466,plain,
% 15.62/2.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) ),
% 15.62/2.48      inference(instantiation,[status(thm)],[c_11]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1471,plain,
% 15.62/2.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_1466]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_18,plain,
% 15.62/2.48      ( v2_tex_2(X0,X1)
% 15.62/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.62/2.48      | r1_tarski(sK1(X1,X0),X0)
% 15.62/2.48      | ~ l1_pre_topc(X1) ),
% 15.62/2.48      inference(cnf_transformation,[],[f66]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1168,plain,
% 15.62/2.48      ( v2_tex_2(X0,X1) = iProver_top
% 15.62/2.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.62/2.48      | r1_tarski(sK1(X1,X0),X0) = iProver_top
% 15.62/2.48      | l1_pre_topc(X1) != iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_2707,plain,
% 15.62/2.48      ( v2_tex_2(k1_xboole_0,X0) = iProver_top
% 15.62/2.48      | r1_tarski(sK1(X0,k1_xboole_0),k1_xboole_0) = iProver_top
% 15.62/2.48      | l1_pre_topc(X0) != iProver_top ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_1175,c_1168]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_5181,plain,
% 15.62/2.48      ( sK1(X0,k1_xboole_0) = k1_xboole_0
% 15.62/2.48      | v2_tex_2(k1_xboole_0,X0) = iProver_top
% 15.62/2.48      | l1_pre_topc(X0) != iProver_top ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_2707,c_1177]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_79239,plain,
% 15.62/2.48      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.62/2.48      | v4_pre_topc(X1,X0) != iProver_top
% 15.62/2.48      | v2_tex_2(k1_xboole_0,X0) = iProver_top
% 15.62/2.48      | l1_pre_topc(X0) != iProver_top ),
% 15.62/2.48      inference(global_propositional_subsumption,
% 15.62/2.48                [status(thm)],
% 15.62/2.48                [c_79141,c_1471,c_5181]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_79240,plain,
% 15.62/2.48      ( v2_tex_2(k1_xboole_0,X0) = iProver_top
% 15.62/2.48      | v4_pre_topc(X1,X0) != iProver_top
% 15.62/2.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.62/2.48      | l1_pre_topc(X0) != iProver_top ),
% 15.62/2.48      inference(renaming,[status(thm)],[c_79239]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_79253,plain,
% 15.62/2.48      ( v2_tex_2(k1_xboole_0,X0) = iProver_top
% 15.62/2.48      | v4_pre_topc(sK0(X0),X0) != iProver_top
% 15.62/2.48      | v2_struct_0(X0) = iProver_top
% 15.62/2.48      | v2_pre_topc(X0) != iProver_top
% 15.62/2.48      | l1_pre_topc(X0) != iProver_top ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_1170,c_79240]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_79345,plain,
% 15.62/2.48      ( v2_tex_2(k1_xboole_0,sK3) = iProver_top
% 15.62/2.48      | v4_pre_topc(sK0(sK3),sK3) != iProver_top
% 15.62/2.48      | v2_struct_0(sK3) = iProver_top
% 15.62/2.48      | v2_pre_topc(sK3) != iProver_top
% 15.62/2.48      | l1_pre_topc(sK3) != iProver_top ),
% 15.62/2.48      inference(instantiation,[status(thm)],[c_79253]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_25,negated_conjecture,
% 15.62/2.48      ( v1_xboole_0(sK4) ),
% 15.62/2.48      inference(cnf_transformation,[],[f71]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1161,plain,
% 15.62/2.48      ( v1_xboole_0(sK4) = iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_0,plain,
% 15.62/2.48      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 15.62/2.48      inference(cnf_transformation,[],[f45]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1181,plain,
% 15.62/2.48      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1704,plain,
% 15.62/2.48      ( sK4 = k1_xboole_0 ),
% 15.62/2.48      inference(superposition,[status(thm)],[c_1161,c_1181]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_23,negated_conjecture,
% 15.62/2.48      ( ~ v2_tex_2(sK4,sK3) ),
% 15.62/2.48      inference(cnf_transformation,[],[f73]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_1163,plain,
% 15.62/2.48      ( v2_tex_2(sK4,sK3) != iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_3110,plain,
% 15.62/2.48      ( v2_tex_2(k1_xboole_0,sK3) != iProver_top ),
% 15.62/2.48      inference(demodulation,[status(thm)],[c_1704,c_1163]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_14,plain,
% 15.62/2.48      ( v4_pre_topc(sK0(X0),X0)
% 15.62/2.48      | v2_struct_0(X0)
% 15.62/2.48      | ~ v2_pre_topc(X0)
% 15.62/2.48      | ~ l1_pre_topc(X0) ),
% 15.62/2.48      inference(cnf_transformation,[],[f61]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_59,plain,
% 15.62/2.48      ( v4_pre_topc(sK0(X0),X0) = iProver_top
% 15.62/2.48      | v2_struct_0(X0) = iProver_top
% 15.62/2.48      | v2_pre_topc(X0) != iProver_top
% 15.62/2.48      | l1_pre_topc(X0) != iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_61,plain,
% 15.62/2.48      ( v4_pre_topc(sK0(sK3),sK3) = iProver_top
% 15.62/2.48      | v2_struct_0(sK3) = iProver_top
% 15.62/2.48      | v2_pre_topc(sK3) != iProver_top
% 15.62/2.48      | l1_pre_topc(sK3) != iProver_top ),
% 15.62/2.48      inference(instantiation,[status(thm)],[c_59]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_26,negated_conjecture,
% 15.62/2.48      ( l1_pre_topc(sK3) ),
% 15.62/2.48      inference(cnf_transformation,[],[f70]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_31,plain,
% 15.62/2.48      ( l1_pre_topc(sK3) = iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_27,negated_conjecture,
% 15.62/2.48      ( v2_pre_topc(sK3) ),
% 15.62/2.48      inference(cnf_transformation,[],[f69]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_30,plain,
% 15.62/2.48      ( v2_pre_topc(sK3) = iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_28,negated_conjecture,
% 15.62/2.48      ( ~ v2_struct_0(sK3) ),
% 15.62/2.48      inference(cnf_transformation,[],[f68]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(c_29,plain,
% 15.62/2.48      ( v2_struct_0(sK3) != iProver_top ),
% 15.62/2.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.62/2.48  
% 15.62/2.48  cnf(contradiction,plain,
% 15.62/2.48      ( $false ),
% 15.62/2.48      inference(minisat,
% 15.62/2.48                [status(thm)],
% 15.62/2.48                [c_79345,c_3110,c_61,c_31,c_30,c_29]) ).
% 15.62/2.48  
% 15.62/2.48  
% 15.62/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.62/2.48  
% 15.62/2.48  ------                               Statistics
% 15.62/2.48  
% 15.62/2.48  ------ Selected
% 15.62/2.48  
% 15.62/2.48  total_time:                             1.837
% 15.62/2.48  
%------------------------------------------------------------------------------
