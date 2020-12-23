%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1859+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:41 EST 2020

% Result     : Theorem 43.51s
% Output     : CNFRefutation 43.51s
% Verified   : 
% Statistics : Number of formulae       :  295 (17974 expanded)
%              Number of clauses        :  206 (5541 expanded)
%              Number of leaves         :   22 (3539 expanded)
%              Depth                    :   36
%              Number of atoms          :  958 (82907 expanded)
%              Number of equality atoms :  429 (18464 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( u1_struct_0(X0) = X1
             => ( v2_tex_2(X1,X0)
              <=> v1_tdlat_3(X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( u1_struct_0(X0) = X1
             => ( v2_tex_2(X1,X0)
              <=> v1_tdlat_3(X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_tdlat_3(X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_tdlat_3(X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tdlat_3(X0)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_tdlat_3(X0)
            | v2_tex_2(X1,X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tdlat_3(X0)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_tdlat_3(X0)
            | v2_tex_2(X1,X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_tdlat_3(X0)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_tdlat_3(X0)
            | v2_tex_2(X1,X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v1_tdlat_3(X0)
          | ~ v2_tex_2(sK5,X0) )
        & ( v1_tdlat_3(X0)
          | v2_tex_2(sK5,X0) )
        & u1_struct_0(X0) = sK5
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_tdlat_3(X0)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_tdlat_3(X0)
              | v2_tex_2(X1,X0) )
            & u1_struct_0(X0) = X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v1_tdlat_3(sK4)
            | ~ v2_tex_2(X1,sK4) )
          & ( v1_tdlat_3(sK4)
            | v2_tex_2(X1,sK4) )
          & u1_struct_0(sK4) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ~ v1_tdlat_3(sK4)
      | ~ v2_tex_2(sK5,sK4) )
    & ( v1_tdlat_3(sK4)
      | v2_tex_2(sK5,sK4) )
    & u1_struct_0(sK4) = sK5
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f54,f56,f55])).

fof(f88,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    u1_struct_0(sK4) = sK5 ),
    inference(cnf_transformation,[],[f57])).

fof(f7,axiom,(
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
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v3_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f43])).

fof(f46,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
        & v3_pre_topc(sK2(X0,X1,X4),X0)
        & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
                    & v3_pre_topc(sK2(X0,X1,X4),X0)
                    & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f44,f46,f45])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f87,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0)) )
        & ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f93,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) = k1_zfmisc_1(u1_struct_0(X0))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f63,f78])).

fof(f90,plain,
    ( v1_tdlat_3(sK4)
    | v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK2(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f64,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | u1_pre_topc(X0) != k1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f64,f78])).

fof(f91,plain,
    ( ~ v1_tdlat_3(sK4)
    | ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f58,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK3(X0),X0)
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).

fof(f80,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3630,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( u1_struct_0(sK4) = sK5 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3644,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3630,c_30])).

cnf(c_13,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_632,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_633,plain,
    ( v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK1(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_3619,plain,
    ( v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK1(sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_3727,plain,
    ( v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(sK1(sK4,X0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3619,c_30])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3633,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4363,plain,
    ( k3_xboole_0(sK1(sK4,X0),X0) = sK1(sK4,X0)
    | v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3727,c_3633])).

cnf(c_6929,plain,
    ( k3_xboole_0(sK1(sK4,sK5),sK5) = sK1(sK4,sK5)
    | v2_tex_2(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3644,c_4363])).

cnf(c_8,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3636,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_24,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3634,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4812,plain,
    ( m1_subset_1(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3636,c_3634])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3631,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6572,plain,
    ( r1_tarski(sK0(k1_zfmisc_1(X0),X1),X0) = iProver_top
    | r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4812,c_3631])).

cnf(c_7382,plain,
    ( k3_xboole_0(sK0(k1_zfmisc_1(X0),X1),X0) = sK0(k1_zfmisc_1(X0),X1)
    | r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6572,c_3633])).

cnf(c_19,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_532,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_32])).

cnf(c_533,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_3624,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_3649,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(sK5))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3624,c_30])).

cnf(c_4585,plain,
    ( r1_tarski(u1_pre_topc(sK4),k1_zfmisc_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3649,c_3631])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3639,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5483,plain,
    ( k1_zfmisc_1(sK5) = u1_pre_topc(sK4)
    | r1_tarski(k1_zfmisc_1(sK5),u1_pre_topc(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4585,c_3639])).

cnf(c_8188,plain,
    ( k3_xboole_0(sK0(k1_zfmisc_1(sK5),u1_pre_topc(sK4)),sK5) = sK0(k1_zfmisc_1(sK5),u1_pre_topc(sK4))
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_7382,c_5483])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_103615,plain,
    ( k3_xboole_0(sK5,sK0(k1_zfmisc_1(sK5),u1_pre_topc(sK4))) = sK0(k1_zfmisc_1(sK5),u1_pre_topc(sK4))
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_8188,c_1])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3638,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_251,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_252,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_251])).

cnf(c_311,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_20,c_252])).

cnf(c_3628,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_6679,plain,
    ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3638,c_3628])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_310,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_18,c_252])).

cnf(c_3629,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_7269,plain,
    ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6679,c_3629])).

cnf(c_34162,plain,
    ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7269,c_3638])).

cnf(c_34166,plain,
    ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_34162])).

cnf(c_34792,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_34166,c_3631])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_tdlat_3(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) = u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_29,negated_conjecture,
    ( v2_tex_2(sK5,sK4)
    | v1_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_255,plain,
    ( v1_tdlat_3(sK4)
    | v2_tex_2(sK5,sK4) ),
    inference(prop_impl,[status(thm)],[c_29])).

cnf(c_256,plain,
    ( v2_tex_2(sK5,sK4)
    | v1_tdlat_3(sK4) ),
    inference(renaming,[status(thm)],[c_255])).

cnf(c_482,plain,
    ( v2_tex_2(sK5,sK4)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) = u1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_256])).

cnf(c_483,plain,
    ( v2_tex_2(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) = u1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_2306,plain,
    ( v2_tex_2(sK5,sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) = u1_pre_topc(sK4) ),
    inference(prop_impl,[status(thm)],[c_32,c_483])).

cnf(c_3626,plain,
    ( k1_zfmisc_1(u1_struct_0(sK4)) = u1_pre_topc(sK4)
    | v2_tex_2(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2306])).

cnf(c_3652,plain,
    ( k1_zfmisc_1(sK5) = u1_pre_topc(sK4)
    | v2_tex_2(sK5,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3626,c_30])).

cnf(c_17,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_554,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_32])).

cnf(c_555,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_3623,plain,
    ( v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_3774,plain,
    ( v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(sK5)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3623,c_30])).

cnf(c_4587,plain,
    ( v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK2(sK4,X0,X1),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3774,c_3631])).

cnf(c_6682,plain,
    ( k9_subset_1(sK5,X0,sK2(sK4,X1,X2)) = k3_xboole_0(X0,sK2(sK4,X1,X2))
    | v2_tex_2(X1,sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4587,c_3628])).

cnf(c_13101,plain,
    ( k9_subset_1(sK5,X0,sK2(sK4,sK5,X1)) = k3_xboole_0(X0,sK2(sK4,sK5,X1))
    | v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3644,c_6682])).

cnf(c_3632,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13280,plain,
    ( k9_subset_1(sK5,X0,sK2(sK4,sK5,X1)) = k3_xboole_0(X0,sK2(sK4,sK5,X1))
    | v2_tex_2(sK5,sK4) != iProver_top
    | r1_tarski(X1,sK5) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13101,c_3632])).

cnf(c_13288,plain,
    ( k9_subset_1(sK5,X0,sK2(sK4,sK5,X1)) = k3_xboole_0(X0,sK2(sK4,sK5,X1))
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4)
    | r1_tarski(X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3652,c_13280])).

cnf(c_41465,plain,
    ( k9_subset_1(sK5,X0,sK2(sK4,sK5,k3_xboole_0(sK5,X1))) = k3_xboole_0(X0,sK2(sK4,sK5,k3_xboole_0(sK5,X1)))
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_34792,c_13288])).

cnf(c_15,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK2(X1,X0,X2)) = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_596,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | k9_subset_1(u1_struct_0(X1),X0,sK2(X1,X0,X2)) = X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_597,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK4),X0,sK2(sK4,X0,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_3621,plain,
    ( k9_subset_1(u1_struct_0(sK4),X0,sK2(sK4,X0,X1)) = X1
    | v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_3763,plain,
    ( k9_subset_1(sK5,X0,sK2(sK4,X0,X1)) = X1
    | v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3621,c_30])).

cnf(c_4200,plain,
    ( k9_subset_1(sK5,sK5,sK2(sK4,sK5,X0)) = X0
    | v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3644,c_3763])).

cnf(c_3982,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5))
    | r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3983,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(X0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3982])).

cnf(c_5038,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | v2_tex_2(sK5,sK4) != iProver_top
    | k9_subset_1(sK5,sK5,sK2(sK4,sK5,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4200,c_3983])).

cnf(c_5039,plain,
    ( k9_subset_1(sK5,sK5,sK2(sK4,sK5,X0)) = X0
    | v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5038])).

cnf(c_34801,plain,
    ( k9_subset_1(sK5,sK5,sK2(sK4,sK5,k3_xboole_0(sK5,X0))) = k3_xboole_0(sK5,X0)
    | v2_tex_2(sK5,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_34166,c_5039])).

cnf(c_39827,plain,
    ( k9_subset_1(sK5,sK5,sK2(sK4,sK5,k3_xboole_0(sK5,X0))) = k3_xboole_0(sK5,X0)
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_3652,c_34801])).

cnf(c_47613,plain,
    ( k3_xboole_0(sK5,sK2(sK4,sK5,k3_xboole_0(sK5,X0))) = k3_xboole_0(sK5,X0)
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_41465,c_39827])).

cnf(c_5230,plain,
    ( k3_xboole_0(sK2(sK4,X0,X1),sK5) = sK2(sK4,X0,X1)
    | v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4587,c_3633])).

cnf(c_11609,plain,
    ( k3_xboole_0(sK2(sK4,sK5,X0),sK5) = sK2(sK4,sK5,X0)
    | v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3644,c_5230])).

cnf(c_5275,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5))
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_5276,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5)) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5275])).

cnf(c_11850,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | k3_xboole_0(sK2(sK4,sK5,X0),sK5) = sK2(sK4,sK5,X0)
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11609,c_5276])).

cnf(c_11851,plain,
    ( k3_xboole_0(sK2(sK4,sK5,X0),sK5) = sK2(sK4,sK5,X0)
    | v2_tex_2(sK5,sK4) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_11850])).

cnf(c_11863,plain,
    ( k3_xboole_0(sK2(sK4,sK5,X0),sK5) = sK2(sK4,sK5,X0)
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4)
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3652,c_11851])).

cnf(c_41477,plain,
    ( k3_xboole_0(sK2(sK4,sK5,k3_xboole_0(sK5,X0)),sK5) = sK2(sK4,sK5,k3_xboole_0(sK5,X0))
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_34792,c_11863])).

cnf(c_43535,plain,
    ( k3_xboole_0(sK5,sK2(sK4,sK5,k3_xboole_0(sK5,X0))) = sK2(sK4,sK5,k3_xboole_0(sK5,X0))
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_41477,c_1])).

cnf(c_48597,plain,
    ( sK2(sK4,sK5,k3_xboole_0(sK5,X0)) = k3_xboole_0(sK5,X0)
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_47613,c_43535])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(sK2(X1,X0,X2),X1)
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_575,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(sK2(X1,X0,X2),X1)
    | ~ r1_tarski(X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_576,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v3_pre_topc(sK2(sK4,X0,X1),sK4)
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_3622,plain,
    ( v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v3_pre_topc(sK2(sK4,X0,X1),sK4) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_3741,plain,
    ( v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK5)) != iProver_top
    | v3_pre_topc(sK2(sK4,X0,X1),sK4) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3622,c_30])).

cnf(c_178704,plain,
    ( k1_zfmisc_1(sK5) = u1_pre_topc(sK4)
    | v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(k3_xboole_0(sK5,X0),k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK5)) != iProver_top
    | v3_pre_topc(k3_xboole_0(sK5,X0),sK4) = iProver_top
    | r1_tarski(k3_xboole_0(sK5,X0),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_48597,c_3741])).

cnf(c_5,plain,
    ( ~ l1_pre_topc(X0)
    | v1_tdlat_3(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_28,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK4)
    | ~ v1_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_253,plain,
    ( ~ v1_tdlat_3(sK4)
    | ~ v2_tex_2(sK5,sK4) ),
    inference(prop_impl,[status(thm)],[c_28])).

cnf(c_254,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | ~ v1_tdlat_3(sK4) ),
    inference(renaming,[status(thm)],[c_253])).

cnf(c_468,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != u1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_254])).

cnf(c_469,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) != u1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_2304,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) != u1_pre_topc(sK4) ),
    inference(prop_impl,[status(thm)],[c_32,c_469])).

cnf(c_3627,plain,
    ( k1_zfmisc_1(u1_struct_0(sK4)) != u1_pre_topc(sK4)
    | v2_tex_2(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2304])).

cnf(c_3677,plain,
    ( k1_zfmisc_1(sK5) != u1_pre_topc(sK4)
    | v2_tex_2(sK5,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3627,c_30])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X2)
    | ~ v1_tdlat_3(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2
    | k1_zfmisc_1(u1_struct_0(X2)) != u1_pre_topc(X2) ),
    inference(resolution_lifted,[status(thm)],[c_5,c_426])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k1_zfmisc_1(u1_struct_0(X1)) != u1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | k1_zfmisc_1(u1_struct_0(X1)) != u1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_451,c_32])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v3_pre_topc(X0,sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) != u1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_1502,plain,
    ( v2_tex_2(sK5,sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) = u1_pre_topc(sK4) ),
    inference(prop_impl,[status(thm)],[c_32,c_483])).

cnf(c_1548,plain,
    ( v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v3_pre_topc(X0,sK4) ),
    inference(bin_hyper_res,[status(thm)],[c_540,c_1502])).

cnf(c_3625,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v3_pre_topc(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1548])).

cnf(c_3706,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | v3_pre_topc(X0,sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3625,c_30])).

cnf(c_4313,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | v3_pre_topc(k9_subset_1(sK5,X0,X1),sK4) = iProver_top
    | r1_tarski(X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3629,c_3706])).

cnf(c_7270,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | v3_pre_topc(k3_xboole_0(X0,sK5),sK4) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6679,c_4313])).

cnf(c_3996,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3999,plain,
    ( r1_tarski(sK5,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3996])).

cnf(c_20280,plain,
    ( v3_pre_topc(k3_xboole_0(X0,sK5),sK4) = iProver_top
    | v2_tex_2(sK5,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7270,c_3999])).

cnf(c_20281,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | v3_pre_topc(k3_xboole_0(X0,sK5),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_20280])).

cnf(c_20288,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | v3_pre_topc(k3_xboole_0(sK5,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_20281])).

cnf(c_4583,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3629,c_3631])).

cnf(c_39878,plain,
    ( k1_zfmisc_1(sK5) = u1_pre_topc(sK4)
    | r1_tarski(sK2(sK4,sK5,k3_xboole_0(sK5,X0)),sK5) != iProver_top
    | r1_tarski(k3_xboole_0(sK5,X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_39827,c_4583])).

cnf(c_34206,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_34162,c_3631])).

cnf(c_43532,plain,
    ( k1_zfmisc_1(sK5) = u1_pre_topc(sK4)
    | r1_tarski(sK2(sK4,sK5,k3_xboole_0(sK5,X0)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_41477,c_34206])).

cnf(c_49506,plain,
    ( k1_zfmisc_1(sK5) = u1_pre_topc(sK4)
    | r1_tarski(k3_xboole_0(sK5,X0),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39878,c_43532])).

cnf(c_90967,plain,
    ( m1_subset_1(k3_xboole_0(sK5,X0),k1_zfmisc_1(sK5))
    | ~ r1_tarski(k3_xboole_0(sK5,X0),sK5) ),
    inference(instantiation,[status(thm)],[c_5275])).

cnf(c_90968,plain,
    ( m1_subset_1(k3_xboole_0(sK5,X0),k1_zfmisc_1(sK5)) = iProver_top
    | r1_tarski(k3_xboole_0(sK5,X0),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_90967])).

cnf(c_180651,plain,
    ( v3_pre_topc(k3_xboole_0(sK5,X0),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_178704,c_3677,c_3644,c_20288,c_49506,c_90968])).

cnf(c_180704,plain,
    ( k1_zfmisc_1(sK5) = u1_pre_topc(sK4)
    | v3_pre_topc(sK0(k1_zfmisc_1(sK5),u1_pre_topc(sK4)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_103615,c_180651])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_668,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | r2_hidden(X0,u1_pre_topc(X1))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_32])).

cnf(c_669,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(X0,sK4)
    | r2_hidden(X0,u1_pre_topc(sK4)) ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_3617,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v3_pre_topc(X0,sK4) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_3720,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | v3_pre_topc(X0,sK4) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3617,c_30])).

cnf(c_6577,plain,
    ( v3_pre_topc(sK0(k1_zfmisc_1(sK5),X0),sK4) != iProver_top
    | r2_hidden(sK0(k1_zfmisc_1(sK5),X0),u1_pre_topc(sK4)) = iProver_top
    | r1_tarski(k1_zfmisc_1(sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4812,c_3720])).

cnf(c_7,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3637,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7176,plain,
    ( v3_pre_topc(sK0(k1_zfmisc_1(sK5),u1_pre_topc(sK4)),sK4) != iProver_top
    | r1_tarski(k1_zfmisc_1(sK5),u1_pre_topc(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6577,c_3637])).

cnf(c_182139,plain,
    ( k1_zfmisc_1(sK5) = u1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_180704,c_5483,c_7176])).

cnf(c_182483,plain,
    ( u1_pre_topc(sK4) != u1_pre_topc(sK4)
    | v2_tex_2(sK5,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_182139,c_3677])).

cnf(c_182486,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_182483])).

cnf(c_186322,plain,
    ( k3_xboole_0(sK1(sK4,sK5),sK5) = sK1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_6929,c_182486])).

cnf(c_186370,plain,
    ( k3_xboole_0(sK5,sK1(sK4,sK5)) = sK1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_186322,c_1])).

cnf(c_6680,plain,
    ( k9_subset_1(X0,X1,sK1(sK4,X0)) = k3_xboole_0(X1,sK1(sK4,X0))
    | v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3727,c_3628])).

cnf(c_7640,plain,
    ( k9_subset_1(sK5,X0,sK1(sK4,sK5)) = k3_xboole_0(X0,sK1(sK4,sK5))
    | v2_tex_2(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3644,c_6680])).

cnf(c_5049,plain,
    ( k9_subset_1(sK5,sK5,sK2(sK4,sK5,sK5)) = sK5
    | v2_tex_2(sK5,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3644,c_5039])).

cnf(c_7708,plain,
    ( k9_subset_1(sK5,X0,sK1(sK4,sK5)) = k3_xboole_0(X0,sK1(sK4,sK5))
    | k9_subset_1(sK5,sK5,sK2(sK4,sK5,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_7640,c_5049])).

cnf(c_12,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_647,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_32])).

cnf(c_648,plain,
    ( v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_pre_topc(X1,sK4)
    | k9_subset_1(u1_struct_0(sK4),X0,X1) != sK1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_3618,plain,
    ( k9_subset_1(u1_struct_0(sK4),X0,X1) != sK1(sK4,X0)
    | v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v3_pre_topc(X1,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_3752,plain,
    ( k9_subset_1(sK5,X0,X1) != sK1(sK4,X0)
    | v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK5)) != iProver_top
    | v3_pre_topc(X1,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3618,c_30])).

cnf(c_20604,plain,
    ( k9_subset_1(sK5,sK5,sK2(sK4,sK5,sK5)) = sK5
    | k3_xboole_0(X0,sK1(sK4,sK5)) != sK1(sK4,X0)
    | v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(sK1(sK4,sK5),k1_zfmisc_1(sK5)) != iProver_top
    | v3_pre_topc(sK1(sK4,sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7708,c_3752])).

cnf(c_4775,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | v3_pre_topc(X0,sK4) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3632,c_3706])).

cnf(c_6762,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK5)) != iProver_top
    | v3_pre_topc(sK1(sK4,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3727,c_4775])).

cnf(c_20887,plain,
    ( m1_subset_1(sK1(sK4,sK5),k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | v2_tex_2(X0,sK4) = iProver_top
    | k3_xboole_0(X0,sK1(sK4,sK5)) != sK1(sK4,X0)
    | k9_subset_1(sK5,sK5,sK2(sK4,sK5,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20604,c_3644,c_5049,c_6762])).

cnf(c_20888,plain,
    ( k9_subset_1(sK5,sK5,sK2(sK4,sK5,sK5)) = sK5
    | k3_xboole_0(X0,sK1(sK4,sK5)) != sK1(sK4,X0)
    | v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(sK1(sK4,sK5),k1_zfmisc_1(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_20887])).

cnf(c_182385,plain,
    ( k9_subset_1(sK5,sK5,sK2(sK4,sK5,sK5)) = sK5
    | k3_xboole_0(X0,sK1(sK4,sK5)) != sK1(sK4,X0)
    | v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,u1_pre_topc(sK4)) != iProver_top
    | m1_subset_1(sK1(sK4,sK5),u1_pre_topc(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_182139,c_20888])).

cnf(c_4146,plain,
    ( m1_subset_1(X0,u1_pre_topc(sK4))
    | ~ r2_hidden(X0,u1_pre_topc(sK4)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_59574,plain,
    ( m1_subset_1(sK1(sK4,sK5),u1_pre_topc(sK4))
    | ~ r2_hidden(sK1(sK4,sK5),u1_pre_topc(sK4)) ),
    inference(instantiation,[status(thm)],[c_4146])).

cnf(c_59575,plain,
    ( m1_subset_1(sK1(sK4,sK5),u1_pre_topc(sK4)) = iProver_top
    | r2_hidden(sK1(sK4,sK5),u1_pre_topc(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59574])).

cnf(c_34804,plain,
    ( v3_pre_topc(k3_xboole_0(sK5,X0),sK4) != iProver_top
    | r2_hidden(k3_xboole_0(sK5,X0),u1_pre_topc(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_34166,c_3720])).

cnf(c_35855,plain,
    ( v3_pre_topc(k3_xboole_0(sK5,X0),sK4) != iProver_top
    | r2_hidden(k3_xboole_0(X0,sK5),u1_pre_topc(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_34804])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_683,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_32])).

cnf(c_684,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v3_pre_topc(X0,sK4)
    | ~ r2_hidden(X0,u1_pre_topc(sK4)) ),
    inference(unflattening,[status(thm)],[c_683])).

cnf(c_3616,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v3_pre_topc(X0,sK4) = iProver_top
    | r2_hidden(X0,u1_pre_topc(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_684])).

cnf(c_3713,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5)) != iProver_top
    | v3_pre_topc(X0,sK4) = iProver_top
    | r2_hidden(X0,u1_pre_topc(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3616,c_30])).

cnf(c_37522,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK5),k1_zfmisc_1(sK5)) != iProver_top
    | v3_pre_topc(k3_xboole_0(X0,sK5),sK4) = iProver_top
    | v3_pre_topc(k3_xboole_0(sK5,X0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_35855,c_3713])).

cnf(c_38767,plain,
    ( v3_pre_topc(k3_xboole_0(X0,sK5),sK4) = iProver_top
    | v3_pre_topc(k3_xboole_0(sK5,X0),sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_37522,c_34162])).

cnf(c_180719,plain,
    ( v3_pre_topc(k3_xboole_0(X0,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_180651,c_38767])).

cnf(c_186371,plain,
    ( v3_pre_topc(sK1(sK4,sK5),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_186322,c_180719])).

cnf(c_34218,plain,
    ( v3_pre_topc(k3_xboole_0(X0,sK5),sK4) != iProver_top
    | r2_hidden(k3_xboole_0(X0,sK5),u1_pre_topc(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_34162,c_3720])).

cnf(c_186398,plain,
    ( v3_pre_topc(k3_xboole_0(sK1(sK4,sK5),sK5),sK4) != iProver_top
    | r2_hidden(sK1(sK4,sK5),u1_pre_topc(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_186322,c_34218])).

cnf(c_186431,plain,
    ( v3_pre_topc(sK1(sK4,sK5),sK4) != iProver_top
    | r2_hidden(sK1(sK4,sK5),u1_pre_topc(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_186398,c_186322])).

cnf(c_186495,plain,
    ( r2_hidden(sK1(sK4,sK5),u1_pre_topc(sK4)) = iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_186371,c_186431])).

cnf(c_186321,plain,
    ( k9_subset_1(sK5,X0,sK1(sK4,sK5)) = k3_xboole_0(X0,sK1(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_7640,c_182486])).

cnf(c_182476,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | m1_subset_1(X0,u1_pre_topc(sK4)) != iProver_top
    | v3_pre_topc(X0,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_182139,c_3706])).

cnf(c_182544,plain,
    ( m1_subset_1(X0,u1_pre_topc(sK4)) != iProver_top
    | v3_pre_topc(X0,sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_182476,c_182486])).

cnf(c_182479,plain,
    ( k9_subset_1(sK5,X0,X1) != sK1(sK4,X0)
    | v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,u1_pre_topc(sK4)) != iProver_top
    | m1_subset_1(X1,u1_pre_topc(sK4)) != iProver_top
    | v3_pre_topc(X1,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_182139,c_3752])).

cnf(c_182547,plain,
    ( k9_subset_1(sK5,X0,X1) != sK1(sK4,X0)
    | v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,u1_pre_topc(sK4)) != iProver_top
    | m1_subset_1(X1,u1_pre_topc(sK4)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_182544,c_182479])).

cnf(c_187671,plain,
    ( k3_xboole_0(X0,sK1(sK4,sK5)) != sK1(sK4,X0)
    | v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,u1_pre_topc(sK4)) != iProver_top
    | m1_subset_1(sK1(sK4,sK5),u1_pre_topc(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_186321,c_182547])).

cnf(c_196962,plain,
    ( m1_subset_1(X0,u1_pre_topc(sK4)) != iProver_top
    | v2_tex_2(X0,sK4) = iProver_top
    | k3_xboole_0(X0,sK1(sK4,sK5)) != sK1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_182385,c_59575,c_186495,c_187671])).

cnf(c_196963,plain,
    ( k3_xboole_0(X0,sK1(sK4,sK5)) != sK1(sK4,X0)
    | v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,u1_pre_topc(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_196962])).

cnf(c_196988,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | m1_subset_1(sK5,u1_pre_topc(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_186370,c_196963])).

cnf(c_12057,plain,
    ( k3_xboole_0(sK2(sK4,sK5,sK5),sK5) = sK2(sK4,sK5,sK5)
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_3638,c_11863])).

cnf(c_12628,plain,
    ( k3_xboole_0(sK5,sK2(sK4,sK5,sK5)) = sK2(sK4,sK5,sK5)
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_1,c_12057])).

cnf(c_13594,plain,
    ( k9_subset_1(sK5,X0,sK2(sK4,sK5,sK5)) = k3_xboole_0(X0,sK2(sK4,sK5,sK5))
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_3638,c_13288])).

cnf(c_5223,plain,
    ( k9_subset_1(sK5,sK5,sK2(sK4,sK5,sK5)) = sK5
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_3652,c_5049])).

cnf(c_13843,plain,
    ( k3_xboole_0(sK5,sK2(sK4,sK5,sK5)) = sK5
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_13594,c_5223])).

cnf(c_18429,plain,
    ( sK2(sK4,sK5,sK5) = sK5
    | k1_zfmisc_1(sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_12628,c_13843])).

cnf(c_19317,plain,
    ( k1_zfmisc_1(sK5) = u1_pre_topc(sK4)
    | v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK5)) != iProver_top
    | v3_pre_topc(sK5,sK4) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_18429,c_3741])).

cnf(c_4314,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | v3_pre_topc(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3644,c_3706])).

cnf(c_20075,plain,
    ( v3_pre_topc(sK5,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19317,c_3677,c_3644,c_3999,c_4314])).

cnf(c_3921,plain,
    ( v3_pre_topc(sK5,sK4) != iProver_top
    | r2_hidden(sK5,u1_pre_topc(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3644,c_3720])).

cnf(c_4624,plain,
    ( m1_subset_1(sK5,u1_pre_topc(sK4)) = iProver_top
    | v3_pre_topc(sK5,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3921,c_3634])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_196988,c_182139,c_20075,c_4624,c_3677])).


%------------------------------------------------------------------------------
