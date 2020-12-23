%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:10 EST 2020

% Result     : Theorem 19.71s
% Output     : CNFRefutation 19.71s
% Verified   : 
% Statistics : Number of formulae       :  273 (10129 expanded)
%              Number of clauses        :  188 (3051 expanded)
%              Number of leaves         :   26 (2162 expanded)
%              Depth                    :   33
%              Number of atoms          : 1113 (61680 expanded)
%              Number of equality atoms :  457 (5631 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK4(X0),X0)
        & ~ v1_zfmisc_1(sK4(X0))
        & ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ( ~ v1_subset_1(sK4(X0),X0)
        & ~ v1_zfmisc_1(sK4(X0))
        & ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f62])).

fof(f99,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK4(X0),X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f65,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( v1_subset_1(sK6,u1_struct_0(X0))
          | ~ v3_tex_2(sK6,X0) )
        & ( ~ v1_subset_1(sK6,u1_struct_0(X0))
          | v3_tex_2(sK6,X0) )
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK5))
            | ~ v3_tex_2(X1,sK5) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK5))
            | v3_tex_2(X1,sK5) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
      & l1_pre_topc(sK5)
      & v1_tdlat_3(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ( v1_subset_1(sK6,u1_struct_0(sK5))
      | ~ v3_tex_2(sK6,sK5) )
    & ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
      | v3_tex_2(sK6,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & l1_pre_topc(sK5)
    & v1_tdlat_3(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f65,f67,f66])).

fof(f109,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f68])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f58])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != X1
        & r1_tarski(X1,sK3(X0,X1))
        & v2_tex_2(sK3(X0,X1),X0)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK3(X0,X1) != X1
                & r1_tarski(X1,sK3(X0,X1))
                & v2_tex_2(sK3(X0,X1),X0)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f59,f60])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK3(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f105,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f106,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f107,plain,(
    v1_tdlat_3(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f108,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f49])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X2)
          | ~ r2_hidden(sK1(X0,X1,X2),X1) )
        & ( r2_hidden(sK1(X0,X1,X2),X2)
          | r2_hidden(sK1(X0,X1,X2),X1) )
        & m1_subset_1(sK1(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK1(X0,X1,X2),X2)
              | ~ r2_hidden(sK1(X0,X1,X2),X1) )
            & ( r2_hidden(sK1(X0,X1,X2),X2)
              | r2_hidden(sK1(X0,X1,X2),X1) )
            & m1_subset_1(sK1(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | m1_subset_1(sK1(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X2)
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK3(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f110,plain,
    ( ~ v1_subset_1(sK6,u1_struct_0(sK5))
    | v3_tex_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | r2_hidden(sK1(X0,X1,X2),X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f54])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f111,plain,
    ( v1_subset_1(sK6,u1_struct_0(sK5))
    | ~ v3_tex_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f91,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f112,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f91])).

cnf(c_33,plain,
    ( m1_subset_1(sK4(X0),k1_zfmisc_1(X0))
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1450,plain,
    ( m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) = iProver_top
    | v1_zfmisc_1(X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1465,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2847,plain,
    ( r1_tarski(sK4(X0),X0) = iProver_top
    | v1_zfmisc_1(X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1450,c_1465])).

cnf(c_22,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_282,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_366,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_22,c_282])).

cnf(c_1438,plain,
    ( X0 = X1
    | v1_subset_1(X1,X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_9033,plain,
    ( sK4(X0) = X0
    | v1_subset_1(sK4(X0),X0) = iProver_top
    | v1_zfmisc_1(X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2847,c_1438])).

cnf(c_30,plain,
    ( ~ v1_subset_1(sK4(X0),X0)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_65,plain,
    ( v1_subset_1(sK4(X0),X0) != iProver_top
    | v1_zfmisc_1(X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_72785,plain,
    ( sK4(X0) = X0
    | v1_zfmisc_1(X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9033,c_65])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1445,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_25,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | r1_tarski(X0,sK3(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1458,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v3_tex_2(X0,X1) = iProver_top
    | r1_tarski(X0,sK3(X1,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6261,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | v3_tex_2(sK6,sK5) = iProver_top
    | r1_tarski(sK6,sK3(sK5,sK6)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1458])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_43,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_44,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( v1_tdlat_3(sK5) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_45,plain,
    ( v1_tdlat_3(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_46,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_47,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_34,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2018,plain,
    ( v2_tex_2(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ v1_tdlat_3(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_2019,plain,
    ( v2_tex_2(sK6,sK5) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v1_tdlat_3(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2018])).

cnf(c_6733,plain,
    ( r1_tarski(sK6,sK3(sK5,sK6)) = iProver_top
    | v3_tex_2(sK6,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6261,c_43,c_44,c_45,c_46,c_47,c_2019])).

cnf(c_6734,plain,
    ( v3_tex_2(sK6,sK5) = iProver_top
    | r1_tarski(sK6,sK3(sK5,sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6733])).

cnf(c_1466,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1473,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5086,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1473])).

cnf(c_11707,plain,
    ( v3_tex_2(sK6,sK5) = iProver_top
    | r2_hidden(X0,sK3(sK5,sK6)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6734,c_5086])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X0,X2),X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_361,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(sK1(X1,X0,X2),X1)
    | X2 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_282])).

cnf(c_1440,plain,
    ( X0 = X1
    | r1_tarski(X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(sK1(X2,X1,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1475,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4583,plain,
    ( X0 = X1
    | r1_tarski(X0,X2) != iProver_top
    | r2_hidden(sK1(X2,X0,X1),X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_1475])).

cnf(c_11,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X2)
    | ~ r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | X2 = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1468,plain,
    ( X0 = X1
    | r2_hidden(sK1(X2,X1,X0),X0) != iProver_top
    | r2_hidden(sK1(X2,X1,X0),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_16840,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r2_hidden(sK1(X0,X1,X0),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4583,c_1468])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1463,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_38104,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16840,c_1463,c_1465])).

cnf(c_38110,plain,
    ( sK3(sK5,sK6) = X0
    | v3_tex_2(sK6,sK5) = iProver_top
    | r2_hidden(sK1(X0,sK3(sK5,sK6),X0),sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11707,c_38104])).

cnf(c_24,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2165,plain,
    ( ~ v2_tex_2(sK6,sK5)
    | v3_tex_2(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5)
    | sK3(sK5,sK6) != sK6 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2166,plain,
    ( sK3(sK5,sK6) != sK6
    | v2_tex_2(sK6,sK5) != iProver_top
    | v3_tex_2(sK6,sK5) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2165])).

cnf(c_482,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2201,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_2254,plain,
    ( r1_tarski(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1465])).

cnf(c_3601,plain,
    ( u1_struct_0(sK5) = sK6
    | v1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2254,c_1438])).

cnf(c_37,negated_conjecture,
    ( v3_tex_2(sK6,sK5)
    | ~ v1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1446,plain,
    ( v3_tex_2(sK6,sK5) = iProver_top
    | v1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4104,plain,
    ( u1_struct_0(sK5) = sK6
    | v3_tex_2(sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3601,c_1446])).

cnf(c_487,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3191,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_366,c_487])).

cnf(c_5820,plain,
    ( v3_tex_2(sK6,sK5)
    | ~ r1_tarski(sK6,u1_struct_0(sK5))
    | v1_xboole_0(u1_struct_0(sK5))
    | ~ v1_xboole_0(sK6) ),
    inference(resolution,[status(thm)],[c_3191,c_37])).

cnf(c_1884,plain,
    ( r1_tarski(sK6,u1_struct_0(sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_35,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1448,plain,
    ( v3_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5664,plain,
    ( v3_tex_2(sK6,sK5) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1448])).

cnf(c_5782,plain,
    ( ~ v3_tex_2(sK6,sK5)
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v1_xboole_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5664])).

cnf(c_6048,plain,
    ( v1_xboole_0(u1_struct_0(sK5))
    | ~ v1_xboole_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5820,c_42,c_41,c_39,c_38,c_1884,c_5782])).

cnf(c_6050,plain,
    ( v1_xboole_0(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6048])).

cnf(c_483,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2421,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK5)
    | u1_struct_0(sK5) != X1 ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_3904,plain,
    ( X0 = u1_struct_0(sK5)
    | X0 != sK6
    | u1_struct_0(sK5) != sK6 ),
    inference(instantiation,[status(thm)],[c_2421])).

cnf(c_7477,plain,
    ( u1_struct_0(sK5) != sK6
    | sK6 = u1_struct_0(sK5)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3904])).

cnf(c_5091,plain,
    ( r2_hidden(X0,u1_struct_0(sK5)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1473])).

cnf(c_12017,plain,
    ( sK3(sK5,sK6) = X0
    | v3_tex_2(sK6,sK5) = iProver_top
    | r2_hidden(sK1(X1,X0,sK3(sK5,sK6)),X0) != iProver_top
    | r2_hidden(sK1(X1,X0,sK3(sK5,sK6)),sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11707,c_1468])).

cnf(c_12228,plain,
    ( sK3(sK5,sK6) = u1_struct_0(sK5)
    | v3_tex_2(sK6,sK5) = iProver_top
    | r2_hidden(sK1(X0,u1_struct_0(sK5),sK3(sK5,sK6)),sK6) != iProver_top
    | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5091,c_12017])).

cnf(c_16856,plain,
    ( sK3(sK5,sK6) = u1_struct_0(sK5)
    | v3_tex_2(sK6,sK5) = iProver_top
    | r1_tarski(u1_struct_0(sK5),sK6) != iProver_top
    | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(sK6)) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK6)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4583,c_12228])).

cnf(c_27,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2162,plain,
    ( ~ v2_tex_2(sK6,sK5)
    | v3_tex_2(sK6,sK5)
    | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2172,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | v3_tex_2(sK6,sK5) = iProver_top
    | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2162])).

cnf(c_3241,plain,
    ( r1_tarski(sK3(sK5,sK6),u1_struct_0(sK5))
    | ~ m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3242,plain,
    ( r1_tarski(sK3(sK5,sK6),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3241])).

cnf(c_489,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_3583,plain,
    ( r1_tarski(sK3(sK5,sK6),X0)
    | ~ r1_tarski(sK3(sK5,sK6),u1_struct_0(sK5))
    | X0 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_489])).

cnf(c_12985,plain,
    ( ~ r1_tarski(sK3(sK5,sK6),u1_struct_0(sK5))
    | r1_tarski(sK3(sK5,sK6),sK6)
    | sK6 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3583])).

cnf(c_12993,plain,
    ( sK6 != u1_struct_0(sK5)
    | r1_tarski(sK3(sK5,sK6),u1_struct_0(sK5)) != iProver_top
    | r1_tarski(sK3(sK5,sK6),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12985])).

cnf(c_7693,plain,
    ( u1_struct_0(sK5) = X0
    | r2_hidden(sK1(X1,X0,u1_struct_0(sK5)),X0) != iProver_top
    | r2_hidden(sK1(X1,X0,u1_struct_0(sK5)),sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5091,c_1468])).

cnf(c_12018,plain,
    ( sK3(sK5,sK6) = u1_struct_0(sK5)
    | v3_tex_2(sK6,sK5) = iProver_top
    | r2_hidden(sK1(X0,sK3(sK5,sK6),u1_struct_0(sK5)),sK6) != iProver_top
    | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11707,c_7693])).

cnf(c_16855,plain,
    ( sK3(sK5,sK6) = u1_struct_0(sK5)
    | v3_tex_2(sK6,sK5) = iProver_top
    | r1_tarski(sK3(sK5,sK6),sK6) != iProver_top
    | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(sK6)) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK6)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4583,c_12018])).

cnf(c_19426,plain,
    ( v3_tex_2(sK6,sK5) = iProver_top
    | sK3(sK5,sK6) = u1_struct_0(sK5)
    | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(sK6)) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK6)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16856,c_43,c_44,c_45,c_46,c_47,c_2019,c_2172,c_2201,c_3242,c_4104,c_7477,c_12993,c_16855])).

cnf(c_19427,plain,
    ( sK3(sK5,sK6) = u1_struct_0(sK5)
    | v3_tex_2(sK6,sK5) = iProver_top
    | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(sK6)) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK6)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_19426])).

cnf(c_19436,plain,
    ( sK3(sK5,sK6) = u1_struct_0(sK5)
    | v3_tex_2(sK6,sK5) = iProver_top
    | r1_tarski(sK3(sK5,sK6),sK6) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK6)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_19427])).

cnf(c_29813,plain,
    ( v3_tex_2(sK6,sK5) = iProver_top
    | sK3(sK5,sK6) = u1_struct_0(sK5)
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK6)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19436,c_43,c_44,c_45,c_46,c_47,c_2019,c_2172,c_2201,c_3242,c_4104,c_7477,c_12993])).

cnf(c_29814,plain,
    ( sK3(sK5,sK6) = u1_struct_0(sK5)
    | v3_tex_2(sK6,sK5) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK6)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_29813])).

cnf(c_29822,plain,
    ( sK3(sK5,sK6) = u1_struct_0(sK5)
    | v3_tex_2(sK6,sK5) = iProver_top
    | r1_tarski(u1_struct_0(sK5),sK6) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_29814])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2041,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK5))
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_3151,plain,
    ( m1_subset_1(u1_struct_0(sK5),X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK5))
    | u1_struct_0(sK5) != sK6 ),
    inference(instantiation,[status(thm)],[c_2041])).

cnf(c_3525,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | u1_struct_0(sK5) != sK6
    | k1_zfmisc_1(u1_struct_0(sK5)) != k1_zfmisc_1(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3151])).

cnf(c_3527,plain,
    ( u1_struct_0(sK5) != sK6
    | k1_zfmisc_1(u1_struct_0(sK5)) != k1_zfmisc_1(u1_struct_0(sK5))
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3525])).

cnf(c_3526,plain,
    ( k1_zfmisc_1(u1_struct_0(sK5)) = k1_zfmisc_1(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_6410,plain,
    ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5))
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6411,plain,
    ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6410])).

cnf(c_8582,plain,
    ( r1_tarski(u1_struct_0(sK5),X0)
    | ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5))
    | X0 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_489])).

cnf(c_20547,plain,
    ( ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5))
    | r1_tarski(u1_struct_0(sK5),sK6)
    | sK6 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_8582])).

cnf(c_20548,plain,
    ( sK6 != u1_struct_0(sK5)
    | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top
    | r1_tarski(u1_struct_0(sK5),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20547])).

cnf(c_29838,plain,
    ( v3_tex_2(sK6,sK5) = iProver_top
    | sK3(sK5,sK6) = u1_struct_0(sK5)
    | v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29822,c_47,c_2201,c_3527,c_3526,c_4104,c_6411,c_7477,c_20548])).

cnf(c_29839,plain,
    ( sK3(sK5,sK6) = u1_struct_0(sK5)
    | v3_tex_2(sK6,sK5) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_29838])).

cnf(c_12,plain,
    ( r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | X2 = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1467,plain,
    ( X0 = X1
    | r2_hidden(sK1(X2,X1,X0),X0) = iProver_top
    | r2_hidden(sK1(X2,X1,X0),X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1456,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v3_tex_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7257,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v3_tex_2(X0,X1) = iProver_top
    | r2_hidden(X2,sK3(X1,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_1463])).

cnf(c_16242,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | v3_tex_2(sK6,sK5) = iProver_top
    | r2_hidden(X0,sK3(sK5,sK6)) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_7257])).

cnf(c_1885,plain,
    ( r1_tarski(sK6,u1_struct_0(sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1884])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_362,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_282])).

cnf(c_2135,plain,
    ( ~ r1_tarski(sK6,u1_struct_0(sK5))
    | ~ v1_xboole_0(u1_struct_0(sK5))
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_2137,plain,
    ( r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2135])).

cnf(c_6479,plain,
    ( v3_tex_2(sK6,sK5) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5664,c_43,c_44,c_46,c_47,c_2356])).

cnf(c_16378,plain,
    ( r2_hidden(X0,sK3(sK5,sK6)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16242,c_43,c_44,c_45,c_46,c_47,c_1885,c_2019,c_2137,c_6479])).

cnf(c_16386,plain,
    ( sK3(sK5,sK6) = X0
    | r2_hidden(sK1(X1,X0,sK3(sK5,sK6)),X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_16378])).

cnf(c_20,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1461,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16239,plain,
    ( v2_tex_2(sK2(X0),X0) != iProver_top
    | v3_tex_2(sK2(X0),X0) = iProver_top
    | r2_hidden(X1,sK3(X0,sK2(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1461,c_7257])).

cnf(c_36694,plain,
    ( sK3(X0,sK2(X0)) = sK3(sK5,sK6)
    | v2_tex_2(sK2(X0),X0) != iProver_top
    | v3_tex_2(sK2(X0),X0) = iProver_top
    | m1_subset_1(sK3(X0,sK2(X0)),k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16386,c_16239])).

cnf(c_2190,plain,
    ( r2_hidden(sK1(X0,sK6,X1),X1)
    | r2_hidden(sK1(X0,sK6,X1),sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | X1 = sK6 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2557,plain,
    ( r2_hidden(sK1(u1_struct_0(sK5),sK6,X0),X0)
    | r2_hidden(sK1(u1_struct_0(sK5),sK6,X0),sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | X0 = sK6 ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_3248,plain,
    ( r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK3(sK5,sK6))
    | r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK6)
    | ~ m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | sK3(sK5,sK6) = sK6 ),
    inference(instantiation,[status(thm)],[c_2557])).

cnf(c_3249,plain,
    ( sK3(sK5,sK6) = sK6
    | r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK3(sK5,sK6)) = iProver_top
    | r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK6) = iProver_top
    | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3248])).

cnf(c_3458,plain,
    ( ~ r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK3(sK5,sK6))
    | ~ m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_14437,plain,
    ( ~ r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK3(sK5,sK6))
    | ~ m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3458])).

cnf(c_14438,plain,
    ( r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK3(sK5,sK6)) != iProver_top
    | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14437])).

cnf(c_6697,plain,
    ( ~ r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_37314,plain,
    ( ~ r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_6697])).

cnf(c_37315,plain,
    ( r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK6) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37314])).

cnf(c_37333,plain,
    ( v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36694,c_43,c_44,c_45,c_46,c_47,c_1885,c_2019,c_2137,c_2166,c_2172,c_3249,c_6479,c_14438,c_37315])).

cnf(c_2183,plain,
    ( X0 != X1
    | X0 = sK6
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_12996,plain,
    ( X0 != u1_struct_0(sK5)
    | X0 = sK6
    | sK6 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2183])).

cnf(c_38011,plain,
    ( sK3(sK5,sK6) != u1_struct_0(sK5)
    | sK3(sK5,sK6) = sK6
    | sK6 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_12996])).

cnf(c_38745,plain,
    ( v3_tex_2(sK6,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38110,c_43,c_44,c_45,c_46,c_47,c_1885,c_2019,c_2137,c_2166,c_2172,c_2201,c_3249,c_4104,c_6050,c_6479,c_7477,c_14438,c_29839,c_37315,c_38011])).

cnf(c_36,negated_conjecture,
    ( ~ v3_tex_2(sK6,sK5)
    | v1_subset_1(sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1447,plain,
    ( v3_tex_2(sK6,sK5) != iProver_top
    | v1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_21,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_365,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_21,c_282])).

cnf(c_434,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1)
    | ~ r1_tarski(X0,X1)
    | ~ v1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_21,c_15,c_362])).

cnf(c_435,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_434])).

cnf(c_1437,plain,
    ( v1_subset_1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_zfmisc_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_2587,plain,
    ( v3_tex_2(sK6,sK5) != iProver_top
    | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1447,c_1437])).

cnf(c_2352,plain,
    ( ~ v3_tex_2(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_2356,plain,
    ( v3_tex_2(sK6,sK5) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2352])).

cnf(c_3050,plain,
    ( v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
    | v3_tex_2(sK6,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2587,c_43,c_44,c_46,c_47,c_1885,c_2356])).

cnf(c_3051,plain,
    ( v3_tex_2(sK6,sK5) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3050])).

cnf(c_38752,plain,
    ( v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_38745,c_3051])).

cnf(c_72795,plain,
    ( sK4(u1_struct_0(sK5)) = u1_struct_0(sK5)
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_72785,c_38752])).

cnf(c_73540,plain,
    ( sK4(u1_struct_0(sK5)) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_72795,c_43,c_44,c_45,c_46,c_47,c_1885,c_2019,c_2137,c_2166,c_2172,c_3249,c_6479,c_14438,c_37315])).

cnf(c_28,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1455,plain,
    ( X0 = X1
    | v2_tex_2(X0,X2) != iProver_top
    | v3_tex_2(X1,X2) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7873,plain,
    ( X0 = X1
    | v2_tex_2(X1,X2) != iProver_top
    | v3_tex_2(X0,X2) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,u1_struct_0(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_1455])).

cnf(c_50049,plain,
    ( sK6 = X0
    | v2_tex_2(X0,sK5) != iProver_top
    | v3_tex_2(sK6,sK5) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_7873])).

cnf(c_50467,plain,
    ( r1_tarski(sK6,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
    | sK6 = X0
    | v2_tex_2(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_50049,c_43,c_44,c_45,c_46,c_47,c_1885,c_2019,c_2137,c_2166,c_2172,c_2201,c_3249,c_4104,c_6050,c_6479,c_7477,c_14438,c_29839,c_37315,c_38011])).

cnf(c_50468,plain,
    ( sK6 = X0
    | v2_tex_2(X0,sK5) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_50467])).

cnf(c_50480,plain,
    ( sK4(u1_struct_0(sK5)) = sK6
    | v2_tex_2(sK4(u1_struct_0(sK5)),sK5) != iProver_top
    | r1_tarski(sK6,sK4(u1_struct_0(sK5))) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2847,c_50468])).

cnf(c_6791,plain,
    ( v2_tex_2(sK4(u1_struct_0(X0)),X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_tdlat_3(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_34,c_33])).

cnf(c_6792,plain,
    ( v2_tex_2(sK4(u1_struct_0(X0)),X0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6791])).

cnf(c_6794,plain,
    ( v2_tex_2(sK4(u1_struct_0(sK5)),sK5) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_pre_topc(sK5) != iProver_top
    | v1_tdlat_3(sK5) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6792])).

cnf(c_29847,plain,
    ( sK3(sK5,sK6) = u1_struct_0(sK5)
    | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_29839,c_3051])).

cnf(c_6739,plain,
    ( sK3(sK5,sK6) = sK6
    | v3_tex_2(sK6,sK5) = iProver_top
    | v1_subset_1(sK6,sK3(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6734,c_1438])).

cnf(c_6971,plain,
    ( v3_tex_2(sK6,sK5) = iProver_top
    | v1_subset_1(sK6,sK3(sK5,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6739,c_43,c_44,c_45,c_46,c_47,c_2019,c_2166])).

cnf(c_6977,plain,
    ( v3_tex_2(sK6,sK5) = iProver_top
    | r1_tarski(sK6,sK3(sK5,sK6)) != iProver_top
    | v1_zfmisc_1(sK3(sK5,sK6)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_6971,c_1437])).

cnf(c_2164,plain,
    ( ~ v2_tex_2(sK6,sK5)
    | v3_tex_2(sK6,sK5)
    | r1_tarski(sK6,sK3(sK5,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2168,plain,
    ( v2_tex_2(sK6,sK5) != iProver_top
    | v3_tex_2(sK6,sK5) = iProver_top
    | r1_tarski(sK6,sK3(sK5,sK6)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2164])).

cnf(c_6980,plain,
    ( v3_tex_2(sK6,sK5) = iProver_top
    | v1_zfmisc_1(sK3(sK5,sK6)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6977,c_43,c_44,c_45,c_46,c_47,c_2019,c_2168])).

cnf(c_493,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_8440,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_zfmisc_1(sK3(sK5,sK6))
    | sK3(sK5,sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_20504,plain,
    ( v1_zfmisc_1(sK3(sK5,sK6))
    | ~ v1_zfmisc_1(u1_struct_0(sK5))
    | sK3(sK5,sK6) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_8440])).

cnf(c_20505,plain,
    ( sK3(sK5,sK6) != u1_struct_0(sK5)
    | v1_zfmisc_1(sK3(sK5,sK6)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20504])).

cnf(c_31085,plain,
    ( v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29847,c_43,c_44,c_46,c_47,c_1885,c_2356,c_2587,c_6980,c_20505])).

cnf(c_50985,plain,
    ( sK4(u1_struct_0(sK5)) = sK6
    | r1_tarski(sK6,sK4(u1_struct_0(sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_50480,c_43,c_44,c_45,c_46,c_47,c_1885,c_2019,c_2137,c_2166,c_2172,c_3249,c_6050,c_6479,c_6794,c_14438,c_31085,c_37315])).

cnf(c_73544,plain,
    ( u1_struct_0(sK5) = sK6
    | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_73540,c_50985])).

cnf(c_73818,plain,
    ( u1_struct_0(sK5) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_73544,c_47,c_1885])).

cnf(c_73966,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_73818,c_1445])).

cnf(c_23,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1460,plain,
    ( v1_subset_1(X0,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_75958,plain,
    ( v1_subset_1(sK6,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_73966,c_1460])).

cnf(c_73965,plain,
    ( v3_tex_2(sK6,sK5) != iProver_top
    | v1_subset_1(sK6,sK6) = iProver_top ),
    inference(demodulation,[status(thm)],[c_73818,c_1447])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_75958,c_73965,c_38745])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:55:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.71/2.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.71/2.98  
% 19.71/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.71/2.98  
% 19.71/2.98  ------  iProver source info
% 19.71/2.98  
% 19.71/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.71/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.71/2.98  git: non_committed_changes: false
% 19.71/2.98  git: last_make_outside_of_git: false
% 19.71/2.98  
% 19.71/2.98  ------ 
% 19.71/2.98  ------ Parsing...
% 19.71/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.71/2.98  
% 19.71/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.71/2.98  
% 19.71/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.71/2.98  
% 19.71/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.71/2.98  ------ Proving...
% 19.71/2.98  ------ Problem Properties 
% 19.71/2.98  
% 19.71/2.98  
% 19.71/2.98  clauses                                 43
% 19.71/2.98  conjectures                             7
% 19.71/2.98  EPR                                     11
% 19.71/2.98  Horn                                    29
% 19.71/2.98  unary                                   10
% 19.71/2.98  binary                                  7
% 19.71/2.98  lits                                    127
% 19.71/2.98  lits eq                                 8
% 19.71/2.98  fd_pure                                 0
% 19.71/2.98  fd_pseudo                               0
% 19.71/2.98  fd_cond                                 1
% 19.71/2.98  fd_pseudo_cond                          5
% 19.71/2.98  AC symbols                              0
% 19.71/2.98  
% 19.71/2.98  ------ Input Options Time Limit: Unbounded
% 19.71/2.98  
% 19.71/2.98  
% 19.71/2.98  ------ 
% 19.71/2.98  Current options:
% 19.71/2.98  ------ 
% 19.71/2.98  
% 19.71/2.98  
% 19.71/2.98  
% 19.71/2.98  
% 19.71/2.98  ------ Proving...
% 19.71/2.98  
% 19.71/2.98  
% 19.71/2.98  % SZS status Theorem for theBenchmark.p
% 19.71/2.98  
% 19.71/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.71/2.98  
% 19.71/2.98  fof(f17,axiom,(
% 19.71/2.98    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ? [X1] : (~v1_subset_1(X1,X0) & ~v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 19.71/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.71/2.98  
% 19.71/2.98  fof(f38,plain,(
% 19.71/2.98    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & ~v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 19.71/2.98    inference(ennf_transformation,[],[f17])).
% 19.71/2.98  
% 19.71/2.98  fof(f39,plain,(
% 19.71/2.98    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & ~v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 19.71/2.98    inference(flattening,[],[f38])).
% 19.71/2.98  
% 19.71/2.98  fof(f62,plain,(
% 19.71/2.98    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & ~v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK4(X0),X0) & ~v1_zfmisc_1(sK4(X0)) & ~v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0))))),
% 19.71/2.98    introduced(choice_axiom,[])).
% 19.71/2.98  
% 19.71/2.98  fof(f63,plain,(
% 19.71/2.98    ! [X0] : ((~v1_subset_1(sK4(X0),X0) & ~v1_zfmisc_1(sK4(X0)) & ~v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0))) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 19.71/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f62])).
% 19.71/2.98  
% 19.71/2.98  fof(f99,plain,(
% 19.71/2.98    ( ! [X0] : (m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 19.71/2.98    inference(cnf_transformation,[],[f63])).
% 19.71/2.98  
% 19.71/2.98  fof(f10,axiom,(
% 19.71/2.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.71/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.71/2.98  
% 19.71/2.98  fof(f53,plain,(
% 19.71/2.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.71/2.98    inference(nnf_transformation,[],[f10])).
% 19.71/2.98  
% 19.71/2.98  fof(f84,plain,(
% 19.71/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.71/2.98    inference(cnf_transformation,[],[f53])).
% 19.71/2.98  
% 19.71/2.98  fof(f15,axiom,(
% 19.71/2.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 19.71/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.71/2.98  
% 19.71/2.98  fof(f35,plain,(
% 19.71/2.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.71/2.98    inference(ennf_transformation,[],[f15])).
% 19.71/2.98  
% 19.71/2.98  fof(f56,plain,(
% 19.71/2.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.71/2.98    inference(nnf_transformation,[],[f35])).
% 19.71/2.98  
% 19.71/2.98  fof(f92,plain,(
% 19.71/2.98    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.71/2.98    inference(cnf_transformation,[],[f56])).
% 19.71/2.98  
% 19.71/2.98  fof(f85,plain,(
% 19.71/2.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.71/2.98    inference(cnf_transformation,[],[f53])).
% 19.71/2.98  
% 19.71/2.98  fof(f102,plain,(
% 19.71/2.98    ( ! [X0] : (~v1_subset_1(sK4(X0),X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 19.71/2.98    inference(cnf_transformation,[],[f63])).
% 19.71/2.98  
% 19.71/2.98  fof(f20,conjecture,(
% 19.71/2.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 19.71/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.71/2.98  
% 19.71/2.98  fof(f21,negated_conjecture,(
% 19.71/2.98    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 19.71/2.98    inference(negated_conjecture,[],[f20])).
% 19.71/2.98  
% 19.71/2.98  fof(f44,plain,(
% 19.71/2.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 19.71/2.98    inference(ennf_transformation,[],[f21])).
% 19.71/2.98  
% 19.71/2.98  fof(f45,plain,(
% 19.71/2.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.71/2.98    inference(flattening,[],[f44])).
% 19.71/2.98  
% 19.71/2.98  fof(f64,plain,(
% 19.71/2.98    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.71/2.98    inference(nnf_transformation,[],[f45])).
% 19.71/2.98  
% 19.71/2.98  fof(f65,plain,(
% 19.71/2.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.71/2.98    inference(flattening,[],[f64])).
% 19.71/2.98  
% 19.71/2.98  fof(f67,plain,(
% 19.71/2.98    ( ! [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_subset_1(sK6,u1_struct_0(X0)) | ~v3_tex_2(sK6,X0)) & (~v1_subset_1(sK6,u1_struct_0(X0)) | v3_tex_2(sK6,X0)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.71/2.98    introduced(choice_axiom,[])).
% 19.71/2.98  
% 19.71/2.98  fof(f66,plain,(
% 19.71/2.98    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK5)) | ~v3_tex_2(X1,sK5)) & (~v1_subset_1(X1,u1_struct_0(sK5)) | v3_tex_2(X1,sK5)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5) & v1_tdlat_3(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 19.71/2.98    introduced(choice_axiom,[])).
% 19.71/2.98  
% 19.71/2.98  fof(f68,plain,(
% 19.71/2.98    ((v1_subset_1(sK6,u1_struct_0(sK5)) | ~v3_tex_2(sK6,sK5)) & (~v1_subset_1(sK6,u1_struct_0(sK5)) | v3_tex_2(sK6,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_pre_topc(sK5) & v1_tdlat_3(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 19.71/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f65,f67,f66])).
% 19.71/2.98  
% 19.71/2.98  fof(f109,plain,(
% 19.71/2.98    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))),
% 19.71/2.98    inference(cnf_transformation,[],[f68])).
% 19.71/2.98  
% 19.71/2.98  fof(f16,axiom,(
% 19.71/2.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 19.71/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.71/2.98  
% 19.71/2.98  fof(f36,plain,(
% 19.71/2.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.71/2.98    inference(ennf_transformation,[],[f16])).
% 19.71/2.98  
% 19.71/2.98  fof(f37,plain,(
% 19.71/2.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.71/2.98    inference(flattening,[],[f36])).
% 19.71/2.98  
% 19.71/2.98  fof(f57,plain,(
% 19.71/2.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.71/2.98    inference(nnf_transformation,[],[f37])).
% 19.71/2.98  
% 19.71/2.98  fof(f58,plain,(
% 19.71/2.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.71/2.98    inference(flattening,[],[f57])).
% 19.71/2.98  
% 19.71/2.98  fof(f59,plain,(
% 19.71/2.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.71/2.98    inference(rectify,[],[f58])).
% 19.71/2.98  
% 19.71/2.98  fof(f60,plain,(
% 19.71/2.98    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != X1 & r1_tarski(X1,sK3(X0,X1)) & v2_tex_2(sK3(X0,X1),X0) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.71/2.98    introduced(choice_axiom,[])).
% 19.71/2.98  
% 19.71/2.98  fof(f61,plain,(
% 19.71/2.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK3(X0,X1) != X1 & r1_tarski(X1,sK3(X0,X1)) & v2_tex_2(sK3(X0,X1),X0) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.71/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f59,f60])).
% 19.71/2.98  
% 19.71/2.98  fof(f97,plain,(
% 19.71/2.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK3(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.71/2.98    inference(cnf_transformation,[],[f61])).
% 19.71/2.98  
% 19.71/2.98  fof(f105,plain,(
% 19.71/2.98    ~v2_struct_0(sK5)),
% 19.71/2.98    inference(cnf_transformation,[],[f68])).
% 19.71/2.98  
% 19.71/2.98  fof(f106,plain,(
% 19.71/2.98    v2_pre_topc(sK5)),
% 19.71/2.98    inference(cnf_transformation,[],[f68])).
% 19.71/2.98  
% 19.71/2.98  fof(f107,plain,(
% 19.71/2.98    v1_tdlat_3(sK5)),
% 19.71/2.98    inference(cnf_transformation,[],[f68])).
% 19.71/2.98  
% 19.71/2.98  fof(f108,plain,(
% 19.71/2.98    l1_pre_topc(sK5)),
% 19.71/2.98    inference(cnf_transformation,[],[f68])).
% 19.71/2.98  
% 19.71/2.98  fof(f18,axiom,(
% 19.71/2.98    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 19.71/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.71/2.98  
% 19.71/2.98  fof(f40,plain,(
% 19.71/2.98    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.71/2.98    inference(ennf_transformation,[],[f18])).
% 19.71/2.98  
% 19.71/2.98  fof(f41,plain,(
% 19.71/2.98    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.71/2.98    inference(flattening,[],[f40])).
% 19.71/2.98  
% 19.71/2.98  fof(f103,plain,(
% 19.71/2.98    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.71/2.98    inference(cnf_transformation,[],[f41])).
% 19.71/2.98  
% 19.71/2.98  fof(f4,axiom,(
% 19.71/2.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 19.71/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.71/2.98  
% 19.71/2.98  fof(f23,plain,(
% 19.71/2.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.71/2.98    inference(ennf_transformation,[],[f4])).
% 19.71/2.98  
% 19.71/2.98  fof(f75,plain,(
% 19.71/2.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.71/2.98    inference(cnf_transformation,[],[f23])).
% 19.71/2.98  
% 19.71/2.98  fof(f8,axiom,(
% 19.71/2.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 19.71/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.71/2.98  
% 19.71/2.98  fof(f26,plain,(
% 19.71/2.98    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.71/2.98    inference(ennf_transformation,[],[f8])).
% 19.71/2.98  
% 19.71/2.98  fof(f27,plain,(
% 19.71/2.98    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.71/2.98    inference(flattening,[],[f26])).
% 19.71/2.98  
% 19.71/2.98  fof(f49,plain,(
% 19.71/2.98    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.71/2.98    inference(nnf_transformation,[],[f27])).
% 19.71/2.98  
% 19.71/2.98  fof(f50,plain,(
% 19.71/2.98    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.71/2.98    inference(flattening,[],[f49])).
% 19.71/2.98  
% 19.71/2.98  fof(f51,plain,(
% 19.71/2.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(sK1(X0,X1,X2),X1)) & (r2_hidden(sK1(X0,X1,X2),X2) | r2_hidden(sK1(X0,X1,X2),X1)) & m1_subset_1(sK1(X0,X1,X2),X0)))),
% 19.71/2.98    introduced(choice_axiom,[])).
% 19.71/2.98  
% 19.71/2.98  fof(f52,plain,(
% 19.71/2.98    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(sK1(X0,X1,X2),X1)) & (r2_hidden(sK1(X0,X1,X2),X2) | r2_hidden(sK1(X0,X1,X2),X1)) & m1_subset_1(sK1(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.71/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).
% 19.71/2.98  
% 19.71/2.98  fof(f80,plain,(
% 19.71/2.98    ( ! [X2,X0,X1] : (X1 = X2 | m1_subset_1(sK1(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.71/2.98    inference(cnf_transformation,[],[f52])).
% 19.71/2.98  
% 19.71/2.98  fof(f2,axiom,(
% 19.71/2.98    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 19.71/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.71/2.98  
% 19.71/2.98  fof(f22,plain,(
% 19.71/2.98    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 19.71/2.98    inference(ennf_transformation,[],[f2])).
% 19.71/2.98  
% 19.71/2.98  fof(f46,plain,(
% 19.71/2.98    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 19.71/2.98    inference(nnf_transformation,[],[f22])).
% 19.71/2.98  
% 19.71/2.98  fof(f70,plain,(
% 19.71/2.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 19.71/2.98    inference(cnf_transformation,[],[f46])).
% 19.71/2.98  
% 19.71/2.98  fof(f82,plain,(
% 19.71/2.98    ( ! [X2,X0,X1] : (X1 = X2 | ~r2_hidden(sK1(X0,X1,X2),X2) | ~r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.71/2.98    inference(cnf_transformation,[],[f52])).
% 19.71/2.98  
% 19.71/2.98  fof(f12,axiom,(
% 19.71/2.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 19.71/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.71/2.98  
% 19.71/2.98  fof(f31,plain,(
% 19.71/2.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 19.71/2.98    inference(ennf_transformation,[],[f12])).
% 19.71/2.98  
% 19.71/2.98  fof(f87,plain,(
% 19.71/2.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 19.71/2.98    inference(cnf_transformation,[],[f31])).
% 19.71/2.98  
% 19.71/2.98  fof(f98,plain,(
% 19.71/2.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK3(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.71/2.98    inference(cnf_transformation,[],[f61])).
% 19.71/2.98  
% 19.71/2.98  fof(f110,plain,(
% 19.71/2.98    ~v1_subset_1(sK6,u1_struct_0(sK5)) | v3_tex_2(sK6,sK5)),
% 19.71/2.98    inference(cnf_transformation,[],[f68])).
% 19.71/2.98  
% 19.71/2.98  fof(f19,axiom,(
% 19.71/2.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 19.71/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.71/2.98  
% 19.71/2.98  fof(f42,plain,(
% 19.71/2.98    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.71/2.98    inference(ennf_transformation,[],[f19])).
% 19.71/2.98  
% 19.71/2.98  fof(f43,plain,(
% 19.71/2.98    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.71/2.98    inference(flattening,[],[f42])).
% 19.71/2.98  
% 19.71/2.98  fof(f104,plain,(
% 19.71/2.98    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.71/2.98    inference(cnf_transformation,[],[f43])).
% 19.71/2.98  
% 19.71/2.98  fof(f95,plain,(
% 19.71/2.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.71/2.98    inference(cnf_transformation,[],[f61])).
% 19.71/2.98  
% 19.71/2.98  fof(f81,plain,(
% 19.71/2.98    ( ! [X2,X0,X1] : (X1 = X2 | r2_hidden(sK1(X0,X1,X2),X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.71/2.98    inference(cnf_transformation,[],[f52])).
% 19.71/2.98  
% 19.71/2.98  fof(f9,axiom,(
% 19.71/2.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 19.71/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.71/2.98  
% 19.71/2.98  fof(f28,plain,(
% 19.71/2.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 19.71/2.98    inference(ennf_transformation,[],[f9])).
% 19.71/2.98  
% 19.71/2.98  fof(f83,plain,(
% 19.71/2.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 19.71/2.98    inference(cnf_transformation,[],[f28])).
% 19.71/2.98  
% 19.71/2.98  fof(f13,axiom,(
% 19.71/2.98    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.71/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.71/2.98  
% 19.71/2.98  fof(f32,plain,(
% 19.71/2.98    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.71/2.98    inference(ennf_transformation,[],[f13])).
% 19.71/2.98  
% 19.71/2.98  fof(f54,plain,(
% 19.71/2.98    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.71/2.98    introduced(choice_axiom,[])).
% 19.71/2.98  
% 19.71/2.98  fof(f55,plain,(
% 19.71/2.98    ! [X0] : ((v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.71/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f54])).
% 19.71/2.98  
% 19.71/2.98  fof(f88,plain,(
% 19.71/2.98    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.71/2.98    inference(cnf_transformation,[],[f55])).
% 19.71/2.98  
% 19.71/2.98  fof(f111,plain,(
% 19.71/2.98    v1_subset_1(sK6,u1_struct_0(sK5)) | ~v3_tex_2(sK6,sK5)),
% 19.71/2.98    inference(cnf_transformation,[],[f68])).
% 19.71/2.98  
% 19.71/2.98  fof(f14,axiom,(
% 19.71/2.98    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 19.71/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.71/2.98  
% 19.71/2.98  fof(f33,plain,(
% 19.71/2.98    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 19.71/2.98    inference(ennf_transformation,[],[f14])).
% 19.71/2.98  
% 19.71/2.98  fof(f34,plain,(
% 19.71/2.98    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 19.71/2.98    inference(flattening,[],[f33])).
% 19.71/2.98  
% 19.71/2.98  fof(f90,plain,(
% 19.71/2.98    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 19.71/2.98    inference(cnf_transformation,[],[f34])).
% 19.71/2.98  
% 19.71/2.98  fof(f94,plain,(
% 19.71/2.98    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.71/2.98    inference(cnf_transformation,[],[f61])).
% 19.71/2.98  
% 19.71/2.98  fof(f91,plain,(
% 19.71/2.98    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.71/2.98    inference(cnf_transformation,[],[f56])).
% 19.71/2.98  
% 19.71/2.98  fof(f112,plain,(
% 19.71/2.98    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 19.71/2.98    inference(equality_resolution,[],[f91])).
% 19.71/2.98  
% 19.71/2.98  cnf(c_33,plain,
% 19.71/2.98      ( m1_subset_1(sK4(X0),k1_zfmisc_1(X0))
% 19.71/2.98      | v1_zfmisc_1(X0)
% 19.71/2.98      | v1_xboole_0(X0) ),
% 19.71/2.98      inference(cnf_transformation,[],[f99]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1450,plain,
% 19.71/2.98      ( m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) = iProver_top
% 19.71/2.98      | v1_zfmisc_1(X0) = iProver_top
% 19.71/2.98      | v1_xboole_0(X0) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_16,plain,
% 19.71/2.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.71/2.98      inference(cnf_transformation,[],[f84]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1465,plain,
% 19.71/2.98      ( r1_tarski(X0,X1) = iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2847,plain,
% 19.71/2.98      ( r1_tarski(sK4(X0),X0) = iProver_top
% 19.71/2.98      | v1_zfmisc_1(X0) = iProver_top
% 19.71/2.98      | v1_xboole_0(X0) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1450,c_1465]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_22,plain,
% 19.71/2.98      ( v1_subset_1(X0,X1)
% 19.71/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.71/2.98      | X1 = X0 ),
% 19.71/2.98      inference(cnf_transformation,[],[f92]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_15,plain,
% 19.71/2.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.71/2.98      inference(cnf_transformation,[],[f85]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_282,plain,
% 19.71/2.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.71/2.98      inference(prop_impl,[status(thm)],[c_15]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_366,plain,
% 19.71/2.98      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X1 = X0 ),
% 19.71/2.98      inference(bin_hyper_res,[status(thm)],[c_22,c_282]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1438,plain,
% 19.71/2.98      ( X0 = X1
% 19.71/2.98      | v1_subset_1(X1,X0) = iProver_top
% 19.71/2.98      | r1_tarski(X1,X0) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_9033,plain,
% 19.71/2.98      ( sK4(X0) = X0
% 19.71/2.98      | v1_subset_1(sK4(X0),X0) = iProver_top
% 19.71/2.98      | v1_zfmisc_1(X0) = iProver_top
% 19.71/2.98      | v1_xboole_0(X0) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_2847,c_1438]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_30,plain,
% 19.71/2.98      ( ~ v1_subset_1(sK4(X0),X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 19.71/2.98      inference(cnf_transformation,[],[f102]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_65,plain,
% 19.71/2.98      ( v1_subset_1(sK4(X0),X0) != iProver_top
% 19.71/2.98      | v1_zfmisc_1(X0) = iProver_top
% 19.71/2.98      | v1_xboole_0(X0) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_72785,plain,
% 19.71/2.98      ( sK4(X0) = X0
% 19.71/2.98      | v1_zfmisc_1(X0) = iProver_top
% 19.71/2.98      | v1_xboole_0(X0) = iProver_top ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_9033,c_65]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_38,negated_conjecture,
% 19.71/2.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 19.71/2.98      inference(cnf_transformation,[],[f109]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1445,plain,
% 19.71/2.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_25,plain,
% 19.71/2.98      ( ~ v2_tex_2(X0,X1)
% 19.71/2.98      | v3_tex_2(X0,X1)
% 19.71/2.98      | r1_tarski(X0,sK3(X1,X0))
% 19.71/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.71/2.98      | ~ l1_pre_topc(X1) ),
% 19.71/2.98      inference(cnf_transformation,[],[f97]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1458,plain,
% 19.71/2.98      ( v2_tex_2(X0,X1) != iProver_top
% 19.71/2.98      | v3_tex_2(X0,X1) = iProver_top
% 19.71/2.98      | r1_tarski(X0,sK3(X1,X0)) = iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 19.71/2.98      | l1_pre_topc(X1) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6261,plain,
% 19.71/2.98      ( v2_tex_2(sK6,sK5) != iProver_top
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | r1_tarski(sK6,sK3(sK5,sK6)) = iProver_top
% 19.71/2.98      | l1_pre_topc(sK5) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1445,c_1458]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_42,negated_conjecture,
% 19.71/2.98      ( ~ v2_struct_0(sK5) ),
% 19.71/2.98      inference(cnf_transformation,[],[f105]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_43,plain,
% 19.71/2.98      ( v2_struct_0(sK5) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_41,negated_conjecture,
% 19.71/2.98      ( v2_pre_topc(sK5) ),
% 19.71/2.98      inference(cnf_transformation,[],[f106]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_44,plain,
% 19.71/2.98      ( v2_pre_topc(sK5) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_40,negated_conjecture,
% 19.71/2.98      ( v1_tdlat_3(sK5) ),
% 19.71/2.98      inference(cnf_transformation,[],[f107]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_45,plain,
% 19.71/2.98      ( v1_tdlat_3(sK5) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_39,negated_conjecture,
% 19.71/2.98      ( l1_pre_topc(sK5) ),
% 19.71/2.98      inference(cnf_transformation,[],[f108]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_46,plain,
% 19.71/2.98      ( l1_pre_topc(sK5) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_47,plain,
% 19.71/2.98      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_34,plain,
% 19.71/2.98      ( v2_tex_2(X0,X1)
% 19.71/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.71/2.98      | v2_struct_0(X1)
% 19.71/2.98      | ~ v2_pre_topc(X1)
% 19.71/2.98      | ~ v1_tdlat_3(X1)
% 19.71/2.98      | ~ l1_pre_topc(X1) ),
% 19.71/2.98      inference(cnf_transformation,[],[f103]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2018,plain,
% 19.71/2.98      ( v2_tex_2(sK6,sK5)
% 19.71/2.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | v2_struct_0(sK5)
% 19.71/2.98      | ~ v2_pre_topc(sK5)
% 19.71/2.98      | ~ v1_tdlat_3(sK5)
% 19.71/2.98      | ~ l1_pre_topc(sK5) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_34]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2019,plain,
% 19.71/2.98      ( v2_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 19.71/2.98      | v2_struct_0(sK5) = iProver_top
% 19.71/2.98      | v2_pre_topc(sK5) != iProver_top
% 19.71/2.98      | v1_tdlat_3(sK5) != iProver_top
% 19.71/2.98      | l1_pre_topc(sK5) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_2018]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6733,plain,
% 19.71/2.98      ( r1_tarski(sK6,sK3(sK5,sK6)) = iProver_top
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_6261,c_43,c_44,c_45,c_46,c_47,c_2019]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6734,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | r1_tarski(sK6,sK3(sK5,sK6)) = iProver_top ),
% 19.71/2.98      inference(renaming,[status(thm)],[c_6733]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1466,plain,
% 19.71/2.98      ( r1_tarski(X0,X1) != iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6,plain,
% 19.71/2.98      ( ~ r2_hidden(X0,X1)
% 19.71/2.98      | r2_hidden(X0,X2)
% 19.71/2.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 19.71/2.98      inference(cnf_transformation,[],[f75]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1473,plain,
% 19.71/2.98      ( r2_hidden(X0,X1) != iProver_top
% 19.71/2.98      | r2_hidden(X0,X2) = iProver_top
% 19.71/2.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_5086,plain,
% 19.71/2.98      ( r1_tarski(X0,X1) != iProver_top
% 19.71/2.98      | r2_hidden(X2,X0) != iProver_top
% 19.71/2.98      | r2_hidden(X2,X1) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1466,c_1473]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_11707,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | r2_hidden(X0,sK3(sK5,sK6)) = iProver_top
% 19.71/2.98      | r2_hidden(X0,sK6) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_6734,c_5086]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_13,plain,
% 19.71/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.71/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.71/2.98      | m1_subset_1(sK1(X1,X0,X2),X1)
% 19.71/2.98      | X2 = X0 ),
% 19.71/2.98      inference(cnf_transformation,[],[f80]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_361,plain,
% 19.71/2.98      ( ~ r1_tarski(X0,X1)
% 19.71/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.71/2.98      | m1_subset_1(sK1(X1,X0,X2),X1)
% 19.71/2.98      | X2 = X0 ),
% 19.71/2.98      inference(bin_hyper_res,[status(thm)],[c_13,c_282]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1440,plain,
% 19.71/2.98      ( X0 = X1
% 19.71/2.98      | r1_tarski(X1,X2) != iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 19.71/2.98      | m1_subset_1(sK1(X2,X1,X0),X2) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_361]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_4,plain,
% 19.71/2.98      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 19.71/2.98      inference(cnf_transformation,[],[f70]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1475,plain,
% 19.71/2.98      ( r2_hidden(X0,X1) = iProver_top
% 19.71/2.98      | m1_subset_1(X0,X1) != iProver_top
% 19.71/2.98      | v1_xboole_0(X1) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_4583,plain,
% 19.71/2.98      ( X0 = X1
% 19.71/2.98      | r1_tarski(X0,X2) != iProver_top
% 19.71/2.98      | r2_hidden(sK1(X2,X0,X1),X2) = iProver_top
% 19.71/2.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 19.71/2.98      | v1_xboole_0(X2) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1440,c_1475]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_11,plain,
% 19.71/2.98      ( ~ r2_hidden(sK1(X0,X1,X2),X2)
% 19.71/2.98      | ~ r2_hidden(sK1(X0,X1,X2),X1)
% 19.71/2.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 19.71/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 19.71/2.98      | X2 = X1 ),
% 19.71/2.98      inference(cnf_transformation,[],[f82]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1468,plain,
% 19.71/2.98      ( X0 = X1
% 19.71/2.98      | r2_hidden(sK1(X2,X1,X0),X0) != iProver_top
% 19.71/2.98      | r2_hidden(sK1(X2,X1,X0),X1) != iProver_top
% 19.71/2.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_16840,plain,
% 19.71/2.98      ( X0 = X1
% 19.71/2.98      | r1_tarski(X1,X0) != iProver_top
% 19.71/2.98      | r2_hidden(sK1(X0,X1,X0),X1) != iProver_top
% 19.71/2.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
% 19.71/2.98      | v1_xboole_0(X0) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_4583,c_1468]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_18,plain,
% 19.71/2.98      ( ~ r2_hidden(X0,X1)
% 19.71/2.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 19.71/2.98      | ~ v1_xboole_0(X2) ),
% 19.71/2.98      inference(cnf_transformation,[],[f87]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1463,plain,
% 19.71/2.98      ( r2_hidden(X0,X1) != iProver_top
% 19.71/2.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 19.71/2.98      | v1_xboole_0(X2) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_38104,plain,
% 19.71/2.98      ( X0 = X1
% 19.71/2.98      | r2_hidden(sK1(X1,X0,X1),X0) != iProver_top
% 19.71/2.98      | m1_subset_1(X1,k1_zfmisc_1(X1)) != iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 19.71/2.98      inference(forward_subsumption_resolution,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_16840,c_1463,c_1465]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_38110,plain,
% 19.71/2.98      ( sK3(sK5,sK6) = X0
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | r2_hidden(sK1(X0,sK3(sK5,sK6),X0),sK6) != iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top
% 19.71/2.98      | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(X0)) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_11707,c_38104]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_24,plain,
% 19.71/2.98      ( ~ v2_tex_2(X0,X1)
% 19.71/2.98      | v3_tex_2(X0,X1)
% 19.71/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.71/2.98      | ~ l1_pre_topc(X1)
% 19.71/2.98      | sK3(X1,X0) != X0 ),
% 19.71/2.98      inference(cnf_transformation,[],[f98]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2165,plain,
% 19.71/2.98      ( ~ v2_tex_2(sK6,sK5)
% 19.71/2.98      | v3_tex_2(sK6,sK5)
% 19.71/2.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | ~ l1_pre_topc(sK5)
% 19.71/2.98      | sK3(sK5,sK6) != sK6 ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_24]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2166,plain,
% 19.71/2.98      ( sK3(sK5,sK6) != sK6
% 19.71/2.98      | v2_tex_2(sK6,sK5) != iProver_top
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 19.71/2.98      | l1_pre_topc(sK5) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_2165]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_482,plain,( X0 = X0 ),theory(equality) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2201,plain,
% 19.71/2.98      ( sK6 = sK6 ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_482]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2254,plain,
% 19.71/2.98      ( r1_tarski(sK6,u1_struct_0(sK5)) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1445,c_1465]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_3601,plain,
% 19.71/2.98      ( u1_struct_0(sK5) = sK6
% 19.71/2.98      | v1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_2254,c_1438]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_37,negated_conjecture,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) | ~ v1_subset_1(sK6,u1_struct_0(sK5)) ),
% 19.71/2.98      inference(cnf_transformation,[],[f110]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1446,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | v1_subset_1(sK6,u1_struct_0(sK5)) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_4104,plain,
% 19.71/2.98      ( u1_struct_0(sK5) = sK6 | v3_tex_2(sK6,sK5) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_3601,c_1446]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_487,plain,
% 19.71/2.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 19.71/2.98      theory(equality) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_3191,plain,
% 19.71/2.98      ( v1_subset_1(X0,X1)
% 19.71/2.98      | ~ r1_tarski(X0,X1)
% 19.71/2.98      | ~ v1_xboole_0(X0)
% 19.71/2.98      | v1_xboole_0(X1) ),
% 19.71/2.98      inference(resolution,[status(thm)],[c_366,c_487]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_5820,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5)
% 19.71/2.98      | ~ r1_tarski(sK6,u1_struct_0(sK5))
% 19.71/2.98      | v1_xboole_0(u1_struct_0(sK5))
% 19.71/2.98      | ~ v1_xboole_0(sK6) ),
% 19.71/2.98      inference(resolution,[status(thm)],[c_3191,c_37]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1884,plain,
% 19.71/2.98      ( r1_tarski(sK6,u1_struct_0(sK5))
% 19.71/2.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_16]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_35,plain,
% 19.71/2.98      ( ~ v3_tex_2(X0,X1)
% 19.71/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.71/2.98      | v2_struct_0(X1)
% 19.71/2.98      | ~ v2_pre_topc(X1)
% 19.71/2.98      | ~ l1_pre_topc(X1)
% 19.71/2.98      | ~ v1_xboole_0(X0) ),
% 19.71/2.98      inference(cnf_transformation,[],[f104]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1448,plain,
% 19.71/2.98      ( v3_tex_2(X0,X1) != iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 19.71/2.98      | v2_struct_0(X1) = iProver_top
% 19.71/2.98      | v2_pre_topc(X1) != iProver_top
% 19.71/2.98      | l1_pre_topc(X1) != iProver_top
% 19.71/2.98      | v1_xboole_0(X0) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_5664,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) != iProver_top
% 19.71/2.98      | v2_struct_0(sK5) = iProver_top
% 19.71/2.98      | v2_pre_topc(sK5) != iProver_top
% 19.71/2.98      | l1_pre_topc(sK5) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1445,c_1448]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_5782,plain,
% 19.71/2.98      ( ~ v3_tex_2(sK6,sK5)
% 19.71/2.98      | v2_struct_0(sK5)
% 19.71/2.98      | ~ v2_pre_topc(sK5)
% 19.71/2.98      | ~ l1_pre_topc(sK5)
% 19.71/2.98      | ~ v1_xboole_0(sK6) ),
% 19.71/2.98      inference(predicate_to_equality_rev,[status(thm)],[c_5664]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6048,plain,
% 19.71/2.98      ( v1_xboole_0(u1_struct_0(sK5)) | ~ v1_xboole_0(sK6) ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_5820,c_42,c_41,c_39,c_38,c_1884,c_5782]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6050,plain,
% 19.71/2.98      ( v1_xboole_0(u1_struct_0(sK5)) = iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_6048]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_483,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2421,plain,
% 19.71/2.98      ( X0 != X1 | X0 = u1_struct_0(sK5) | u1_struct_0(sK5) != X1 ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_483]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_3904,plain,
% 19.71/2.98      ( X0 = u1_struct_0(sK5) | X0 != sK6 | u1_struct_0(sK5) != sK6 ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_2421]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_7477,plain,
% 19.71/2.98      ( u1_struct_0(sK5) != sK6 | sK6 = u1_struct_0(sK5) | sK6 != sK6 ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_3904]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_5091,plain,
% 19.71/2.98      ( r2_hidden(X0,u1_struct_0(sK5)) = iProver_top
% 19.71/2.98      | r2_hidden(X0,sK6) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1445,c_1473]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_12017,plain,
% 19.71/2.98      ( sK3(sK5,sK6) = X0
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | r2_hidden(sK1(X1,X0,sK3(sK5,sK6)),X0) != iProver_top
% 19.71/2.98      | r2_hidden(sK1(X1,X0,sK3(sK5,sK6)),sK6) != iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.71/2.98      | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(X1)) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_11707,c_1468]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_12228,plain,
% 19.71/2.98      ( sK3(sK5,sK6) = u1_struct_0(sK5)
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | r2_hidden(sK1(X0,u1_struct_0(sK5),sK3(sK5,sK6)),sK6) != iProver_top
% 19.71/2.98      | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(X0)) != iProver_top
% 19.71/2.98      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(X0)) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_5091,c_12017]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_16856,plain,
% 19.71/2.98      ( sK3(sK5,sK6) = u1_struct_0(sK5)
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | r1_tarski(u1_struct_0(sK5),sK6) != iProver_top
% 19.71/2.98      | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(sK6)) != iProver_top
% 19.71/2.98      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK6)) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_4583,c_12228]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_27,plain,
% 19.71/2.98      ( ~ v2_tex_2(X0,X1)
% 19.71/2.98      | v3_tex_2(X0,X1)
% 19.71/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.71/2.98      | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.71/2.98      | ~ l1_pre_topc(X1) ),
% 19.71/2.98      inference(cnf_transformation,[],[f95]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2162,plain,
% 19.71/2.98      ( ~ v2_tex_2(sK6,sK5)
% 19.71/2.98      | v3_tex_2(sK6,sK5)
% 19.71/2.98      | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | ~ l1_pre_topc(sK5) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_27]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2172,plain,
% 19.71/2.98      ( v2_tex_2(sK6,sK5) != iProver_top
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 19.71/2.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 19.71/2.98      | l1_pre_topc(sK5) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_2162]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_3241,plain,
% 19.71/2.98      ( r1_tarski(sK3(sK5,sK6),u1_struct_0(sK5))
% 19.71/2.98      | ~ m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_16]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_3242,plain,
% 19.71/2.98      ( r1_tarski(sK3(sK5,sK6),u1_struct_0(sK5)) = iProver_top
% 19.71/2.98      | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_3241]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_489,plain,
% 19.71/2.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X2) | X2 != X1 ),
% 19.71/2.98      theory(equality) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_3583,plain,
% 19.71/2.98      ( r1_tarski(sK3(sK5,sK6),X0)
% 19.71/2.98      | ~ r1_tarski(sK3(sK5,sK6),u1_struct_0(sK5))
% 19.71/2.98      | X0 != u1_struct_0(sK5) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_489]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_12985,plain,
% 19.71/2.98      ( ~ r1_tarski(sK3(sK5,sK6),u1_struct_0(sK5))
% 19.71/2.98      | r1_tarski(sK3(sK5,sK6),sK6)
% 19.71/2.98      | sK6 != u1_struct_0(sK5) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_3583]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_12993,plain,
% 19.71/2.98      ( sK6 != u1_struct_0(sK5)
% 19.71/2.98      | r1_tarski(sK3(sK5,sK6),u1_struct_0(sK5)) != iProver_top
% 19.71/2.98      | r1_tarski(sK3(sK5,sK6),sK6) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_12985]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_7693,plain,
% 19.71/2.98      ( u1_struct_0(sK5) = X0
% 19.71/2.98      | r2_hidden(sK1(X1,X0,u1_struct_0(sK5)),X0) != iProver_top
% 19.71/2.98      | r2_hidden(sK1(X1,X0,u1_struct_0(sK5)),sK6) != iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.71/2.98      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(X1)) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_5091,c_1468]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_12018,plain,
% 19.71/2.98      ( sK3(sK5,sK6) = u1_struct_0(sK5)
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | r2_hidden(sK1(X0,sK3(sK5,sK6),u1_struct_0(sK5)),sK6) != iProver_top
% 19.71/2.98      | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(X0)) != iProver_top
% 19.71/2.98      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(X0)) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_11707,c_7693]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_16855,plain,
% 19.71/2.98      ( sK3(sK5,sK6) = u1_struct_0(sK5)
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | r1_tarski(sK3(sK5,sK6),sK6) != iProver_top
% 19.71/2.98      | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(sK6)) != iProver_top
% 19.71/2.98      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK6)) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_4583,c_12018]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_19426,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | sK3(sK5,sK6) = u1_struct_0(sK5)
% 19.71/2.98      | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(sK6)) != iProver_top
% 19.71/2.98      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK6)) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_16856,c_43,c_44,c_45,c_46,c_47,c_2019,c_2172,c_2201,
% 19.71/2.98                 c_3242,c_4104,c_7477,c_12993,c_16855]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_19427,plain,
% 19.71/2.98      ( sK3(sK5,sK6) = u1_struct_0(sK5)
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(sK6)) != iProver_top
% 19.71/2.98      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK6)) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(renaming,[status(thm)],[c_19426]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_19436,plain,
% 19.71/2.98      ( sK3(sK5,sK6) = u1_struct_0(sK5)
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | r1_tarski(sK3(sK5,sK6),sK6) != iProver_top
% 19.71/2.98      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK6)) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1466,c_19427]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_29813,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | sK3(sK5,sK6) = u1_struct_0(sK5)
% 19.71/2.98      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK6)) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_19436,c_43,c_44,c_45,c_46,c_47,c_2019,c_2172,c_2201,
% 19.71/2.98                 c_3242,c_4104,c_7477,c_12993]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_29814,plain,
% 19.71/2.98      ( sK3(sK5,sK6) = u1_struct_0(sK5)
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(sK6)) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(renaming,[status(thm)],[c_29813]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_29822,plain,
% 19.71/2.98      ( sK3(sK5,sK6) = u1_struct_0(sK5)
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | r1_tarski(u1_struct_0(sK5),sK6) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1466,c_29814]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_486,plain,
% 19.71/2.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.71/2.98      theory(equality) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2041,plain,
% 19.71/2.98      ( m1_subset_1(X0,X1)
% 19.71/2.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | X1 != k1_zfmisc_1(u1_struct_0(sK5))
% 19.71/2.98      | X0 != sK6 ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_486]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_3151,plain,
% 19.71/2.98      ( m1_subset_1(u1_struct_0(sK5),X0)
% 19.71/2.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | X0 != k1_zfmisc_1(u1_struct_0(sK5))
% 19.71/2.98      | u1_struct_0(sK5) != sK6 ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_2041]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_3525,plain,
% 19.71/2.98      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | u1_struct_0(sK5) != sK6
% 19.71/2.98      | k1_zfmisc_1(u1_struct_0(sK5)) != k1_zfmisc_1(u1_struct_0(sK5)) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_3151]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_3527,plain,
% 19.71/2.98      ( u1_struct_0(sK5) != sK6
% 19.71/2.98      | k1_zfmisc_1(u1_struct_0(sK5)) != k1_zfmisc_1(u1_struct_0(sK5))
% 19.71/2.98      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 19.71/2.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_3525]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_3526,plain,
% 19.71/2.98      ( k1_zfmisc_1(u1_struct_0(sK5)) = k1_zfmisc_1(u1_struct_0(sK5)) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_482]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6410,plain,
% 19.71/2.98      ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5))
% 19.71/2.98      | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_16]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6411,plain,
% 19.71/2.98      ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) = iProver_top
% 19.71/2.98      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_6410]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_8582,plain,
% 19.71/2.98      ( r1_tarski(u1_struct_0(sK5),X0)
% 19.71/2.98      | ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5))
% 19.71/2.98      | X0 != u1_struct_0(sK5) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_489]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_20547,plain,
% 19.71/2.98      ( ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5))
% 19.71/2.98      | r1_tarski(u1_struct_0(sK5),sK6)
% 19.71/2.98      | sK6 != u1_struct_0(sK5) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_8582]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_20548,plain,
% 19.71/2.98      ( sK6 != u1_struct_0(sK5)
% 19.71/2.98      | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top
% 19.71/2.98      | r1_tarski(u1_struct_0(sK5),sK6) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_20547]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_29838,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | sK3(sK5,sK6) = u1_struct_0(sK5)
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_29822,c_47,c_2201,c_3527,c_3526,c_4104,c_6411,c_7477,
% 19.71/2.98                 c_20548]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_29839,plain,
% 19.71/2.98      ( sK3(sK5,sK6) = u1_struct_0(sK5)
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(renaming,[status(thm)],[c_29838]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_12,plain,
% 19.71/2.98      ( r2_hidden(sK1(X0,X1,X2),X2)
% 19.71/2.98      | r2_hidden(sK1(X0,X1,X2),X1)
% 19.71/2.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 19.71/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 19.71/2.98      | X2 = X1 ),
% 19.71/2.98      inference(cnf_transformation,[],[f81]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1467,plain,
% 19.71/2.98      ( X0 = X1
% 19.71/2.98      | r2_hidden(sK1(X2,X1,X0),X0) = iProver_top
% 19.71/2.98      | r2_hidden(sK1(X2,X1,X0),X1) = iProver_top
% 19.71/2.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1456,plain,
% 19.71/2.98      ( v2_tex_2(X0,X1) != iProver_top
% 19.71/2.98      | v3_tex_2(X0,X1) = iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 19.71/2.98      | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 19.71/2.98      | l1_pre_topc(X1) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_7257,plain,
% 19.71/2.98      ( v2_tex_2(X0,X1) != iProver_top
% 19.71/2.98      | v3_tex_2(X0,X1) = iProver_top
% 19.71/2.98      | r2_hidden(X2,sK3(X1,X0)) != iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 19.71/2.98      | l1_pre_topc(X1) != iProver_top
% 19.71/2.98      | v1_xboole_0(u1_struct_0(X1)) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1456,c_1463]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_16242,plain,
% 19.71/2.98      ( v2_tex_2(sK6,sK5) != iProver_top
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | r2_hidden(X0,sK3(sK5,sK6)) != iProver_top
% 19.71/2.98      | l1_pre_topc(sK5) != iProver_top
% 19.71/2.98      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1445,c_7257]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1885,plain,
% 19.71/2.98      ( r1_tarski(sK6,u1_struct_0(sK5)) = iProver_top
% 19.71/2.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_1884]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_14,plain,
% 19.71/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.71/2.98      | ~ v1_xboole_0(X1)
% 19.71/2.98      | v1_xboole_0(X0) ),
% 19.71/2.98      inference(cnf_transformation,[],[f83]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_362,plain,
% 19.71/2.98      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 19.71/2.98      inference(bin_hyper_res,[status(thm)],[c_14,c_282]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2135,plain,
% 19.71/2.98      ( ~ r1_tarski(sK6,u1_struct_0(sK5))
% 19.71/2.98      | ~ v1_xboole_0(u1_struct_0(sK5))
% 19.71/2.98      | v1_xboole_0(sK6) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_362]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2137,plain,
% 19.71/2.98      ( r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top
% 19.71/2.98      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_2135]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6479,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) != iProver_top ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_5664,c_43,c_44,c_46,c_47,c_2356]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_16378,plain,
% 19.71/2.98      ( r2_hidden(X0,sK3(sK5,sK6)) != iProver_top
% 19.71/2.98      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_16242,c_43,c_44,c_45,c_46,c_47,c_1885,c_2019,c_2137,
% 19.71/2.98                 c_6479]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_16386,plain,
% 19.71/2.98      ( sK3(sK5,sK6) = X0
% 19.71/2.98      | r2_hidden(sK1(X1,X0,sK3(sK5,sK6)),X0) = iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.71/2.98      | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(X1)) != iProver_top
% 19.71/2.98      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1467,c_16378]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_20,plain,
% 19.71/2.98      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 19.71/2.98      | ~ l1_pre_topc(X0) ),
% 19.71/2.98      inference(cnf_transformation,[],[f88]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1461,plain,
% 19.71/2.98      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 19.71/2.98      | l1_pre_topc(X0) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_16239,plain,
% 19.71/2.98      ( v2_tex_2(sK2(X0),X0) != iProver_top
% 19.71/2.98      | v3_tex_2(sK2(X0),X0) = iProver_top
% 19.71/2.98      | r2_hidden(X1,sK3(X0,sK2(X0))) != iProver_top
% 19.71/2.98      | l1_pre_topc(X0) != iProver_top
% 19.71/2.98      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1461,c_7257]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_36694,plain,
% 19.71/2.98      ( sK3(X0,sK2(X0)) = sK3(sK5,sK6)
% 19.71/2.98      | v2_tex_2(sK2(X0),X0) != iProver_top
% 19.71/2.98      | v3_tex_2(sK2(X0),X0) = iProver_top
% 19.71/2.98      | m1_subset_1(sK3(X0,sK2(X0)),k1_zfmisc_1(X1)) != iProver_top
% 19.71/2.98      | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(X1)) != iProver_top
% 19.71/2.98      | l1_pre_topc(X0) != iProver_top
% 19.71/2.98      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 19.71/2.98      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_16386,c_16239]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2190,plain,
% 19.71/2.98      ( r2_hidden(sK1(X0,sK6,X1),X1)
% 19.71/2.98      | r2_hidden(sK1(X0,sK6,X1),sK6)
% 19.71/2.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 19.71/2.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
% 19.71/2.98      | X1 = sK6 ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_12]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2557,plain,
% 19.71/2.98      ( r2_hidden(sK1(u1_struct_0(sK5),sK6,X0),X0)
% 19.71/2.98      | r2_hidden(sK1(u1_struct_0(sK5),sK6,X0),sK6)
% 19.71/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | X0 = sK6 ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_2190]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_3248,plain,
% 19.71/2.98      ( r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK3(sK5,sK6))
% 19.71/2.98      | r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK6)
% 19.71/2.98      | ~ m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | sK3(sK5,sK6) = sK6 ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_2557]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_3249,plain,
% 19.71/2.98      ( sK3(sK5,sK6) = sK6
% 19.71/2.98      | r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK3(sK5,sK6)) = iProver_top
% 19.71/2.98      | r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK6) = iProver_top
% 19.71/2.98      | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 19.71/2.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_3248]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_3458,plain,
% 19.71/2.98      ( ~ r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK3(sK5,sK6))
% 19.71/2.98      | ~ m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(X0))
% 19.71/2.98      | ~ v1_xboole_0(X0) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_18]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_14437,plain,
% 19.71/2.98      ( ~ r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK3(sK5,sK6))
% 19.71/2.98      | ~ m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_3458]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_14438,plain,
% 19.71/2.98      ( r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK3(sK5,sK6)) != iProver_top
% 19.71/2.98      | m1_subset_1(sK3(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 19.71/2.98      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_14437]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6697,plain,
% 19.71/2.98      ( ~ r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK6)
% 19.71/2.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
% 19.71/2.98      | ~ v1_xboole_0(X0) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_18]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_37314,plain,
% 19.71/2.98      ( ~ r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK6)
% 19.71/2.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_6697]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_37315,plain,
% 19.71/2.98      ( r2_hidden(sK1(u1_struct_0(sK5),sK6,sK3(sK5,sK6)),sK6) != iProver_top
% 19.71/2.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 19.71/2.98      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_37314]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_37333,plain,
% 19.71/2.98      ( v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_36694,c_43,c_44,c_45,c_46,c_47,c_1885,c_2019,c_2137,
% 19.71/2.98                 c_2166,c_2172,c_3249,c_6479,c_14438,c_37315]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2183,plain,
% 19.71/2.98      ( X0 != X1 | X0 = sK6 | sK6 != X1 ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_483]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_12996,plain,
% 19.71/2.98      ( X0 != u1_struct_0(sK5) | X0 = sK6 | sK6 != u1_struct_0(sK5) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_2183]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_38011,plain,
% 19.71/2.98      ( sK3(sK5,sK6) != u1_struct_0(sK5)
% 19.71/2.98      | sK3(sK5,sK6) = sK6
% 19.71/2.98      | sK6 != u1_struct_0(sK5) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_12996]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_38745,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) = iProver_top ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_38110,c_43,c_44,c_45,c_46,c_47,c_1885,c_2019,c_2137,
% 19.71/2.98                 c_2166,c_2172,c_2201,c_3249,c_4104,c_6050,c_6479,c_7477,
% 19.71/2.98                 c_14438,c_29839,c_37315,c_38011]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_36,negated_conjecture,
% 19.71/2.98      ( ~ v3_tex_2(sK6,sK5) | v1_subset_1(sK6,u1_struct_0(sK5)) ),
% 19.71/2.98      inference(cnf_transformation,[],[f111]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1447,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) != iProver_top
% 19.71/2.98      | v1_subset_1(sK6,u1_struct_0(sK5)) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_21,plain,
% 19.71/2.98      ( ~ v1_subset_1(X0,X1)
% 19.71/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.71/2.98      | ~ v1_zfmisc_1(X1)
% 19.71/2.98      | v1_xboole_0(X0)
% 19.71/2.98      | v1_xboole_0(X1) ),
% 19.71/2.98      inference(cnf_transformation,[],[f90]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_365,plain,
% 19.71/2.98      ( ~ v1_subset_1(X0,X1)
% 19.71/2.98      | ~ r1_tarski(X0,X1)
% 19.71/2.98      | ~ v1_zfmisc_1(X1)
% 19.71/2.98      | v1_xboole_0(X0)
% 19.71/2.98      | v1_xboole_0(X1) ),
% 19.71/2.98      inference(bin_hyper_res,[status(thm)],[c_21,c_282]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_434,plain,
% 19.71/2.98      ( v1_xboole_0(X0)
% 19.71/2.98      | ~ v1_zfmisc_1(X1)
% 19.71/2.98      | ~ r1_tarski(X0,X1)
% 19.71/2.98      | ~ v1_subset_1(X0,X1) ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_365,c_21,c_15,c_362]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_435,plain,
% 19.71/2.98      ( ~ v1_subset_1(X0,X1)
% 19.71/2.98      | ~ r1_tarski(X0,X1)
% 19.71/2.98      | ~ v1_zfmisc_1(X1)
% 19.71/2.98      | v1_xboole_0(X0) ),
% 19.71/2.98      inference(renaming,[status(thm)],[c_434]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1437,plain,
% 19.71/2.98      ( v1_subset_1(X0,X1) != iProver_top
% 19.71/2.98      | r1_tarski(X0,X1) != iProver_top
% 19.71/2.98      | v1_zfmisc_1(X1) != iProver_top
% 19.71/2.98      | v1_xboole_0(X0) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2587,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) != iProver_top
% 19.71/2.98      | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top
% 19.71/2.98      | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1447,c_1437]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2352,plain,
% 19.71/2.98      ( ~ v3_tex_2(sK6,sK5)
% 19.71/2.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | v2_struct_0(sK5)
% 19.71/2.98      | ~ v2_pre_topc(sK5)
% 19.71/2.98      | ~ l1_pre_topc(sK5)
% 19.71/2.98      | ~ v1_xboole_0(sK6) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_35]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2356,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) != iProver_top
% 19.71/2.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 19.71/2.98      | v2_struct_0(sK5) = iProver_top
% 19.71/2.98      | v2_pre_topc(sK5) != iProver_top
% 19.71/2.98      | l1_pre_topc(sK5) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_2352]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_3050,plain,
% 19.71/2.98      ( v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
% 19.71/2.98      | v3_tex_2(sK6,sK5) != iProver_top ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_2587,c_43,c_44,c_46,c_47,c_1885,c_2356]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_3051,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) != iProver_top
% 19.71/2.98      | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top ),
% 19.71/2.98      inference(renaming,[status(thm)],[c_3050]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_38752,plain,
% 19.71/2.98      ( v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_38745,c_3051]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_72795,plain,
% 19.71/2.98      ( sK4(u1_struct_0(sK5)) = u1_struct_0(sK5)
% 19.71/2.98      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_72785,c_38752]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_73540,plain,
% 19.71/2.98      ( sK4(u1_struct_0(sK5)) = u1_struct_0(sK5) ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_72795,c_43,c_44,c_45,c_46,c_47,c_1885,c_2019,c_2137,
% 19.71/2.98                 c_2166,c_2172,c_3249,c_6479,c_14438,c_37315]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_28,plain,
% 19.71/2.98      ( ~ v2_tex_2(X0,X1)
% 19.71/2.98      | ~ v3_tex_2(X2,X1)
% 19.71/2.98      | ~ r1_tarski(X2,X0)
% 19.71/2.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.71/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.71/2.98      | ~ l1_pre_topc(X1)
% 19.71/2.98      | X0 = X2 ),
% 19.71/2.98      inference(cnf_transformation,[],[f94]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1455,plain,
% 19.71/2.98      ( X0 = X1
% 19.71/2.98      | v2_tex_2(X0,X2) != iProver_top
% 19.71/2.98      | v3_tex_2(X1,X2) != iProver_top
% 19.71/2.98      | r1_tarski(X1,X0) != iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 19.71/2.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 19.71/2.98      | l1_pre_topc(X2) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_7873,plain,
% 19.71/2.98      ( X0 = X1
% 19.71/2.98      | v2_tex_2(X1,X2) != iProver_top
% 19.71/2.98      | v3_tex_2(X0,X2) != iProver_top
% 19.71/2.98      | r1_tarski(X0,X1) != iProver_top
% 19.71/2.98      | r1_tarski(X1,u1_struct_0(X2)) != iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
% 19.71/2.98      | l1_pre_topc(X2) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1466,c_1455]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_50049,plain,
% 19.71/2.98      ( sK6 = X0
% 19.71/2.98      | v2_tex_2(X0,sK5) != iProver_top
% 19.71/2.98      | v3_tex_2(sK6,sK5) != iProver_top
% 19.71/2.98      | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
% 19.71/2.98      | r1_tarski(sK6,X0) != iProver_top
% 19.71/2.98      | l1_pre_topc(sK5) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_1445,c_7873]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_50467,plain,
% 19.71/2.98      ( r1_tarski(sK6,X0) != iProver_top
% 19.71/2.98      | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
% 19.71/2.98      | sK6 = X0
% 19.71/2.98      | v2_tex_2(X0,sK5) != iProver_top ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_50049,c_43,c_44,c_45,c_46,c_47,c_1885,c_2019,c_2137,
% 19.71/2.98                 c_2166,c_2172,c_2201,c_3249,c_4104,c_6050,c_6479,c_7477,
% 19.71/2.98                 c_14438,c_29839,c_37315,c_38011]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_50468,plain,
% 19.71/2.98      ( sK6 = X0
% 19.71/2.98      | v2_tex_2(X0,sK5) != iProver_top
% 19.71/2.98      | r1_tarski(X0,u1_struct_0(sK5)) != iProver_top
% 19.71/2.98      | r1_tarski(sK6,X0) != iProver_top ),
% 19.71/2.98      inference(renaming,[status(thm)],[c_50467]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_50480,plain,
% 19.71/2.98      ( sK4(u1_struct_0(sK5)) = sK6
% 19.71/2.98      | v2_tex_2(sK4(u1_struct_0(sK5)),sK5) != iProver_top
% 19.71/2.98      | r1_tarski(sK6,sK4(u1_struct_0(sK5))) != iProver_top
% 19.71/2.98      | v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top
% 19.71/2.98      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_2847,c_50468]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6791,plain,
% 19.71/2.98      ( v2_tex_2(sK4(u1_struct_0(X0)),X0)
% 19.71/2.98      | v2_struct_0(X0)
% 19.71/2.98      | ~ v2_pre_topc(X0)
% 19.71/2.98      | ~ v1_tdlat_3(X0)
% 19.71/2.98      | v1_zfmisc_1(u1_struct_0(X0))
% 19.71/2.98      | ~ l1_pre_topc(X0)
% 19.71/2.98      | v1_xboole_0(u1_struct_0(X0)) ),
% 19.71/2.98      inference(resolution,[status(thm)],[c_34,c_33]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6792,plain,
% 19.71/2.98      ( v2_tex_2(sK4(u1_struct_0(X0)),X0) = iProver_top
% 19.71/2.98      | v2_struct_0(X0) = iProver_top
% 19.71/2.98      | v2_pre_topc(X0) != iProver_top
% 19.71/2.98      | v1_tdlat_3(X0) != iProver_top
% 19.71/2.98      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
% 19.71/2.98      | l1_pre_topc(X0) != iProver_top
% 19.71/2.98      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_6791]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6794,plain,
% 19.71/2.98      ( v2_tex_2(sK4(u1_struct_0(sK5)),sK5) = iProver_top
% 19.71/2.98      | v2_struct_0(sK5) = iProver_top
% 19.71/2.98      | v2_pre_topc(sK5) != iProver_top
% 19.71/2.98      | v1_tdlat_3(sK5) != iProver_top
% 19.71/2.98      | v1_zfmisc_1(u1_struct_0(sK5)) = iProver_top
% 19.71/2.98      | l1_pre_topc(sK5) != iProver_top
% 19.71/2.98      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_6792]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_29847,plain,
% 19.71/2.98      ( sK3(sK5,sK6) = u1_struct_0(sK5)
% 19.71/2.98      | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_29839,c_3051]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6739,plain,
% 19.71/2.98      ( sK3(sK5,sK6) = sK6
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | v1_subset_1(sK6,sK3(sK5,sK6)) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_6734,c_1438]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6971,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | v1_subset_1(sK6,sK3(sK5,sK6)) = iProver_top ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_6739,c_43,c_44,c_45,c_46,c_47,c_2019,c_2166]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6977,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | r1_tarski(sK6,sK3(sK5,sK6)) != iProver_top
% 19.71/2.98      | v1_zfmisc_1(sK3(sK5,sK6)) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_6971,c_1437]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2164,plain,
% 19.71/2.98      ( ~ v2_tex_2(sK6,sK5)
% 19.71/2.98      | v3_tex_2(sK6,sK5)
% 19.71/2.98      | r1_tarski(sK6,sK3(sK5,sK6))
% 19.71/2.98      | ~ m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
% 19.71/2.98      | ~ l1_pre_topc(sK5) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_25]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_2168,plain,
% 19.71/2.98      ( v2_tex_2(sK6,sK5) != iProver_top
% 19.71/2.98      | v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | r1_tarski(sK6,sK3(sK5,sK6)) = iProver_top
% 19.71/2.98      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 19.71/2.98      | l1_pre_topc(sK5) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_2164]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_6980,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) = iProver_top
% 19.71/2.98      | v1_zfmisc_1(sK3(sK5,sK6)) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_6977,c_43,c_44,c_45,c_46,c_47,c_2019,c_2168]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_493,plain,
% 19.71/2.98      ( ~ v1_zfmisc_1(X0) | v1_zfmisc_1(X1) | X1 != X0 ),
% 19.71/2.98      theory(equality) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_8440,plain,
% 19.71/2.98      ( ~ v1_zfmisc_1(X0)
% 19.71/2.98      | v1_zfmisc_1(sK3(sK5,sK6))
% 19.71/2.98      | sK3(sK5,sK6) != X0 ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_493]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_20504,plain,
% 19.71/2.98      ( v1_zfmisc_1(sK3(sK5,sK6))
% 19.71/2.98      | ~ v1_zfmisc_1(u1_struct_0(sK5))
% 19.71/2.98      | sK3(sK5,sK6) != u1_struct_0(sK5) ),
% 19.71/2.98      inference(instantiation,[status(thm)],[c_8440]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_20505,plain,
% 19.71/2.98      ( sK3(sK5,sK6) != u1_struct_0(sK5)
% 19.71/2.98      | v1_zfmisc_1(sK3(sK5,sK6)) = iProver_top
% 19.71/2.98      | v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_20504]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_31085,plain,
% 19.71/2.98      ( v1_zfmisc_1(u1_struct_0(sK5)) != iProver_top
% 19.71/2.98      | v1_xboole_0(sK6) = iProver_top ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_29847,c_43,c_44,c_46,c_47,c_1885,c_2356,c_2587,c_6980,
% 19.71/2.98                 c_20505]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_50985,plain,
% 19.71/2.98      ( sK4(u1_struct_0(sK5)) = sK6
% 19.71/2.98      | r1_tarski(sK6,sK4(u1_struct_0(sK5))) != iProver_top ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_50480,c_43,c_44,c_45,c_46,c_47,c_1885,c_2019,c_2137,
% 19.71/2.98                 c_2166,c_2172,c_3249,c_6050,c_6479,c_6794,c_14438,
% 19.71/2.98                 c_31085,c_37315]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_73544,plain,
% 19.71/2.98      ( u1_struct_0(sK5) = sK6
% 19.71/2.98      | r1_tarski(sK6,u1_struct_0(sK5)) != iProver_top ),
% 19.71/2.98      inference(demodulation,[status(thm)],[c_73540,c_50985]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_73818,plain,
% 19.71/2.98      ( u1_struct_0(sK5) = sK6 ),
% 19.71/2.98      inference(global_propositional_subsumption,
% 19.71/2.98                [status(thm)],
% 19.71/2.98                [c_73544,c_47,c_1885]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_73966,plain,
% 19.71/2.98      ( m1_subset_1(sK6,k1_zfmisc_1(sK6)) = iProver_top ),
% 19.71/2.98      inference(demodulation,[status(thm)],[c_73818,c_1445]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_23,plain,
% 19.71/2.98      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 19.71/2.98      inference(cnf_transformation,[],[f112]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_1460,plain,
% 19.71/2.98      ( v1_subset_1(X0,X0) != iProver_top
% 19.71/2.98      | m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top ),
% 19.71/2.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_75958,plain,
% 19.71/2.98      ( v1_subset_1(sK6,sK6) != iProver_top ),
% 19.71/2.98      inference(superposition,[status(thm)],[c_73966,c_1460]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(c_73965,plain,
% 19.71/2.98      ( v3_tex_2(sK6,sK5) != iProver_top
% 19.71/2.98      | v1_subset_1(sK6,sK6) = iProver_top ),
% 19.71/2.98      inference(demodulation,[status(thm)],[c_73818,c_1447]) ).
% 19.71/2.98  
% 19.71/2.98  cnf(contradiction,plain,
% 19.71/2.98      ( $false ),
% 19.71/2.98      inference(minisat,[status(thm)],[c_75958,c_73965,c_38745]) ).
% 19.71/2.98  
% 19.71/2.98  
% 19.71/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.71/2.98  
% 19.71/2.98  ------                               Statistics
% 19.71/2.98  
% 19.71/2.98  ------ Selected
% 19.71/2.98  
% 19.71/2.98  total_time:                             2.098
% 19.71/2.98  
%------------------------------------------------------------------------------
