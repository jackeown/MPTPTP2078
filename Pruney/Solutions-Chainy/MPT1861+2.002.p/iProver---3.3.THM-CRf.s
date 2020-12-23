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
% DateTime   : Thu Dec  3 12:25:48 EST 2020

% Result     : Theorem 43.33s
% Output     : CNFRefutation 43.33s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 442 expanded)
%              Number of clauses        :   99 ( 164 expanded)
%              Number of leaves         :   20 ( 122 expanded)
%              Depth                    :   15
%              Number of atoms          :  487 (1843 expanded)
%              Number of equality atoms :  121 ( 188 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & ( v2_tex_2(X2,X0)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK4),X0)
        & ( v2_tex_2(sK4,X0)
          | v2_tex_2(X1,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),sK3,X2),X0)
            & ( v2_tex_2(X2,X0)
              | v2_tex_2(sK3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK2),X1,X2),sK2)
              & ( v2_tex_2(X2,sK2)
                | v2_tex_2(X1,sK2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    & ( v2_tex_2(sK4,sK2)
      | v2_tex_2(sK3,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f30,f29,f28])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f43])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f36,f54])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f52,plain,
    ( v2_tex_2(sK4,sK2)
    | v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_25818,plain,
    ( ~ r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),X0),X0)
    | r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_144286,plain,
    ( ~ r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),sK4)
    | r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_25818])).

cnf(c_144287,plain,
    ( r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),sK4) != iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_144286])).

cnf(c_895,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_894,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2867,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_895,c_894])).

cnf(c_897,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_10901,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_2867,c_897])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_104703,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | X0 != sK3
    | X1 != sK2 ),
    inference(resolution,[status(thm)],[c_10901,c_18])).

cnf(c_14,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_258,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_259,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_1524,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK3,X0) ),
    inference(resolution,[status(thm)],[c_259,c_18])).

cnf(c_105344,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK3,sK2)
    | ~ r1_tarski(sK3,X0)
    | X0 != sK3
    | sK2 != sK2 ),
    inference(resolution,[status(thm)],[c_104703,c_1524])).

cnf(c_105351,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK3,sK2)
    | ~ r1_tarski(sK3,X0)
    | X0 != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_105344])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_905,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_888,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_907,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_888])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1495,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[status(thm)],[c_13,c_17])).

cnf(c_1911,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1552,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2110,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1552])).

cnf(c_2124,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_888])).

cnf(c_2202,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_894])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1615,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK2)),X0)
    | r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2298,plain,
    ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1615])).

cnf(c_2600,plain,
    ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2))
    | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3401,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(X0))
    | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4365,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(sK3))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_889,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2012,plain,
    ( X0 != X1
    | X0 = k1_setfam_1(k2_enumset1(X2,X2,X2,X3))
    | k1_setfam_1(k2_enumset1(X2,X2,X2,X3)) != X1 ),
    inference(instantiation,[status(thm)],[c_889])).

cnf(c_2962,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X0
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_2012])).

cnf(c_3264,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,sK4)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != k9_subset_1(u1_struct_0(sK2),sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2962])).

cnf(c_5584,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,sK4)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4))
    | k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)) != k9_subset_1(u1_struct_0(sK2),sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3264])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k2_enumset1(X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_146,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_147,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_146])).

cnf(c_184,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_enumset1(X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_147])).

cnf(c_5585,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK2))
    | k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)) = k9_subset_1(u1_struct_0(sK2),sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_7691,plain,
    ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),X0)
    | ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_890,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_3414,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X1)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_890])).

cnf(c_13886,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0)
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),X0)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3414])).

cnf(c_25841,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK3)
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK3)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_13886])).

cnf(c_9,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1720,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,X0)),sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_41051,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_1720])).

cnf(c_79985,plain,
    ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0),X1)
    | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0),X0)
    | ~ r1_tarski(X1,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_104772,plain,
    ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),X0)
    | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_79985])).

cnf(c_105337,plain,
    ( r1_tarski(X0,u1_struct_0(X1))
    | X0 != sK3
    | X1 != sK2 ),
    inference(resolution,[status(thm)],[c_104703,c_13])).

cnf(c_106815,plain,
    ( r1_tarski(X0,u1_struct_0(sK2))
    | X0 != sK3 ),
    inference(resolution,[status(thm)],[c_105337,c_888])).

cnf(c_7965,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X2)
    | X2 != X1
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_15858,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0)
    | m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X1)
    | X1 != X0
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_7965])).

cnf(c_35566,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(sK3))
    | X0 != k1_zfmisc_1(sK3)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_15858])).

cnf(c_127283,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(X0))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(sK3))
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,sK4)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
    inference(instantiation,[status(thm)],[c_35566])).

cnf(c_127284,plain,
    ( X0 != sK3
    | k1_zfmisc_1(X0) = k1_zfmisc_1(sK3) ),
    inference(instantiation,[status(thm)],[c_894])).

cnf(c_1444,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_1593,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1444])).

cnf(c_10756,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_136009,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != sK3
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_10756])).

cnf(c_141132,plain,
    ( ~ v2_tex_2(X0,sK2)
    | X0 != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_105351,c_18,c_15,c_905,c_907,c_1495,c_1911,c_2110,c_2124,c_2202,c_2298,c_2600,c_3401,c_4365,c_5584,c_5585,c_7691,c_25841,c_41051,c_104772,c_106815,c_127283,c_127284,c_136009])).

cnf(c_141164,plain,
    ( ~ v2_tex_2(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_141132,c_888])).

cnf(c_141165,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_141164])).

cnf(c_40671,plain,
    ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),X0)
    | ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),sK4)
    | ~ r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_127297,plain,
    ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),sK4)
    | ~ r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_40671])).

cnf(c_127298,plain,
    ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),sK4) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_127297])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_81884,plain,
    ( ~ r2_hidden(sK0(X0,sK4),k1_setfam_1(k2_enumset1(X1,X1,X1,sK4)))
    | r2_hidden(sK0(X0,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_102590,plain,
    ( ~ r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)))
    | r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_81884])).

cnf(c_102591,plain,
    ( r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4))) != iProver_top
    | r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_102590])).

cnf(c_3394,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_890])).

cnf(c_50458,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4)
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3394])).

cnf(c_50464,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4))
    | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) = iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50458])).

cnf(c_25819,plain,
    ( r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),X0),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)))
    | r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_50456,plain,
    ( r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)))
    | r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_25819])).

cnf(c_50460,plain,
    ( r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4))) = iProver_top
    | r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50456])).

cnf(c_14344,plain,
    ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),sK4)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_7691])).

cnf(c_14345,plain,
    ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4)) != iProver_top
    | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),sK4) = iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14344])).

cnf(c_2601,plain,
    ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2600])).

cnf(c_1439,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v2_tex_2(sK4,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_2395,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v2_tex_2(sK4,sK2)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1439])).

cnf(c_2396,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) = iProver_top
    | v2_tex_2(sK4,sK2) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2395])).

cnf(c_2302,plain,
    ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4)) = iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2298])).

cnf(c_2111,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2110])).

cnf(c_1496,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1495])).

cnf(c_24,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_16,negated_conjecture,
    ( v2_tex_2(sK4,sK2)
    | v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,plain,
    ( v2_tex_2(sK4,sK2) = iProver_top
    | v2_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_22,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_144287,c_141165,c_127298,c_102591,c_50464,c_50460,c_14345,c_5585,c_5584,c_2601,c_2396,c_2302,c_2124,c_2111,c_1496,c_1495,c_24,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:55:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 43.33/5.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.33/5.99  
% 43.33/5.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.33/5.99  
% 43.33/5.99  ------  iProver source info
% 43.33/5.99  
% 43.33/5.99  git: date: 2020-06-30 10:37:57 +0100
% 43.33/5.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.33/5.99  git: non_committed_changes: false
% 43.33/5.99  git: last_make_outside_of_git: false
% 43.33/5.99  
% 43.33/5.99  ------ 
% 43.33/5.99  ------ Parsing...
% 43.33/5.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.33/5.99  
% 43.33/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 43.33/5.99  
% 43.33/5.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.33/5.99  
% 43.33/5.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.33/5.99  ------ Proving...
% 43.33/5.99  ------ Problem Properties 
% 43.33/5.99  
% 43.33/5.99  
% 43.33/5.99  clauses                                 19
% 43.33/5.99  conjectures                             4
% 43.33/5.99  EPR                                     2
% 43.33/5.99  Horn                                    15
% 43.33/5.99  unary                                   5
% 43.33/5.99  binary                                  8
% 43.33/5.99  lits                                    42
% 43.33/5.99  lits eq                                 5
% 43.33/5.99  fd_pure                                 0
% 43.33/5.99  fd_pseudo                               0
% 43.33/5.99  fd_cond                                 0
% 43.33/5.99  fd_pseudo_cond                          3
% 43.33/5.99  AC symbols                              0
% 43.33/5.99  
% 43.33/5.99  ------ Input Options Time Limit: Unbounded
% 43.33/5.99  
% 43.33/5.99  
% 43.33/5.99  ------ 
% 43.33/5.99  Current options:
% 43.33/5.99  ------ 
% 43.33/5.99  
% 43.33/5.99  
% 43.33/5.99  
% 43.33/5.99  
% 43.33/5.99  ------ Proving...
% 43.33/5.99  
% 43.33/5.99  
% 43.33/5.99  % SZS status Theorem for theBenchmark.p
% 43.33/5.99  
% 43.33/5.99  % SZS output start CNFRefutation for theBenchmark.p
% 43.33/5.99  
% 43.33/5.99  fof(f1,axiom,(
% 43.33/5.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 43.33/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f12,plain,(
% 43.33/5.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 43.33/5.99    inference(ennf_transformation,[],[f1])).
% 43.33/5.99  
% 43.33/5.99  fof(f18,plain,(
% 43.33/5.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 43.33/5.99    inference(nnf_transformation,[],[f12])).
% 43.33/5.99  
% 43.33/5.99  fof(f19,plain,(
% 43.33/5.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 43.33/5.99    inference(rectify,[],[f18])).
% 43.33/5.99  
% 43.33/5.99  fof(f20,plain,(
% 43.33/5.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 43.33/5.99    introduced(choice_axiom,[])).
% 43.33/5.99  
% 43.33/5.99  fof(f21,plain,(
% 43.33/5.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 43.33/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 43.33/5.99  
% 43.33/5.99  fof(f34,plain,(
% 43.33/5.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 43.33/5.99    inference(cnf_transformation,[],[f21])).
% 43.33/5.99  
% 43.33/5.99  fof(f10,conjecture,(
% 43.33/5.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 43.33/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f11,negated_conjecture,(
% 43.33/5.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 43.33/5.99    inference(negated_conjecture,[],[f10])).
% 43.33/5.99  
% 43.33/5.99  fof(f16,plain,(
% 43.33/5.99    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 43.33/5.99    inference(ennf_transformation,[],[f11])).
% 43.33/5.99  
% 43.33/5.99  fof(f17,plain,(
% 43.33/5.99    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 43.33/5.99    inference(flattening,[],[f16])).
% 43.33/5.99  
% 43.33/5.99  fof(f30,plain,(
% 43.33/5.99    ( ! [X0,X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK4),X0) & (v2_tex_2(sK4,X0) | v2_tex_2(X1,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 43.33/5.99    introduced(choice_axiom,[])).
% 43.33/5.99  
% 43.33/5.99  fof(f29,plain,(
% 43.33/5.99    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),sK3,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(sK3,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 43.33/5.99    introduced(choice_axiom,[])).
% 43.33/5.99  
% 43.33/5.99  fof(f28,plain,(
% 43.33/5.99    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK2),X1,X2),sK2) & (v2_tex_2(X2,sK2) | v2_tex_2(X1,sK2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 43.33/5.99    introduced(choice_axiom,[])).
% 43.33/5.99  
% 43.33/5.99  fof(f31,plain,(
% 43.33/5.99    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) & (v2_tex_2(sK4,sK2) | v2_tex_2(sK3,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 43.33/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f30,f29,f28])).
% 43.33/5.99  
% 43.33/5.99  fof(f50,plain,(
% 43.33/5.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 43.33/5.99    inference(cnf_transformation,[],[f31])).
% 43.33/5.99  
% 43.33/5.99  fof(f9,axiom,(
% 43.33/5.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 43.33/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f14,plain,(
% 43.33/5.99    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.33/5.99    inference(ennf_transformation,[],[f9])).
% 43.33/5.99  
% 43.33/5.99  fof(f15,plain,(
% 43.33/5.99    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.33/5.99    inference(flattening,[],[f14])).
% 43.33/5.99  
% 43.33/5.99  fof(f48,plain,(
% 43.33/5.99    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.33/5.99    inference(cnf_transformation,[],[f15])).
% 43.33/5.99  
% 43.33/5.99  fof(f49,plain,(
% 43.33/5.99    l1_pre_topc(sK2)),
% 43.33/5.99    inference(cnf_transformation,[],[f31])).
% 43.33/5.99  
% 43.33/5.99  fof(f53,plain,(
% 43.33/5.99    ~v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)),
% 43.33/5.99    inference(cnf_transformation,[],[f31])).
% 43.33/5.99  
% 43.33/5.99  fof(f8,axiom,(
% 43.33/5.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 43.33/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f27,plain,(
% 43.33/5.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 43.33/5.99    inference(nnf_transformation,[],[f8])).
% 43.33/5.99  
% 43.33/5.99  fof(f46,plain,(
% 43.33/5.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 43.33/5.99    inference(cnf_transformation,[],[f27])).
% 43.33/5.99  
% 43.33/5.99  fof(f51,plain,(
% 43.33/5.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 43.33/5.99    inference(cnf_transformation,[],[f31])).
% 43.33/5.99  
% 43.33/5.99  fof(f47,plain,(
% 43.33/5.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 43.33/5.99    inference(cnf_transformation,[],[f27])).
% 43.33/5.99  
% 43.33/5.99  fof(f33,plain,(
% 43.33/5.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 43.33/5.99    inference(cnf_transformation,[],[f21])).
% 43.33/5.99  
% 43.33/5.99  fof(f6,axiom,(
% 43.33/5.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 43.33/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f13,plain,(
% 43.33/5.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 43.33/5.99    inference(ennf_transformation,[],[f6])).
% 43.33/5.99  
% 43.33/5.99  fof(f44,plain,(
% 43.33/5.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 43.33/5.99    inference(cnf_transformation,[],[f13])).
% 43.33/5.99  
% 43.33/5.99  fof(f7,axiom,(
% 43.33/5.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 43.33/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f45,plain,(
% 43.33/5.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 43.33/5.99    inference(cnf_transformation,[],[f7])).
% 43.33/5.99  
% 43.33/5.99  fof(f5,axiom,(
% 43.33/5.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 43.33/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f43,plain,(
% 43.33/5.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 43.33/5.99    inference(cnf_transformation,[],[f5])).
% 43.33/5.99  
% 43.33/5.99  fof(f54,plain,(
% 43.33/5.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 43.33/5.99    inference(definition_unfolding,[],[f45,f43])).
% 43.33/5.99  
% 43.33/5.99  fof(f63,plain,(
% 43.33/5.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 43.33/5.99    inference(definition_unfolding,[],[f44,f54])).
% 43.33/5.99  
% 43.33/5.99  fof(f32,plain,(
% 43.33/5.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 43.33/5.99    inference(cnf_transformation,[],[f21])).
% 43.33/5.99  
% 43.33/5.99  fof(f3,axiom,(
% 43.33/5.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 43.33/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f41,plain,(
% 43.33/5.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 43.33/5.99    inference(cnf_transformation,[],[f3])).
% 43.33/5.99  
% 43.33/5.99  fof(f61,plain,(
% 43.33/5.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 43.33/5.99    inference(definition_unfolding,[],[f41,f54])).
% 43.33/5.99  
% 43.33/5.99  fof(f2,axiom,(
% 43.33/5.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 43.33/5.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.33/5.99  
% 43.33/5.99  fof(f22,plain,(
% 43.33/5.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 43.33/5.99    inference(nnf_transformation,[],[f2])).
% 43.33/5.99  
% 43.33/5.99  fof(f23,plain,(
% 43.33/5.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 43.33/5.99    inference(flattening,[],[f22])).
% 43.33/5.99  
% 43.33/5.99  fof(f24,plain,(
% 43.33/5.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 43.33/5.99    inference(rectify,[],[f23])).
% 43.33/5.99  
% 43.33/5.99  fof(f25,plain,(
% 43.33/5.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 43.33/5.99    introduced(choice_axiom,[])).
% 43.33/5.99  
% 43.33/5.99  fof(f26,plain,(
% 43.33/5.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 43.33/5.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 43.33/5.99  
% 43.33/5.99  fof(f36,plain,(
% 43.33/5.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 43.33/5.99    inference(cnf_transformation,[],[f26])).
% 43.33/5.99  
% 43.33/5.99  fof(f59,plain,(
% 43.33/5.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 43.33/5.99    inference(definition_unfolding,[],[f36,f54])).
% 43.33/5.99  
% 43.33/5.99  fof(f65,plain,(
% 43.33/5.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 43.33/5.99    inference(equality_resolution,[],[f59])).
% 43.33/5.99  
% 43.33/5.99  fof(f52,plain,(
% 43.33/5.99    v2_tex_2(sK4,sK2) | v2_tex_2(sK3,sK2)),
% 43.33/5.99    inference(cnf_transformation,[],[f31])).
% 43.33/5.99  
% 43.33/5.99  cnf(c_0,plain,
% 43.33/5.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 43.33/5.99      inference(cnf_transformation,[],[f34]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_25818,plain,
% 43.33/5.99      ( ~ r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),X0),X0)
% 43.33/5.99      | r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),X0) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_0]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_144286,plain,
% 43.33/5.99      ( ~ r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),sK4)
% 43.33/5.99      | r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_25818]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_144287,plain,
% 43.33/5.99      ( r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),sK4) != iProver_top
% 43.33/5.99      | r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_144286]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_895,plain,
% 43.33/5.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 43.33/5.99      theory(equality) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_894,plain,
% 43.33/5.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 43.33/5.99      theory(equality) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2867,plain,
% 43.33/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.33/5.99      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 43.33/5.99      | X2 != X0
% 43.33/5.99      | X3 != X1 ),
% 43.33/5.99      inference(resolution,[status(thm)],[c_895,c_894]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_897,plain,
% 43.33/5.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 43.33/5.99      theory(equality) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_10901,plain,
% 43.33/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.33/5.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 43.33/5.99      | X2 != X0
% 43.33/5.99      | X3 != X1 ),
% 43.33/5.99      inference(resolution,[status(thm)],[c_2867,c_897]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_18,negated_conjecture,
% 43.33/5.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 43.33/5.99      inference(cnf_transformation,[],[f50]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_104703,plain,
% 43.33/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.33/5.99      | X0 != sK3
% 43.33/5.99      | X1 != sK2 ),
% 43.33/5.99      inference(resolution,[status(thm)],[c_10901,c_18]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_14,plain,
% 43.33/5.99      ( ~ v2_tex_2(X0,X1)
% 43.33/5.99      | v2_tex_2(X2,X1)
% 43.33/5.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 43.33/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.33/5.99      | ~ r1_tarski(X2,X0)
% 43.33/5.99      | ~ l1_pre_topc(X1) ),
% 43.33/5.99      inference(cnf_transformation,[],[f48]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_19,negated_conjecture,
% 43.33/5.99      ( l1_pre_topc(sK2) ),
% 43.33/5.99      inference(cnf_transformation,[],[f49]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_258,plain,
% 43.33/5.99      ( ~ v2_tex_2(X0,X1)
% 43.33/5.99      | v2_tex_2(X2,X1)
% 43.33/5.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 43.33/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.33/5.99      | ~ r1_tarski(X2,X0)
% 43.33/5.99      | sK2 != X1 ),
% 43.33/5.99      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_259,plain,
% 43.33/5.99      ( ~ v2_tex_2(X0,sK2)
% 43.33/5.99      | v2_tex_2(X1,sK2)
% 43.33/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 43.33/5.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 43.33/5.99      | ~ r1_tarski(X1,X0) ),
% 43.33/5.99      inference(unflattening,[status(thm)],[c_258]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1524,plain,
% 43.33/5.99      ( ~ v2_tex_2(X0,sK2)
% 43.33/5.99      | v2_tex_2(sK3,sK2)
% 43.33/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 43.33/5.99      | ~ r1_tarski(sK3,X0) ),
% 43.33/5.99      inference(resolution,[status(thm)],[c_259,c_18]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_105344,plain,
% 43.33/5.99      ( ~ v2_tex_2(X0,sK2)
% 43.33/5.99      | v2_tex_2(sK3,sK2)
% 43.33/5.99      | ~ r1_tarski(sK3,X0)
% 43.33/5.99      | X0 != sK3
% 43.33/5.99      | sK2 != sK2 ),
% 43.33/5.99      inference(resolution,[status(thm)],[c_104703,c_1524]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_105351,plain,
% 43.33/5.99      ( ~ v2_tex_2(X0,sK2)
% 43.33/5.99      | v2_tex_2(sK3,sK2)
% 43.33/5.99      | ~ r1_tarski(sK3,X0)
% 43.33/5.99      | X0 != sK3 ),
% 43.33/5.99      inference(equality_resolution_simp,[status(thm)],[c_105344]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_15,negated_conjecture,
% 43.33/5.99      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) ),
% 43.33/5.99      inference(cnf_transformation,[],[f53]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_905,plain,
% 43.33/5.99      ( u1_struct_0(sK2) = u1_struct_0(sK2) | sK2 != sK2 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_897]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_888,plain,( X0 = X0 ),theory(equality) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_907,plain,
% 43.33/5.99      ( sK2 = sK2 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_888]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_13,plain,
% 43.33/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 43.33/5.99      inference(cnf_transformation,[],[f46]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_17,negated_conjecture,
% 43.33/5.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 43.33/5.99      inference(cnf_transformation,[],[f51]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1495,plain,
% 43.33/5.99      ( r1_tarski(sK4,u1_struct_0(sK2)) ),
% 43.33/5.99      inference(resolution,[status(thm)],[c_13,c_17]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1911,plain,
% 43.33/5.99      ( ~ v2_tex_2(X0,sK2)
% 43.33/5.99      | v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
% 43.33/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 43.33/5.99      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 43.33/5.99      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_259]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_12,plain,
% 43.33/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.33/5.99      inference(cnf_transformation,[],[f47]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1552,plain,
% 43.33/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 43.33/5.99      | ~ r1_tarski(X0,u1_struct_0(sK2)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_12]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2110,plain,
% 43.33/5.99      ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 43.33/5.99      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_1552]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2124,plain,
% 43.33/5.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k9_subset_1(u1_struct_0(sK2),sK3,sK4) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_888]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2202,plain,
% 43.33/5.99      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 43.33/5.99      | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_894]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1,plain,
% 43.33/5.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 43.33/5.99      inference(cnf_transformation,[],[f33]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1615,plain,
% 43.33/5.99      ( r2_hidden(sK0(X0,u1_struct_0(sK2)),X0)
% 43.33/5.99      | r1_tarski(X0,u1_struct_0(sK2)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_1]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2298,plain,
% 43.33/5.99      ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
% 43.33/5.99      | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_1615]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2600,plain,
% 43.33/5.99      ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2))
% 43.33/5.99      | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_0]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_3401,plain,
% 43.33/5.99      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(X0))
% 43.33/5.99      | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_13]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_4365,plain,
% 43.33/5.99      ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(sK3))
% 43.33/5.99      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK3) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_12]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_889,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2012,plain,
% 43.33/5.99      ( X0 != X1
% 43.33/5.99      | X0 = k1_setfam_1(k2_enumset1(X2,X2,X2,X3))
% 43.33/5.99      | k1_setfam_1(k2_enumset1(X2,X2,X2,X3)) != X1 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_889]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2962,plain,
% 43.33/5.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X0
% 43.33/5.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
% 43.33/5.99      | k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) != X0 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_2012]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_3264,plain,
% 43.33/5.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,sK4)
% 43.33/5.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))
% 43.33/5.99      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) != k9_subset_1(u1_struct_0(sK2),sK3,sK4) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_2962]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_5584,plain,
% 43.33/5.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,sK4)
% 43.33/5.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4))
% 43.33/5.99      | k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)) != k9_subset_1(u1_struct_0(sK2),sK3,sK4) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_3264]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_11,plain,
% 43.33/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.33/5.99      | k1_setfam_1(k2_enumset1(X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 43.33/5.99      inference(cnf_transformation,[],[f63]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_146,plain,
% 43.33/5.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 43.33/5.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_147,plain,
% 43.33/5.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.33/5.99      inference(renaming,[status(thm)],[c_146]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_184,plain,
% 43.33/5.99      ( ~ r1_tarski(X0,X1)
% 43.33/5.99      | k1_setfam_1(k2_enumset1(X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 43.33/5.99      inference(bin_hyper_res,[status(thm)],[c_11,c_147]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_5585,plain,
% 43.33/5.99      ( ~ r1_tarski(sK4,u1_struct_0(sK2))
% 43.33/5.99      | k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)) = k9_subset_1(u1_struct_0(sK2),sK3,sK4) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_184]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2,plain,
% 43.33/5.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 43.33/5.99      inference(cnf_transformation,[],[f32]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_7691,plain,
% 43.33/5.99      ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),X0)
% 43.33/5.99      | ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
% 43.33/5.99      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_2]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_890,plain,
% 43.33/5.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 43.33/5.99      theory(equality) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_3414,plain,
% 43.33/5.99      ( ~ r1_tarski(X0,X1)
% 43.33/5.99      | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X1)
% 43.33/5.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X0 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_890]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_13886,plain,
% 43.33/5.99      ( r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0)
% 43.33/5.99      | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),X0)
% 43.33/5.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_3414]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_25841,plain,
% 43.33/5.99      ( r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK3)
% 43.33/5.99      | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK3)
% 43.33/5.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_13886]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_9,plain,
% 43.33/5.99      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
% 43.33/5.99      inference(cnf_transformation,[],[f61]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1720,plain,
% 43.33/5.99      ( r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,X0)),sK3) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_9]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_41051,plain,
% 43.33/5.99      ( r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK3) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_1720]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_79985,plain,
% 43.33/5.99      ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0),X1)
% 43.33/5.99      | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0),X0)
% 43.33/5.99      | ~ r1_tarski(X1,X0) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_2]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_104772,plain,
% 43.33/5.99      ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),X0)
% 43.33/5.99      | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2))
% 43.33/5.99      | ~ r1_tarski(X0,u1_struct_0(sK2)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_79985]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_105337,plain,
% 43.33/5.99      ( r1_tarski(X0,u1_struct_0(X1)) | X0 != sK3 | X1 != sK2 ),
% 43.33/5.99      inference(resolution,[status(thm)],[c_104703,c_13]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_106815,plain,
% 43.33/5.99      ( r1_tarski(X0,u1_struct_0(sK2)) | X0 != sK3 ),
% 43.33/5.99      inference(resolution,[status(thm)],[c_105337,c_888]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_7965,plain,
% 43.33/5.99      ( ~ m1_subset_1(X0,X1)
% 43.33/5.99      | m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X2)
% 43.33/5.99      | X2 != X1
% 43.33/5.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X0 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_895]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_15858,plain,
% 43.33/5.99      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0)
% 43.33/5.99      | m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X1)
% 43.33/5.99      | X1 != X0
% 43.33/5.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,sK4) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_7965]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_35566,plain,
% 43.33/5.99      ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),X0)
% 43.33/5.99      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(sK3))
% 43.33/5.99      | X0 != k1_zfmisc_1(sK3)
% 43.33/5.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,sK4) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_15858]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_127283,plain,
% 43.33/5.99      ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(X0))
% 43.33/5.99      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(sK3))
% 43.33/5.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,sK4)
% 43.33/5.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK3) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_35566]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_127284,plain,
% 43.33/5.99      ( X0 != sK3 | k1_zfmisc_1(X0) = k1_zfmisc_1(sK3) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_894]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1444,plain,
% 43.33/5.99      ( m1_subset_1(X0,X1)
% 43.33/5.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 43.33/5.99      | X0 != X2
% 43.33/5.99      | X1 != k1_zfmisc_1(X3) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_895]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1593,plain,
% 43.33/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.33/5.99      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 43.33/5.99      | X2 != X0
% 43.33/5.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_1444]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_10756,plain,
% 43.33/5.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 43.33/5.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 43.33/5.99      | X1 != X0
% 43.33/5.99      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_1593]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_136009,plain,
% 43.33/5.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 43.33/5.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 43.33/5.99      | X0 != sK3
% 43.33/5.99      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_10756]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_141132,plain,
% 43.33/5.99      ( ~ v2_tex_2(X0,sK2) | X0 != sK3 ),
% 43.33/5.99      inference(global_propositional_subsumption,
% 43.33/5.99                [status(thm)],
% 43.33/5.99                [c_105351,c_18,c_15,c_905,c_907,c_1495,c_1911,c_2110,
% 43.33/5.99                 c_2124,c_2202,c_2298,c_2600,c_3401,c_4365,c_5584,c_5585,
% 43.33/5.99                 c_7691,c_25841,c_41051,c_104772,c_106815,c_127283,
% 43.33/5.99                 c_127284,c_136009]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_141164,plain,
% 43.33/5.99      ( ~ v2_tex_2(sK3,sK2) ),
% 43.33/5.99      inference(resolution,[status(thm)],[c_141132,c_888]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_141165,plain,
% 43.33/5.99      ( v2_tex_2(sK3,sK2) != iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_141164]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_40671,plain,
% 43.33/5.99      ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),X0)
% 43.33/5.99      | ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),sK4)
% 43.33/5.99      | ~ r1_tarski(sK4,X0) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_2]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_127297,plain,
% 43.33/5.99      ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2))
% 43.33/5.99      | ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),sK4)
% 43.33/5.99      | ~ r1_tarski(sK4,u1_struct_0(sK2)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_40671]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_127298,plain,
% 43.33/5.99      ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top
% 43.33/5.99      | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),sK4) != iProver_top
% 43.33/5.99      | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_127297]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_7,plain,
% 43.33/5.99      ( r2_hidden(X0,X1)
% 43.33/5.99      | ~ r2_hidden(X0,k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
% 43.33/5.99      inference(cnf_transformation,[],[f65]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_81884,plain,
% 43.33/5.99      ( ~ r2_hidden(sK0(X0,sK4),k1_setfam_1(k2_enumset1(X1,X1,X1,sK4)))
% 43.33/5.99      | r2_hidden(sK0(X0,sK4),sK4) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_7]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_102590,plain,
% 43.33/5.99      ( ~ r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)))
% 43.33/5.99      | r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),sK4) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_81884]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_102591,plain,
% 43.33/5.99      ( r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4))) != iProver_top
% 43.33/5.99      | r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),sK4) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_102590]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_3394,plain,
% 43.33/5.99      ( ~ r1_tarski(X0,sK4)
% 43.33/5.99      | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4)
% 43.33/5.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X0 ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_890]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_50458,plain,
% 43.33/5.99      ( r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4)
% 43.33/5.99      | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4)
% 43.33/5.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_3394]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_50464,plain,
% 43.33/5.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4))
% 43.33/5.99      | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) = iProver_top
% 43.33/5.99      | r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4) != iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_50458]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_25819,plain,
% 43.33/5.99      ( r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),X0),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)))
% 43.33/5.99      | r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),X0) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_1]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_50456,plain,
% 43.33/5.99      ( r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)))
% 43.33/5.99      | r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_25819]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_50460,plain,
% 43.33/5.99      ( r2_hidden(sK0(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4),k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4))) = iProver_top
% 43.33/5.99      | r1_tarski(k1_setfam_1(k2_enumset1(sK3,sK3,sK3,sK4)),sK4) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_50456]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_14344,plain,
% 43.33/5.99      ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
% 43.33/5.99      | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),sK4)
% 43.33/5.99      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_7691]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_14345,plain,
% 43.33/5.99      ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4)) != iProver_top
% 43.33/5.99      | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),sK4) = iProver_top
% 43.33/5.99      | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) != iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_14344]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2601,plain,
% 43.33/5.99      ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top
% 43.33/5.99      | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_2600]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1439,plain,
% 43.33/5.99      ( v2_tex_2(X0,sK2)
% 43.33/5.99      | ~ v2_tex_2(sK4,sK2)
% 43.33/5.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 43.33/5.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 43.33/5.99      | ~ r1_tarski(X0,sK4) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_259]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2395,plain,
% 43.33/5.99      ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
% 43.33/5.99      | ~ v2_tex_2(sK4,sK2)
% 43.33/5.99      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 43.33/5.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 43.33/5.99      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) ),
% 43.33/5.99      inference(instantiation,[status(thm)],[c_1439]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2396,plain,
% 43.33/5.99      ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) = iProver_top
% 43.33/5.99      | v2_tex_2(sK4,sK2) != iProver_top
% 43.33/5.99      | m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 43.33/5.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 43.33/5.99      | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) != iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_2395]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2302,plain,
% 43.33/5.99      ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4)) = iProver_top
% 43.33/5.99      | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_2298]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_2111,plain,
% 43.33/5.99      ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 43.33/5.99      | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) != iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_2110]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_1496,plain,
% 43.33/5.99      ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_1495]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_24,plain,
% 43.33/5.99      ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) != iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_16,negated_conjecture,
% 43.33/5.99      ( v2_tex_2(sK4,sK2) | v2_tex_2(sK3,sK2) ),
% 43.33/5.99      inference(cnf_transformation,[],[f52]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_23,plain,
% 43.33/5.99      ( v2_tex_2(sK4,sK2) = iProver_top
% 43.33/5.99      | v2_tex_2(sK3,sK2) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(c_22,plain,
% 43.33/5.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 43.33/5.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 43.33/5.99  
% 43.33/5.99  cnf(contradiction,plain,
% 43.33/5.99      ( $false ),
% 43.33/5.99      inference(minisat,
% 43.33/5.99                [status(thm)],
% 43.33/5.99                [c_144287,c_141165,c_127298,c_102591,c_50464,c_50460,
% 43.33/5.99                 c_14345,c_5585,c_5584,c_2601,c_2396,c_2302,c_2124,
% 43.33/5.99                 c_2111,c_1496,c_1495,c_24,c_23,c_22]) ).
% 43.33/5.99  
% 43.33/5.99  
% 43.33/5.99  % SZS output end CNFRefutation for theBenchmark.p
% 43.33/5.99  
% 43.33/5.99  ------                               Statistics
% 43.33/5.99  
% 43.33/5.99  ------ Selected
% 43.33/5.99  
% 43.33/5.99  total_time:                             5.375
% 43.33/5.99  
%------------------------------------------------------------------------------
