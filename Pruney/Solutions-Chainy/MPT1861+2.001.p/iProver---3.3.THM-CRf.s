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
% DateTime   : Thu Dec  3 12:25:48 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :  151 (3064 expanded)
%              Number of clauses        :   97 (1184 expanded)
%              Number of leaves         :   17 ( 716 expanded)
%              Depth                    :   24
%              Number of atoms          :  435 (8211 expanded)
%              Number of equality atoms :  151 (1853 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

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
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f32,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    & ( v2_tex_2(sK4,sK2)
      | v2_tex_2(sK3,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f31,f30,f29])).

fof(f53,plain,
    ( v2_tex_2(sK4,sK2)
    | v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f19,plain,(
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

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f37,f46])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1478,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1860,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1478])).

cnf(c_17,negated_conjecture,
    ( v2_tex_2(sK4,sK2)
    | v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1473,plain,
    ( v2_tex_2(sK4,sK2) = iProver_top
    | v2_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1472,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1475,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1893,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1472,c_1475])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1477,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2423,plain,
    ( k1_setfam_1(k2_tarski(sK4,u1_struct_0(sK2))) = sK4 ),
    inference(superposition,[status(thm)],[c_1893,c_1477])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1476,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_15,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_271,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_272,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_1469,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X1,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_2260,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X1,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1476,c_1469])).

cnf(c_2787,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(X1,sK2) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1476,c_2260])).

cnf(c_4861,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2))),sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1860,c_2787])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1767,plain,
    ( ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),u1_struct_0(sK2))
    | r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1773,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1767])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1766,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK2)),X0)
    | r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1777,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK2)),X0) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1766])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4775,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK2)),X1)
    | ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),k1_setfam_1(k2_tarski(X2,X1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_11150,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_4775])).

cnf(c_11151,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK0(X0,u1_struct_0(sK2)),k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11150])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3221,plain,
    ( ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),X0)
    | r2_hidden(sK0(X0,u1_struct_0(sK2)),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4774,plain,
    ( ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),X0)
    | r2_hidden(sK0(X0,u1_struct_0(sK2)),k1_setfam_1(k2_tarski(X1,X2)))
    | ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(instantiation,[status(thm)],[c_3221])).

cnf(c_19232,plain,
    ( ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),X0)
    | r2_hidden(sK0(X0,u1_struct_0(sK2)),k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2))))
    | ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_4774])).

cnf(c_19233,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK2)),X0) != iProver_top
    | r2_hidden(sK0(X0,u1_struct_0(sK2)),k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) = iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19232])).

cnf(c_21073,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2))),sK2) != iProver_top
    | v2_tex_2(X0,sK2) = iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4861,c_1773,c_1777,c_11151,c_19233])).

cnf(c_21074,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2))),sK2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_21073])).

cnf(c_21085,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(sK4,sK2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(sK4,u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2423,c_21074])).

cnf(c_21170,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(sK4,sK2) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21085,c_2423])).

cnf(c_22554,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(sK3,sK2) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1473,c_21170])).

cnf(c_22810,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(X0,sK4)),sK2) = iProver_top
    | v2_tex_2(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1860,c_22554])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_994,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1013,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_1899,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1893])).

cnf(c_1002,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1991,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_2063,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v2_tex_2(k1_setfam_1(k2_tarski(sK3,sK4)),X0)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK3,sK4))
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1991])).

cnf(c_2065,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK3,sK4))
    | sK2 != X0
    | v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) = iProver_top
    | v2_tex_2(k1_setfam_1(k2_tarski(sK3,sK4)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2063])).

cnf(c_2067,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK3,sK4))
    | sK2 != sK2
    | v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) = iProver_top
    | v2_tex_2(k1_setfam_1(k2_tarski(sK3,sK4)),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2065])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_155,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_156,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_155])).

cnf(c_194,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_156])).

cnf(c_2064,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK2))
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k1_setfam_1(k2_tarski(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_2425,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1860,c_1477])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1471,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1894,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1471,c_1475])).

cnf(c_2424,plain,
    ( k1_setfam_1(k2_tarski(sK3,u1_struct_0(sK2))) = sK3 ),
    inference(superposition,[status(thm)],[c_1894,c_1477])).

cnf(c_1470,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_194])).

cnf(c_1862,plain,
    ( k9_subset_1(X0,X1,k1_setfam_1(k2_tarski(X0,X2))) = k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_1478,c_1470])).

cnf(c_2384,plain,
    ( k9_subset_1(X0,X1,k1_setfam_1(k2_tarski(X2,X0))) = k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_11,c_1862])).

cnf(c_3152,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)))) = k9_subset_1(u1_struct_0(sK2),X0,sK3) ),
    inference(superposition,[status(thm)],[c_2424,c_2384])).

cnf(c_2040,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_1894,c_1470])).

cnf(c_3159,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)))) = k1_setfam_1(k2_tarski(X0,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_3152,c_2040])).

cnf(c_4341,plain,
    ( k9_subset_1(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),X0,k1_setfam_1(k2_tarski(X1,sK3))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),X1)))) ),
    inference(superposition,[status(thm)],[c_3159,c_2384])).

cnf(c_1872,plain,
    ( k9_subset_1(X0,X1,k1_setfam_1(k2_tarski(X2,X0))) = k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X0)))) ),
    inference(superposition,[status(thm)],[c_1860,c_1470])).

cnf(c_3079,plain,
    ( k9_subset_1(X0,X1,k1_setfam_1(k2_tarski(X0,X2))) = k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X0)))) ),
    inference(superposition,[status(thm)],[c_11,c_1872])).

cnf(c_4343,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),X1)))) = k9_subset_1(X1,X0,k1_setfam_1(k2_tarski(X1,sK3))) ),
    inference(superposition,[status(thm)],[c_3159,c_3079])).

cnf(c_4363,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),X1)))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK3,X1)))) ),
    inference(demodulation,[status(thm)],[c_4343,c_3079])).

cnf(c_4342,plain,
    ( k9_subset_1(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),X0,k1_setfam_1(k2_tarski(X1,sK3))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)))))) ),
    inference(superposition,[status(thm)],[c_3159,c_1872])).

cnf(c_4365,plain,
    ( k9_subset_1(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),X0,k1_setfam_1(k2_tarski(X1,sK3))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,sK3)))) ),
    inference(demodulation,[status(thm)],[c_4342,c_3159])).

cnf(c_4368,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK3,X1)))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,sK3)))) ),
    inference(light_normalisation,[status(thm)],[c_4341,c_4363,c_4365])).

cnf(c_10517,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(sK3,X0)),X1)) = k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X0,sK3)))) ),
    inference(superposition,[status(thm)],[c_11,c_4368])).

cnf(c_17015,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,sK3)))) = k1_setfam_1(k2_tarski(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_2425,c_10517])).

cnf(c_22808,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(sK4,X0)),sK2) = iProver_top
    | v2_tex_2(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_22554])).

cnf(c_22846,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(sK3,sK4)),sK2) = iProver_top
    | v2_tex_2(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_17015,c_22808])).

cnf(c_23023,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22810,c_25,c_1013,c_1899,c_2067,c_2064,c_22846])).

cnf(c_10897,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)))) = k1_setfam_1(k2_tarski(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_2424,c_10517])).

cnf(c_10905,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,sK3)),X1)) = k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X0,sK3)))) ),
    inference(superposition,[status(thm)],[c_11,c_10517])).

cnf(c_12131,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),X0)) = k1_setfam_1(k2_tarski(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_10897,c_10905])).

cnf(c_21091,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(k1_setfam_1(k2_tarski(sK3,u1_struct_0(sK2))),sK2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12131,c_21074])).

cnf(c_21149,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),u1_struct_0(sK2)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21091,c_2424])).

cnf(c_21150,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(X0,k1_setfam_1(k2_tarski(sK3,u1_struct_0(sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_21149,c_12131])).

cnf(c_21151,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21150,c_2424])).

cnf(c_23028,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_23023,c_21151])).

cnf(c_23468,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(sK3,X0)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_23028])).

cnf(c_1903,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK4) = k1_setfam_1(k2_tarski(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_1893,c_1470])).

cnf(c_1474,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2136,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(sK3,sK4)),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1903,c_1474])).

cnf(c_23627,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_23468,c_2136])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:08:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 7.47/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.47/1.51  
% 7.47/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.47/1.51  
% 7.47/1.51  ------  iProver source info
% 7.47/1.51  
% 7.47/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.47/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.47/1.51  git: non_committed_changes: false
% 7.47/1.51  git: last_make_outside_of_git: false
% 7.47/1.51  
% 7.47/1.51  ------ 
% 7.47/1.51  
% 7.47/1.51  ------ Input Options
% 7.47/1.51  
% 7.47/1.51  --out_options                           all
% 7.47/1.51  --tptp_safe_out                         true
% 7.47/1.51  --problem_path                          ""
% 7.47/1.51  --include_path                          ""
% 7.47/1.51  --clausifier                            res/vclausify_rel
% 7.47/1.51  --clausifier_options                    --mode clausify
% 7.47/1.51  --stdin                                 false
% 7.47/1.51  --stats_out                             all
% 7.47/1.51  
% 7.47/1.51  ------ General Options
% 7.47/1.51  
% 7.47/1.51  --fof                                   false
% 7.47/1.51  --time_out_real                         305.
% 7.47/1.51  --time_out_virtual                      -1.
% 7.47/1.51  --symbol_type_check                     false
% 7.47/1.51  --clausify_out                          false
% 7.47/1.51  --sig_cnt_out                           false
% 7.47/1.51  --trig_cnt_out                          false
% 7.47/1.51  --trig_cnt_out_tolerance                1.
% 7.47/1.51  --trig_cnt_out_sk_spl                   false
% 7.47/1.51  --abstr_cl_out                          false
% 7.47/1.51  
% 7.47/1.51  ------ Global Options
% 7.47/1.51  
% 7.47/1.51  --schedule                              default
% 7.47/1.51  --add_important_lit                     false
% 7.47/1.51  --prop_solver_per_cl                    1000
% 7.47/1.51  --min_unsat_core                        false
% 7.47/1.51  --soft_assumptions                      false
% 7.47/1.51  --soft_lemma_size                       3
% 7.47/1.51  --prop_impl_unit_size                   0
% 7.47/1.51  --prop_impl_unit                        []
% 7.47/1.51  --share_sel_clauses                     true
% 7.47/1.51  --reset_solvers                         false
% 7.47/1.51  --bc_imp_inh                            [conj_cone]
% 7.47/1.51  --conj_cone_tolerance                   3.
% 7.47/1.51  --extra_neg_conj                        none
% 7.47/1.51  --large_theory_mode                     true
% 7.47/1.51  --prolific_symb_bound                   200
% 7.47/1.51  --lt_threshold                          2000
% 7.47/1.51  --clause_weak_htbl                      true
% 7.47/1.51  --gc_record_bc_elim                     false
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing Options
% 7.47/1.51  
% 7.47/1.51  --preprocessing_flag                    true
% 7.47/1.51  --time_out_prep_mult                    0.1
% 7.47/1.51  --splitting_mode                        input
% 7.47/1.51  --splitting_grd                         true
% 7.47/1.51  --splitting_cvd                         false
% 7.47/1.51  --splitting_cvd_svl                     false
% 7.47/1.51  --splitting_nvd                         32
% 7.47/1.51  --sub_typing                            true
% 7.47/1.51  --prep_gs_sim                           true
% 7.47/1.51  --prep_unflatten                        true
% 7.47/1.51  --prep_res_sim                          true
% 7.47/1.51  --prep_upred                            true
% 7.47/1.51  --prep_sem_filter                       exhaustive
% 7.47/1.51  --prep_sem_filter_out                   false
% 7.47/1.51  --pred_elim                             true
% 7.47/1.51  --res_sim_input                         true
% 7.47/1.51  --eq_ax_congr_red                       true
% 7.47/1.51  --pure_diseq_elim                       true
% 7.47/1.51  --brand_transform                       false
% 7.47/1.51  --non_eq_to_eq                          false
% 7.47/1.51  --prep_def_merge                        true
% 7.47/1.51  --prep_def_merge_prop_impl              false
% 7.47/1.51  --prep_def_merge_mbd                    true
% 7.47/1.51  --prep_def_merge_tr_red                 false
% 7.47/1.51  --prep_def_merge_tr_cl                  false
% 7.47/1.51  --smt_preprocessing                     true
% 7.47/1.51  --smt_ac_axioms                         fast
% 7.47/1.51  --preprocessed_out                      false
% 7.47/1.51  --preprocessed_stats                    false
% 7.47/1.51  
% 7.47/1.51  ------ Abstraction refinement Options
% 7.47/1.51  
% 7.47/1.51  --abstr_ref                             []
% 7.47/1.51  --abstr_ref_prep                        false
% 7.47/1.51  --abstr_ref_until_sat                   false
% 7.47/1.51  --abstr_ref_sig_restrict                funpre
% 7.47/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.47/1.51  --abstr_ref_under                       []
% 7.47/1.51  
% 7.47/1.51  ------ SAT Options
% 7.47/1.51  
% 7.47/1.51  --sat_mode                              false
% 7.47/1.51  --sat_fm_restart_options                ""
% 7.47/1.51  --sat_gr_def                            false
% 7.47/1.51  --sat_epr_types                         true
% 7.47/1.51  --sat_non_cyclic_types                  false
% 7.47/1.51  --sat_finite_models                     false
% 7.47/1.51  --sat_fm_lemmas                         false
% 7.47/1.51  --sat_fm_prep                           false
% 7.47/1.51  --sat_fm_uc_incr                        true
% 7.47/1.51  --sat_out_model                         small
% 7.47/1.51  --sat_out_clauses                       false
% 7.47/1.51  
% 7.47/1.51  ------ QBF Options
% 7.47/1.51  
% 7.47/1.51  --qbf_mode                              false
% 7.47/1.51  --qbf_elim_univ                         false
% 7.47/1.51  --qbf_dom_inst                          none
% 7.47/1.51  --qbf_dom_pre_inst                      false
% 7.47/1.51  --qbf_sk_in                             false
% 7.47/1.51  --qbf_pred_elim                         true
% 7.47/1.51  --qbf_split                             512
% 7.47/1.51  
% 7.47/1.51  ------ BMC1 Options
% 7.47/1.51  
% 7.47/1.51  --bmc1_incremental                      false
% 7.47/1.51  --bmc1_axioms                           reachable_all
% 7.47/1.51  --bmc1_min_bound                        0
% 7.47/1.51  --bmc1_max_bound                        -1
% 7.47/1.51  --bmc1_max_bound_default                -1
% 7.47/1.51  --bmc1_symbol_reachability              true
% 7.47/1.51  --bmc1_property_lemmas                  false
% 7.47/1.51  --bmc1_k_induction                      false
% 7.47/1.51  --bmc1_non_equiv_states                 false
% 7.47/1.51  --bmc1_deadlock                         false
% 7.47/1.51  --bmc1_ucm                              false
% 7.47/1.51  --bmc1_add_unsat_core                   none
% 7.47/1.51  --bmc1_unsat_core_children              false
% 7.47/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.47/1.51  --bmc1_out_stat                         full
% 7.47/1.51  --bmc1_ground_init                      false
% 7.47/1.51  --bmc1_pre_inst_next_state              false
% 7.47/1.51  --bmc1_pre_inst_state                   false
% 7.47/1.51  --bmc1_pre_inst_reach_state             false
% 7.47/1.51  --bmc1_out_unsat_core                   false
% 7.47/1.51  --bmc1_aig_witness_out                  false
% 7.47/1.51  --bmc1_verbose                          false
% 7.47/1.51  --bmc1_dump_clauses_tptp                false
% 7.47/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.47/1.51  --bmc1_dump_file                        -
% 7.47/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.47/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.47/1.51  --bmc1_ucm_extend_mode                  1
% 7.47/1.51  --bmc1_ucm_init_mode                    2
% 7.47/1.51  --bmc1_ucm_cone_mode                    none
% 7.47/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.47/1.51  --bmc1_ucm_relax_model                  4
% 7.47/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.47/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.47/1.51  --bmc1_ucm_layered_model                none
% 7.47/1.51  --bmc1_ucm_max_lemma_size               10
% 7.47/1.51  
% 7.47/1.51  ------ AIG Options
% 7.47/1.51  
% 7.47/1.51  --aig_mode                              false
% 7.47/1.51  
% 7.47/1.51  ------ Instantiation Options
% 7.47/1.51  
% 7.47/1.51  --instantiation_flag                    true
% 7.47/1.51  --inst_sos_flag                         false
% 7.47/1.51  --inst_sos_phase                        true
% 7.47/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.47/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.47/1.51  --inst_lit_sel_side                     num_symb
% 7.47/1.51  --inst_solver_per_active                1400
% 7.47/1.51  --inst_solver_calls_frac                1.
% 7.47/1.51  --inst_passive_queue_type               priority_queues
% 7.47/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.47/1.51  --inst_passive_queues_freq              [25;2]
% 7.47/1.51  --inst_dismatching                      true
% 7.47/1.51  --inst_eager_unprocessed_to_passive     true
% 7.47/1.51  --inst_prop_sim_given                   true
% 7.47/1.51  --inst_prop_sim_new                     false
% 7.47/1.51  --inst_subs_new                         false
% 7.47/1.51  --inst_eq_res_simp                      false
% 7.47/1.51  --inst_subs_given                       false
% 7.47/1.51  --inst_orphan_elimination               true
% 7.47/1.51  --inst_learning_loop_flag               true
% 7.47/1.51  --inst_learning_start                   3000
% 7.47/1.51  --inst_learning_factor                  2
% 7.47/1.51  --inst_start_prop_sim_after_learn       3
% 7.47/1.51  --inst_sel_renew                        solver
% 7.47/1.51  --inst_lit_activity_flag                true
% 7.47/1.51  --inst_restr_to_given                   false
% 7.47/1.51  --inst_activity_threshold               500
% 7.47/1.51  --inst_out_proof                        true
% 7.47/1.51  
% 7.47/1.51  ------ Resolution Options
% 7.47/1.51  
% 7.47/1.51  --resolution_flag                       true
% 7.47/1.51  --res_lit_sel                           adaptive
% 7.47/1.51  --res_lit_sel_side                      none
% 7.47/1.51  --res_ordering                          kbo
% 7.47/1.51  --res_to_prop_solver                    active
% 7.47/1.51  --res_prop_simpl_new                    false
% 7.47/1.51  --res_prop_simpl_given                  true
% 7.47/1.51  --res_passive_queue_type                priority_queues
% 7.47/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.47/1.51  --res_passive_queues_freq               [15;5]
% 7.47/1.51  --res_forward_subs                      full
% 7.47/1.51  --res_backward_subs                     full
% 7.47/1.51  --res_forward_subs_resolution           true
% 7.47/1.51  --res_backward_subs_resolution          true
% 7.47/1.51  --res_orphan_elimination                true
% 7.47/1.51  --res_time_limit                        2.
% 7.47/1.51  --res_out_proof                         true
% 7.47/1.51  
% 7.47/1.51  ------ Superposition Options
% 7.47/1.51  
% 7.47/1.51  --superposition_flag                    true
% 7.47/1.51  --sup_passive_queue_type                priority_queues
% 7.47/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.47/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.47/1.51  --demod_completeness_check              fast
% 7.47/1.51  --demod_use_ground                      true
% 7.47/1.51  --sup_to_prop_solver                    passive
% 7.47/1.51  --sup_prop_simpl_new                    true
% 7.47/1.51  --sup_prop_simpl_given                  true
% 7.47/1.51  --sup_fun_splitting                     false
% 7.47/1.51  --sup_smt_interval                      50000
% 7.47/1.51  
% 7.47/1.51  ------ Superposition Simplification Setup
% 7.47/1.51  
% 7.47/1.51  --sup_indices_passive                   []
% 7.47/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.47/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.51  --sup_full_bw                           [BwDemod]
% 7.47/1.51  --sup_immed_triv                        [TrivRules]
% 7.47/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.51  --sup_immed_bw_main                     []
% 7.47/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.47/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.47/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.47/1.51  
% 7.47/1.51  ------ Combination Options
% 7.47/1.51  
% 7.47/1.51  --comb_res_mult                         3
% 7.47/1.51  --comb_sup_mult                         2
% 7.47/1.51  --comb_inst_mult                        10
% 7.47/1.51  
% 7.47/1.51  ------ Debug Options
% 7.47/1.51  
% 7.47/1.51  --dbg_backtrace                         false
% 7.47/1.51  --dbg_dump_prop_clauses                 false
% 7.47/1.51  --dbg_dump_prop_clauses_file            -
% 7.47/1.51  --dbg_out_stat                          false
% 7.47/1.51  ------ Parsing...
% 7.47/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.47/1.51  ------ Proving...
% 7.47/1.51  ------ Problem Properties 
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  clauses                                 20
% 7.47/1.51  conjectures                             4
% 7.47/1.51  EPR                                     2
% 7.47/1.51  Horn                                    16
% 7.47/1.51  unary                                   5
% 7.47/1.51  binary                                  9
% 7.47/1.51  lits                                    44
% 7.47/1.51  lits eq                                 6
% 7.47/1.51  fd_pure                                 0
% 7.47/1.51  fd_pseudo                               0
% 7.47/1.51  fd_cond                                 0
% 7.47/1.51  fd_pseudo_cond                          3
% 7.47/1.51  AC symbols                              0
% 7.47/1.51  
% 7.47/1.51  ------ Schedule dynamic 5 is on 
% 7.47/1.51  
% 7.47/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  ------ 
% 7.47/1.51  Current options:
% 7.47/1.51  ------ 
% 7.47/1.51  
% 7.47/1.51  ------ Input Options
% 7.47/1.51  
% 7.47/1.51  --out_options                           all
% 7.47/1.51  --tptp_safe_out                         true
% 7.47/1.51  --problem_path                          ""
% 7.47/1.51  --include_path                          ""
% 7.47/1.51  --clausifier                            res/vclausify_rel
% 7.47/1.51  --clausifier_options                    --mode clausify
% 7.47/1.51  --stdin                                 false
% 7.47/1.51  --stats_out                             all
% 7.47/1.51  
% 7.47/1.51  ------ General Options
% 7.47/1.51  
% 7.47/1.51  --fof                                   false
% 7.47/1.51  --time_out_real                         305.
% 7.47/1.51  --time_out_virtual                      -1.
% 7.47/1.51  --symbol_type_check                     false
% 7.47/1.51  --clausify_out                          false
% 7.47/1.51  --sig_cnt_out                           false
% 7.47/1.51  --trig_cnt_out                          false
% 7.47/1.51  --trig_cnt_out_tolerance                1.
% 7.47/1.51  --trig_cnt_out_sk_spl                   false
% 7.47/1.51  --abstr_cl_out                          false
% 7.47/1.51  
% 7.47/1.51  ------ Global Options
% 7.47/1.51  
% 7.47/1.51  --schedule                              default
% 7.47/1.51  --add_important_lit                     false
% 7.47/1.51  --prop_solver_per_cl                    1000
% 7.47/1.51  --min_unsat_core                        false
% 7.47/1.51  --soft_assumptions                      false
% 7.47/1.51  --soft_lemma_size                       3
% 7.47/1.51  --prop_impl_unit_size                   0
% 7.47/1.51  --prop_impl_unit                        []
% 7.47/1.51  --share_sel_clauses                     true
% 7.47/1.51  --reset_solvers                         false
% 7.47/1.51  --bc_imp_inh                            [conj_cone]
% 7.47/1.51  --conj_cone_tolerance                   3.
% 7.47/1.51  --extra_neg_conj                        none
% 7.47/1.51  --large_theory_mode                     true
% 7.47/1.51  --prolific_symb_bound                   200
% 7.47/1.51  --lt_threshold                          2000
% 7.47/1.51  --clause_weak_htbl                      true
% 7.47/1.51  --gc_record_bc_elim                     false
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing Options
% 7.47/1.51  
% 7.47/1.51  --preprocessing_flag                    true
% 7.47/1.51  --time_out_prep_mult                    0.1
% 7.47/1.51  --splitting_mode                        input
% 7.47/1.51  --splitting_grd                         true
% 7.47/1.51  --splitting_cvd                         false
% 7.47/1.51  --splitting_cvd_svl                     false
% 7.47/1.51  --splitting_nvd                         32
% 7.47/1.51  --sub_typing                            true
% 7.47/1.51  --prep_gs_sim                           true
% 7.47/1.51  --prep_unflatten                        true
% 7.47/1.51  --prep_res_sim                          true
% 7.47/1.51  --prep_upred                            true
% 7.47/1.51  --prep_sem_filter                       exhaustive
% 7.47/1.51  --prep_sem_filter_out                   false
% 7.47/1.51  --pred_elim                             true
% 7.47/1.51  --res_sim_input                         true
% 7.47/1.51  --eq_ax_congr_red                       true
% 7.47/1.51  --pure_diseq_elim                       true
% 7.47/1.51  --brand_transform                       false
% 7.47/1.51  --non_eq_to_eq                          false
% 7.47/1.51  --prep_def_merge                        true
% 7.47/1.51  --prep_def_merge_prop_impl              false
% 7.47/1.51  --prep_def_merge_mbd                    true
% 7.47/1.51  --prep_def_merge_tr_red                 false
% 7.47/1.51  --prep_def_merge_tr_cl                  false
% 7.47/1.51  --smt_preprocessing                     true
% 7.47/1.51  --smt_ac_axioms                         fast
% 7.47/1.51  --preprocessed_out                      false
% 7.47/1.51  --preprocessed_stats                    false
% 7.47/1.51  
% 7.47/1.51  ------ Abstraction refinement Options
% 7.47/1.51  
% 7.47/1.51  --abstr_ref                             []
% 7.47/1.51  --abstr_ref_prep                        false
% 7.47/1.51  --abstr_ref_until_sat                   false
% 7.47/1.51  --abstr_ref_sig_restrict                funpre
% 7.47/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.47/1.51  --abstr_ref_under                       []
% 7.47/1.51  
% 7.47/1.51  ------ SAT Options
% 7.47/1.51  
% 7.47/1.51  --sat_mode                              false
% 7.47/1.51  --sat_fm_restart_options                ""
% 7.47/1.51  --sat_gr_def                            false
% 7.47/1.51  --sat_epr_types                         true
% 7.47/1.51  --sat_non_cyclic_types                  false
% 7.47/1.51  --sat_finite_models                     false
% 7.47/1.51  --sat_fm_lemmas                         false
% 7.47/1.51  --sat_fm_prep                           false
% 7.47/1.51  --sat_fm_uc_incr                        true
% 7.47/1.51  --sat_out_model                         small
% 7.47/1.51  --sat_out_clauses                       false
% 7.47/1.51  
% 7.47/1.51  ------ QBF Options
% 7.47/1.51  
% 7.47/1.51  --qbf_mode                              false
% 7.47/1.51  --qbf_elim_univ                         false
% 7.47/1.51  --qbf_dom_inst                          none
% 7.47/1.51  --qbf_dom_pre_inst                      false
% 7.47/1.51  --qbf_sk_in                             false
% 7.47/1.51  --qbf_pred_elim                         true
% 7.47/1.51  --qbf_split                             512
% 7.47/1.51  
% 7.47/1.51  ------ BMC1 Options
% 7.47/1.51  
% 7.47/1.51  --bmc1_incremental                      false
% 7.47/1.51  --bmc1_axioms                           reachable_all
% 7.47/1.51  --bmc1_min_bound                        0
% 7.47/1.51  --bmc1_max_bound                        -1
% 7.47/1.51  --bmc1_max_bound_default                -1
% 7.47/1.51  --bmc1_symbol_reachability              true
% 7.47/1.51  --bmc1_property_lemmas                  false
% 7.47/1.51  --bmc1_k_induction                      false
% 7.47/1.51  --bmc1_non_equiv_states                 false
% 7.47/1.51  --bmc1_deadlock                         false
% 7.47/1.51  --bmc1_ucm                              false
% 7.47/1.51  --bmc1_add_unsat_core                   none
% 7.47/1.51  --bmc1_unsat_core_children              false
% 7.47/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.47/1.51  --bmc1_out_stat                         full
% 7.47/1.51  --bmc1_ground_init                      false
% 7.47/1.51  --bmc1_pre_inst_next_state              false
% 7.47/1.51  --bmc1_pre_inst_state                   false
% 7.47/1.51  --bmc1_pre_inst_reach_state             false
% 7.47/1.51  --bmc1_out_unsat_core                   false
% 7.47/1.51  --bmc1_aig_witness_out                  false
% 7.47/1.51  --bmc1_verbose                          false
% 7.47/1.51  --bmc1_dump_clauses_tptp                false
% 7.47/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.47/1.51  --bmc1_dump_file                        -
% 7.47/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.47/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.47/1.51  --bmc1_ucm_extend_mode                  1
% 7.47/1.51  --bmc1_ucm_init_mode                    2
% 7.47/1.51  --bmc1_ucm_cone_mode                    none
% 7.47/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.47/1.51  --bmc1_ucm_relax_model                  4
% 7.47/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.47/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.47/1.51  --bmc1_ucm_layered_model                none
% 7.47/1.51  --bmc1_ucm_max_lemma_size               10
% 7.47/1.51  
% 7.47/1.51  ------ AIG Options
% 7.47/1.51  
% 7.47/1.51  --aig_mode                              false
% 7.47/1.51  
% 7.47/1.51  ------ Instantiation Options
% 7.47/1.51  
% 7.47/1.51  --instantiation_flag                    true
% 7.47/1.51  --inst_sos_flag                         false
% 7.47/1.51  --inst_sos_phase                        true
% 7.47/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.47/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.47/1.51  --inst_lit_sel_side                     none
% 7.47/1.51  --inst_solver_per_active                1400
% 7.47/1.51  --inst_solver_calls_frac                1.
% 7.47/1.51  --inst_passive_queue_type               priority_queues
% 7.47/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.47/1.51  --inst_passive_queues_freq              [25;2]
% 7.47/1.51  --inst_dismatching                      true
% 7.47/1.51  --inst_eager_unprocessed_to_passive     true
% 7.47/1.51  --inst_prop_sim_given                   true
% 7.47/1.51  --inst_prop_sim_new                     false
% 7.47/1.51  --inst_subs_new                         false
% 7.47/1.51  --inst_eq_res_simp                      false
% 7.47/1.51  --inst_subs_given                       false
% 7.47/1.51  --inst_orphan_elimination               true
% 7.47/1.51  --inst_learning_loop_flag               true
% 7.47/1.51  --inst_learning_start                   3000
% 7.47/1.51  --inst_learning_factor                  2
% 7.47/1.51  --inst_start_prop_sim_after_learn       3
% 7.47/1.51  --inst_sel_renew                        solver
% 7.47/1.51  --inst_lit_activity_flag                true
% 7.47/1.51  --inst_restr_to_given                   false
% 7.47/1.51  --inst_activity_threshold               500
% 7.47/1.51  --inst_out_proof                        true
% 7.47/1.51  
% 7.47/1.51  ------ Resolution Options
% 7.47/1.51  
% 7.47/1.51  --resolution_flag                       false
% 7.47/1.51  --res_lit_sel                           adaptive
% 7.47/1.51  --res_lit_sel_side                      none
% 7.47/1.51  --res_ordering                          kbo
% 7.47/1.51  --res_to_prop_solver                    active
% 7.47/1.51  --res_prop_simpl_new                    false
% 7.47/1.51  --res_prop_simpl_given                  true
% 7.47/1.51  --res_passive_queue_type                priority_queues
% 7.47/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.47/1.51  --res_passive_queues_freq               [15;5]
% 7.47/1.51  --res_forward_subs                      full
% 7.47/1.51  --res_backward_subs                     full
% 7.47/1.51  --res_forward_subs_resolution           true
% 7.47/1.51  --res_backward_subs_resolution          true
% 7.47/1.51  --res_orphan_elimination                true
% 7.47/1.51  --res_time_limit                        2.
% 7.47/1.51  --res_out_proof                         true
% 7.47/1.51  
% 7.47/1.51  ------ Superposition Options
% 7.47/1.51  
% 7.47/1.51  --superposition_flag                    true
% 7.47/1.51  --sup_passive_queue_type                priority_queues
% 7.47/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.47/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.47/1.51  --demod_completeness_check              fast
% 7.47/1.51  --demod_use_ground                      true
% 7.47/1.51  --sup_to_prop_solver                    passive
% 7.47/1.51  --sup_prop_simpl_new                    true
% 7.47/1.51  --sup_prop_simpl_given                  true
% 7.47/1.51  --sup_fun_splitting                     false
% 7.47/1.51  --sup_smt_interval                      50000
% 7.47/1.51  
% 7.47/1.51  ------ Superposition Simplification Setup
% 7.47/1.51  
% 7.47/1.51  --sup_indices_passive                   []
% 7.47/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.47/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.51  --sup_full_bw                           [BwDemod]
% 7.47/1.51  --sup_immed_triv                        [TrivRules]
% 7.47/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.52  --sup_immed_bw_main                     []
% 7.47/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.47/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.47/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.47/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.47/1.52  
% 7.47/1.52  ------ Combination Options
% 7.47/1.52  
% 7.47/1.52  --comb_res_mult                         3
% 7.47/1.52  --comb_sup_mult                         2
% 7.47/1.52  --comb_inst_mult                        10
% 7.47/1.52  
% 7.47/1.52  ------ Debug Options
% 7.47/1.52  
% 7.47/1.52  --dbg_backtrace                         false
% 7.47/1.52  --dbg_dump_prop_clauses                 false
% 7.47/1.52  --dbg_dump_prop_clauses_file            -
% 7.47/1.52  --dbg_out_stat                          false
% 7.47/1.52  
% 7.47/1.52  
% 7.47/1.52  
% 7.47/1.52  
% 7.47/1.52  ------ Proving...
% 7.47/1.52  
% 7.47/1.52  
% 7.47/1.52  % SZS status Theorem for theBenchmark.p
% 7.47/1.52  
% 7.47/1.52   Resolution empty clause
% 7.47/1.52  
% 7.47/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.47/1.52  
% 7.47/1.52  fof(f3,axiom,(
% 7.47/1.52    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.47/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.52  
% 7.47/1.52  fof(f42,plain,(
% 7.47/1.52    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.47/1.52    inference(cnf_transformation,[],[f3])).
% 7.47/1.52  
% 7.47/1.52  fof(f7,axiom,(
% 7.47/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.47/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.52  
% 7.47/1.52  fof(f46,plain,(
% 7.47/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.47/1.52    inference(cnf_transformation,[],[f7])).
% 7.47/1.52  
% 7.47/1.52  fof(f61,plain,(
% 7.47/1.52    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 7.47/1.52    inference(definition_unfolding,[],[f42,f46])).
% 7.47/1.52  
% 7.47/1.52  fof(f5,axiom,(
% 7.47/1.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.47/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.52  
% 7.47/1.52  fof(f44,plain,(
% 7.47/1.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.47/1.52    inference(cnf_transformation,[],[f5])).
% 7.47/1.52  
% 7.47/1.52  fof(f10,conjecture,(
% 7.47/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.47/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.52  
% 7.47/1.52  fof(f11,negated_conjecture,(
% 7.47/1.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.47/1.52    inference(negated_conjecture,[],[f10])).
% 7.47/1.52  
% 7.47/1.52  fof(f17,plain,(
% 7.47/1.52    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.47/1.52    inference(ennf_transformation,[],[f11])).
% 7.47/1.52  
% 7.47/1.52  fof(f18,plain,(
% 7.47/1.52    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.47/1.52    inference(flattening,[],[f17])).
% 7.47/1.52  
% 7.47/1.52  fof(f31,plain,(
% 7.47/1.52    ( ! [X0,X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK4),X0) & (v2_tex_2(sK4,X0) | v2_tex_2(X1,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.47/1.52    introduced(choice_axiom,[])).
% 7.47/1.52  
% 7.47/1.52  fof(f30,plain,(
% 7.47/1.52    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),sK3,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(sK3,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.47/1.52    introduced(choice_axiom,[])).
% 7.47/1.52  
% 7.47/1.52  fof(f29,plain,(
% 7.47/1.52    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK2),X1,X2),sK2) & (v2_tex_2(X2,sK2) | v2_tex_2(X1,sK2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 7.47/1.52    introduced(choice_axiom,[])).
% 7.47/1.52  
% 7.47/1.52  fof(f32,plain,(
% 7.47/1.52    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) & (v2_tex_2(sK4,sK2) | v2_tex_2(sK3,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 7.47/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f31,f30,f29])).
% 7.47/1.52  
% 7.47/1.52  fof(f53,plain,(
% 7.47/1.52    v2_tex_2(sK4,sK2) | v2_tex_2(sK3,sK2)),
% 7.47/1.52    inference(cnf_transformation,[],[f32])).
% 7.47/1.52  
% 7.47/1.52  fof(f52,plain,(
% 7.47/1.52    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 7.47/1.52    inference(cnf_transformation,[],[f32])).
% 7.47/1.52  
% 7.47/1.52  fof(f8,axiom,(
% 7.47/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.47/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.52  
% 7.47/1.52  fof(f28,plain,(
% 7.47/1.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.47/1.52    inference(nnf_transformation,[],[f8])).
% 7.47/1.52  
% 7.47/1.52  fof(f47,plain,(
% 7.47/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.47/1.52    inference(cnf_transformation,[],[f28])).
% 7.47/1.52  
% 7.47/1.52  fof(f4,axiom,(
% 7.47/1.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.47/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.52  
% 7.47/1.52  fof(f13,plain,(
% 7.47/1.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.47/1.52    inference(ennf_transformation,[],[f4])).
% 7.47/1.52  
% 7.47/1.52  fof(f43,plain,(
% 7.47/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.47/1.52    inference(cnf_transformation,[],[f13])).
% 7.47/1.52  
% 7.47/1.52  fof(f62,plain,(
% 7.47/1.52    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.47/1.52    inference(definition_unfolding,[],[f43,f46])).
% 7.47/1.52  
% 7.47/1.52  fof(f48,plain,(
% 7.47/1.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.47/1.52    inference(cnf_transformation,[],[f28])).
% 7.47/1.52  
% 7.47/1.52  fof(f9,axiom,(
% 7.47/1.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 7.47/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.52  
% 7.47/1.52  fof(f15,plain,(
% 7.47/1.52    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.47/1.52    inference(ennf_transformation,[],[f9])).
% 7.47/1.52  
% 7.47/1.52  fof(f16,plain,(
% 7.47/1.52    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.47/1.52    inference(flattening,[],[f15])).
% 7.47/1.52  
% 7.47/1.52  fof(f49,plain,(
% 7.47/1.52    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.47/1.52    inference(cnf_transformation,[],[f16])).
% 7.47/1.52  
% 7.47/1.52  fof(f50,plain,(
% 7.47/1.52    l1_pre_topc(sK2)),
% 7.47/1.52    inference(cnf_transformation,[],[f32])).
% 7.47/1.52  
% 7.47/1.52  fof(f1,axiom,(
% 7.47/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.47/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.52  
% 7.47/1.52  fof(f12,plain,(
% 7.47/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.47/1.52    inference(ennf_transformation,[],[f1])).
% 7.47/1.52  
% 7.47/1.52  fof(f19,plain,(
% 7.47/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.47/1.52    inference(nnf_transformation,[],[f12])).
% 7.47/1.52  
% 7.47/1.52  fof(f20,plain,(
% 7.47/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.47/1.52    inference(rectify,[],[f19])).
% 7.47/1.52  
% 7.47/1.52  fof(f21,plain,(
% 7.47/1.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.47/1.52    introduced(choice_axiom,[])).
% 7.47/1.52  
% 7.47/1.52  fof(f22,plain,(
% 7.47/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.47/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 7.47/1.52  
% 7.47/1.52  fof(f35,plain,(
% 7.47/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.47/1.52    inference(cnf_transformation,[],[f22])).
% 7.47/1.52  
% 7.47/1.52  fof(f34,plain,(
% 7.47/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.47/1.52    inference(cnf_transformation,[],[f22])).
% 7.47/1.52  
% 7.47/1.52  fof(f2,axiom,(
% 7.47/1.52    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.47/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.52  
% 7.47/1.52  fof(f23,plain,(
% 7.47/1.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.47/1.52    inference(nnf_transformation,[],[f2])).
% 7.47/1.52  
% 7.47/1.52  fof(f24,plain,(
% 7.47/1.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.47/1.52    inference(flattening,[],[f23])).
% 7.47/1.52  
% 7.47/1.52  fof(f25,plain,(
% 7.47/1.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.47/1.52    inference(rectify,[],[f24])).
% 7.47/1.52  
% 7.47/1.52  fof(f26,plain,(
% 7.47/1.52    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.47/1.52    introduced(choice_axiom,[])).
% 7.47/1.52  
% 7.47/1.52  fof(f27,plain,(
% 7.47/1.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 7.47/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 7.47/1.52  
% 7.47/1.52  fof(f37,plain,(
% 7.47/1.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 7.47/1.52    inference(cnf_transformation,[],[f27])).
% 7.47/1.52  
% 7.47/1.52  fof(f59,plain,(
% 7.47/1.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 7.47/1.52    inference(definition_unfolding,[],[f37,f46])).
% 7.47/1.52  
% 7.47/1.52  fof(f65,plain,(
% 7.47/1.52    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 7.47/1.52    inference(equality_resolution,[],[f59])).
% 7.47/1.52  
% 7.47/1.52  fof(f33,plain,(
% 7.47/1.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.47/1.52    inference(cnf_transformation,[],[f22])).
% 7.47/1.52  
% 7.47/1.52  fof(f54,plain,(
% 7.47/1.52    ~v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)),
% 7.47/1.52    inference(cnf_transformation,[],[f32])).
% 7.47/1.52  
% 7.47/1.52  fof(f6,axiom,(
% 7.47/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.47/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.52  
% 7.47/1.52  fof(f14,plain,(
% 7.47/1.52    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.47/1.52    inference(ennf_transformation,[],[f6])).
% 7.47/1.52  
% 7.47/1.52  fof(f45,plain,(
% 7.47/1.52    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.47/1.52    inference(cnf_transformation,[],[f14])).
% 7.47/1.52  
% 7.47/1.52  fof(f63,plain,(
% 7.47/1.52    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.47/1.52    inference(definition_unfolding,[],[f45,f46])).
% 7.47/1.52  
% 7.47/1.52  fof(f51,plain,(
% 7.47/1.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 7.47/1.52    inference(cnf_transformation,[],[f32])).
% 7.47/1.52  
% 7.47/1.52  cnf(c_9,plain,
% 7.47/1.52      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 7.47/1.52      inference(cnf_transformation,[],[f61]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1478,plain,
% 7.47/1.52      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_11,plain,
% 7.47/1.52      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 7.47/1.52      inference(cnf_transformation,[],[f44]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1860,plain,
% 7.47/1.52      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_11,c_1478]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_17,negated_conjecture,
% 7.47/1.52      ( v2_tex_2(sK4,sK2) | v2_tex_2(sK3,sK2) ),
% 7.47/1.52      inference(cnf_transformation,[],[f53]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1473,plain,
% 7.47/1.52      ( v2_tex_2(sK4,sK2) = iProver_top | v2_tex_2(sK3,sK2) = iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_18,negated_conjecture,
% 7.47/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.47/1.52      inference(cnf_transformation,[],[f52]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1472,plain,
% 7.47/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_14,plain,
% 7.47/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.47/1.52      inference(cnf_transformation,[],[f47]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1475,plain,
% 7.47/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.47/1.52      | r1_tarski(X0,X1) = iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1893,plain,
% 7.47/1.52      ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1472,c_1475]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_10,plain,
% 7.47/1.52      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 7.47/1.52      inference(cnf_transformation,[],[f62]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1477,plain,
% 7.47/1.52      ( k1_setfam_1(k2_tarski(X0,X1)) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_2423,plain,
% 7.47/1.52      ( k1_setfam_1(k2_tarski(sK4,u1_struct_0(sK2))) = sK4 ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1893,c_1477]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_13,plain,
% 7.47/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.47/1.52      inference(cnf_transformation,[],[f48]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1476,plain,
% 7.47/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.47/1.52      | r1_tarski(X0,X1) != iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_15,plain,
% 7.47/1.52      ( ~ v2_tex_2(X0,X1)
% 7.47/1.52      | v2_tex_2(X2,X1)
% 7.47/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.47/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.47/1.52      | ~ r1_tarski(X2,X0)
% 7.47/1.52      | ~ l1_pre_topc(X1) ),
% 7.47/1.52      inference(cnf_transformation,[],[f49]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_20,negated_conjecture,
% 7.47/1.52      ( l1_pre_topc(sK2) ),
% 7.47/1.52      inference(cnf_transformation,[],[f50]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_271,plain,
% 7.47/1.52      ( ~ v2_tex_2(X0,X1)
% 7.47/1.52      | v2_tex_2(X2,X1)
% 7.47/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.47/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.47/1.52      | ~ r1_tarski(X2,X0)
% 7.47/1.52      | sK2 != X1 ),
% 7.47/1.52      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_272,plain,
% 7.47/1.52      ( ~ v2_tex_2(X0,sK2)
% 7.47/1.52      | v2_tex_2(X1,sK2)
% 7.47/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.47/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.47/1.52      | ~ r1_tarski(X1,X0) ),
% 7.47/1.52      inference(unflattening,[status(thm)],[c_271]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1469,plain,
% 7.47/1.52      ( v2_tex_2(X0,sK2) != iProver_top
% 7.47/1.52      | v2_tex_2(X1,sK2) = iProver_top
% 7.47/1.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.47/1.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.47/1.52      | r1_tarski(X1,X0) != iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_2260,plain,
% 7.47/1.52      ( v2_tex_2(X0,sK2) != iProver_top
% 7.47/1.52      | v2_tex_2(X1,sK2) = iProver_top
% 7.47/1.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.47/1.52      | r1_tarski(X1,X0) != iProver_top
% 7.47/1.52      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1476,c_1469]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_2787,plain,
% 7.47/1.52      ( v2_tex_2(X0,sK2) != iProver_top
% 7.47/1.52      | v2_tex_2(X1,sK2) = iProver_top
% 7.47/1.52      | r1_tarski(X1,X0) != iProver_top
% 7.47/1.52      | r1_tarski(X1,u1_struct_0(sK2)) != iProver_top
% 7.47/1.52      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1476,c_2260]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_4861,plain,
% 7.47/1.52      ( v2_tex_2(X0,sK2) = iProver_top
% 7.47/1.52      | v2_tex_2(k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2))),sK2) != iProver_top
% 7.47/1.52      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 7.47/1.52      | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) != iProver_top ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1860,c_2787]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_0,plain,
% 7.47/1.52      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.47/1.52      inference(cnf_transformation,[],[f35]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1767,plain,
% 7.47/1.52      ( ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),u1_struct_0(sK2))
% 7.47/1.52      | r1_tarski(X0,u1_struct_0(sK2)) ),
% 7.47/1.52      inference(instantiation,[status(thm)],[c_0]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1773,plain,
% 7.47/1.52      ( r2_hidden(sK0(X0,u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top
% 7.47/1.52      | r1_tarski(X0,u1_struct_0(sK2)) = iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_1767]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1,plain,
% 7.47/1.52      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.47/1.52      inference(cnf_transformation,[],[f34]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1766,plain,
% 7.47/1.52      ( r2_hidden(sK0(X0,u1_struct_0(sK2)),X0)
% 7.47/1.52      | r1_tarski(X0,u1_struct_0(sK2)) ),
% 7.47/1.52      inference(instantiation,[status(thm)],[c_1]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1777,plain,
% 7.47/1.52      ( r2_hidden(sK0(X0,u1_struct_0(sK2)),X0) = iProver_top
% 7.47/1.52      | r1_tarski(X0,u1_struct_0(sK2)) = iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_1766]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_7,plain,
% 7.47/1.52      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X2,X1))) ),
% 7.47/1.52      inference(cnf_transformation,[],[f65]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_4775,plain,
% 7.47/1.52      ( r2_hidden(sK0(X0,u1_struct_0(sK2)),X1)
% 7.47/1.52      | ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),k1_setfam_1(k2_tarski(X2,X1))) ),
% 7.47/1.52      inference(instantiation,[status(thm)],[c_7]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_11150,plain,
% 7.47/1.52      ( r2_hidden(sK0(X0,u1_struct_0(sK2)),u1_struct_0(sK2))
% 7.47/1.52      | ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) ),
% 7.47/1.52      inference(instantiation,[status(thm)],[c_4775]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_11151,plain,
% 7.47/1.52      ( r2_hidden(sK0(X0,u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top
% 7.47/1.52      | r2_hidden(sK0(X0,u1_struct_0(sK2)),k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) != iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_11150]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_2,plain,
% 7.47/1.52      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.47/1.52      inference(cnf_transformation,[],[f33]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_3221,plain,
% 7.47/1.52      ( ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),X0)
% 7.47/1.52      | r2_hidden(sK0(X0,u1_struct_0(sK2)),X1)
% 7.47/1.52      | ~ r1_tarski(X0,X1) ),
% 7.47/1.52      inference(instantiation,[status(thm)],[c_2]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_4774,plain,
% 7.47/1.52      ( ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),X0)
% 7.47/1.52      | r2_hidden(sK0(X0,u1_struct_0(sK2)),k1_setfam_1(k2_tarski(X1,X2)))
% 7.47/1.52      | ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 7.47/1.52      inference(instantiation,[status(thm)],[c_3221]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_19232,plain,
% 7.47/1.52      ( ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),X0)
% 7.47/1.52      | r2_hidden(sK0(X0,u1_struct_0(sK2)),k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2))))
% 7.47/1.52      | ~ r1_tarski(X0,k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) ),
% 7.47/1.52      inference(instantiation,[status(thm)],[c_4774]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_19233,plain,
% 7.47/1.52      ( r2_hidden(sK0(X0,u1_struct_0(sK2)),X0) != iProver_top
% 7.47/1.52      | r2_hidden(sK0(X0,u1_struct_0(sK2)),k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) = iProver_top
% 7.47/1.52      | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) != iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_19232]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_21073,plain,
% 7.47/1.52      ( v2_tex_2(k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2))),sK2) != iProver_top
% 7.47/1.52      | v2_tex_2(X0,sK2) = iProver_top
% 7.47/1.52      | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) != iProver_top ),
% 7.47/1.52      inference(global_propositional_subsumption,
% 7.47/1.52                [status(thm)],
% 7.47/1.52                [c_4861,c_1773,c_1777,c_11151,c_19233]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_21074,plain,
% 7.47/1.52      ( v2_tex_2(X0,sK2) = iProver_top
% 7.47/1.52      | v2_tex_2(k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2))),sK2) != iProver_top
% 7.47/1.52      | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,u1_struct_0(sK2)))) != iProver_top ),
% 7.47/1.52      inference(renaming,[status(thm)],[c_21073]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_21085,plain,
% 7.47/1.52      ( v2_tex_2(X0,sK2) = iProver_top
% 7.47/1.52      | v2_tex_2(sK4,sK2) != iProver_top
% 7.47/1.52      | r1_tarski(X0,k1_setfam_1(k2_tarski(sK4,u1_struct_0(sK2)))) != iProver_top ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_2423,c_21074]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_21170,plain,
% 7.47/1.52      ( v2_tex_2(X0,sK2) = iProver_top
% 7.47/1.52      | v2_tex_2(sK4,sK2) != iProver_top
% 7.47/1.52      | r1_tarski(X0,sK4) != iProver_top ),
% 7.47/1.52      inference(light_normalisation,[status(thm)],[c_21085,c_2423]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_22554,plain,
% 7.47/1.52      ( v2_tex_2(X0,sK2) = iProver_top
% 7.47/1.52      | v2_tex_2(sK3,sK2) = iProver_top
% 7.47/1.52      | r1_tarski(X0,sK4) != iProver_top ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1473,c_21170]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_22810,plain,
% 7.47/1.52      ( v2_tex_2(k1_setfam_1(k2_tarski(X0,sK4)),sK2) = iProver_top
% 7.47/1.52      | v2_tex_2(sK3,sK2) = iProver_top ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1860,c_22554]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_16,negated_conjecture,
% 7.47/1.52      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) ),
% 7.47/1.52      inference(cnf_transformation,[],[f54]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_25,plain,
% 7.47/1.52      ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) != iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_994,plain,( X0 = X0 ),theory(equality) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1013,plain,
% 7.47/1.52      ( sK2 = sK2 ),
% 7.47/1.52      inference(instantiation,[status(thm)],[c_994]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1899,plain,
% 7.47/1.52      ( r1_tarski(sK4,u1_struct_0(sK2)) ),
% 7.47/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_1893]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1002,plain,
% 7.47/1.52      ( ~ v2_tex_2(X0,X1) | v2_tex_2(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.47/1.52      theory(equality) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1991,plain,
% 7.47/1.52      ( ~ v2_tex_2(X0,X1)
% 7.47/1.52      | v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
% 7.47/1.52      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X0
% 7.47/1.52      | sK2 != X1 ),
% 7.47/1.52      inference(instantiation,[status(thm)],[c_1002]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_2063,plain,
% 7.47/1.52      ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
% 7.47/1.52      | ~ v2_tex_2(k1_setfam_1(k2_tarski(sK3,sK4)),X0)
% 7.47/1.52      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK3,sK4))
% 7.47/1.52      | sK2 != X0 ),
% 7.47/1.52      inference(instantiation,[status(thm)],[c_1991]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_2065,plain,
% 7.47/1.52      ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK3,sK4))
% 7.47/1.52      | sK2 != X0
% 7.47/1.52      | v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) = iProver_top
% 7.47/1.52      | v2_tex_2(k1_setfam_1(k2_tarski(sK3,sK4)),X0) != iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_2063]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_2067,plain,
% 7.47/1.52      ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK3,sK4))
% 7.47/1.52      | sK2 != sK2
% 7.47/1.52      | v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) = iProver_top
% 7.47/1.52      | v2_tex_2(k1_setfam_1(k2_tarski(sK3,sK4)),sK2) != iProver_top ),
% 7.47/1.52      inference(instantiation,[status(thm)],[c_2065]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_12,plain,
% 7.47/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.47/1.52      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.47/1.52      inference(cnf_transformation,[],[f63]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_155,plain,
% 7.47/1.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.47/1.52      inference(prop_impl,[status(thm)],[c_13]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_156,plain,
% 7.47/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.47/1.52      inference(renaming,[status(thm)],[c_155]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_194,plain,
% 7.47/1.52      ( ~ r1_tarski(X0,X1)
% 7.47/1.52      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.47/1.52      inference(bin_hyper_res,[status(thm)],[c_12,c_156]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_2064,plain,
% 7.47/1.52      ( ~ r1_tarski(sK4,u1_struct_0(sK2))
% 7.47/1.52      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k1_setfam_1(k2_tarski(sK3,sK4)) ),
% 7.47/1.52      inference(instantiation,[status(thm)],[c_194]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_2425,plain,
% 7.47/1.52      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1860,c_1477]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_19,negated_conjecture,
% 7.47/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.47/1.52      inference(cnf_transformation,[],[f51]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1471,plain,
% 7.47/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1894,plain,
% 7.47/1.52      ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1471,c_1475]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_2424,plain,
% 7.47/1.52      ( k1_setfam_1(k2_tarski(sK3,u1_struct_0(sK2))) = sK3 ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1894,c_1477]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1470,plain,
% 7.47/1.52      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 7.47/1.52      | r1_tarski(X2,X0) != iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_194]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1862,plain,
% 7.47/1.52      ( k9_subset_1(X0,X1,k1_setfam_1(k2_tarski(X0,X2))) = k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X0,X2)))) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1478,c_1470]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_2384,plain,
% 7.47/1.52      ( k9_subset_1(X0,X1,k1_setfam_1(k2_tarski(X2,X0))) = k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X0,X2)))) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_11,c_1862]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_3152,plain,
% 7.47/1.52      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)))) = k9_subset_1(u1_struct_0(sK2),X0,sK3) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_2424,c_2384]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_2040,plain,
% 7.47/1.52      ( k9_subset_1(u1_struct_0(sK2),X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3)) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1894,c_1470]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_3159,plain,
% 7.47/1.52      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)))) = k1_setfam_1(k2_tarski(X0,sK3)) ),
% 7.47/1.52      inference(light_normalisation,[status(thm)],[c_3152,c_2040]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_4341,plain,
% 7.47/1.52      ( k9_subset_1(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),X0,k1_setfam_1(k2_tarski(X1,sK3))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),X1)))) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_3159,c_2384]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1872,plain,
% 7.47/1.52      ( k9_subset_1(X0,X1,k1_setfam_1(k2_tarski(X2,X0))) = k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X0)))) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1860,c_1470]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_3079,plain,
% 7.47/1.52      ( k9_subset_1(X0,X1,k1_setfam_1(k2_tarski(X0,X2))) = k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X2,X0)))) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_11,c_1872]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_4343,plain,
% 7.47/1.52      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),X1)))) = k9_subset_1(X1,X0,k1_setfam_1(k2_tarski(X1,sK3))) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_3159,c_3079]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_4363,plain,
% 7.47/1.52      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),X1)))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK3,X1)))) ),
% 7.47/1.52      inference(demodulation,[status(thm)],[c_4343,c_3079]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_4342,plain,
% 7.47/1.52      ( k9_subset_1(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),X0,k1_setfam_1(k2_tarski(X1,sK3))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)))))) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_3159,c_1872]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_4365,plain,
% 7.47/1.52      ( k9_subset_1(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),X0,k1_setfam_1(k2_tarski(X1,sK3))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,sK3)))) ),
% 7.47/1.52      inference(demodulation,[status(thm)],[c_4342,c_3159]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_4368,plain,
% 7.47/1.52      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(sK3,X1)))) = k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,sK3)))) ),
% 7.47/1.52      inference(light_normalisation,[status(thm)],[c_4341,c_4363,c_4365]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_10517,plain,
% 7.47/1.52      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(sK3,X0)),X1)) = k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X0,sK3)))) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_11,c_4368]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_17015,plain,
% 7.47/1.52      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,sK3)))) = k1_setfam_1(k2_tarski(sK3,X0)) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_2425,c_10517]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_22808,plain,
% 7.47/1.52      ( v2_tex_2(k1_setfam_1(k2_tarski(sK4,X0)),sK2) = iProver_top
% 7.47/1.52      | v2_tex_2(sK3,sK2) = iProver_top ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1478,c_22554]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_22846,plain,
% 7.47/1.52      ( v2_tex_2(k1_setfam_1(k2_tarski(sK3,sK4)),sK2) = iProver_top
% 7.47/1.52      | v2_tex_2(sK3,sK2) = iProver_top ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_17015,c_22808]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_23023,plain,
% 7.47/1.52      ( v2_tex_2(sK3,sK2) = iProver_top ),
% 7.47/1.52      inference(global_propositional_subsumption,
% 7.47/1.52                [status(thm)],
% 7.47/1.52                [c_22810,c_25,c_1013,c_1899,c_2067,c_2064,c_22846]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_10897,plain,
% 7.47/1.52      ( k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)))) = k1_setfam_1(k2_tarski(sK3,X0)) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_2424,c_10517]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_10905,plain,
% 7.47/1.52      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,sK3)),X1)) = k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X0,sK3)))) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_11,c_10517]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_12131,plain,
% 7.47/1.52      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),X0)) = k1_setfam_1(k2_tarski(sK3,X0)) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_10897,c_10905]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_21091,plain,
% 7.47/1.52      ( v2_tex_2(X0,sK2) = iProver_top
% 7.47/1.52      | v2_tex_2(k1_setfam_1(k2_tarski(sK3,u1_struct_0(sK2))),sK2) != iProver_top
% 7.47/1.52      | r1_tarski(X0,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),u1_struct_0(sK2)))) != iProver_top ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_12131,c_21074]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_21149,plain,
% 7.47/1.52      ( v2_tex_2(X0,sK2) = iProver_top
% 7.47/1.52      | v2_tex_2(sK3,sK2) != iProver_top
% 7.47/1.52      | r1_tarski(X0,k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(u1_struct_0(sK2),sK3)),u1_struct_0(sK2)))) != iProver_top ),
% 7.47/1.52      inference(light_normalisation,[status(thm)],[c_21091,c_2424]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_21150,plain,
% 7.47/1.52      ( v2_tex_2(X0,sK2) = iProver_top
% 7.47/1.52      | v2_tex_2(sK3,sK2) != iProver_top
% 7.47/1.52      | r1_tarski(X0,k1_setfam_1(k2_tarski(sK3,u1_struct_0(sK2)))) != iProver_top ),
% 7.47/1.52      inference(demodulation,[status(thm)],[c_21149,c_12131]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_21151,plain,
% 7.47/1.52      ( v2_tex_2(X0,sK2) = iProver_top
% 7.47/1.52      | v2_tex_2(sK3,sK2) != iProver_top
% 7.47/1.52      | r1_tarski(X0,sK3) != iProver_top ),
% 7.47/1.52      inference(light_normalisation,[status(thm)],[c_21150,c_2424]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_23028,plain,
% 7.47/1.52      ( v2_tex_2(X0,sK2) = iProver_top | r1_tarski(X0,sK3) != iProver_top ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_23023,c_21151]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_23468,plain,
% 7.47/1.52      ( v2_tex_2(k1_setfam_1(k2_tarski(sK3,X0)),sK2) = iProver_top ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1478,c_23028]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1903,plain,
% 7.47/1.52      ( k9_subset_1(u1_struct_0(sK2),X0,sK4) = k1_setfam_1(k2_tarski(X0,sK4)) ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_1893,c_1470]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_1474,plain,
% 7.47/1.52      ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) != iProver_top ),
% 7.47/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_2136,plain,
% 7.47/1.52      ( v2_tex_2(k1_setfam_1(k2_tarski(sK3,sK4)),sK2) != iProver_top ),
% 7.47/1.52      inference(demodulation,[status(thm)],[c_1903,c_1474]) ).
% 7.47/1.52  
% 7.47/1.52  cnf(c_23627,plain,
% 7.47/1.52      ( $false ),
% 7.47/1.52      inference(superposition,[status(thm)],[c_23468,c_2136]) ).
% 7.47/1.52  
% 7.47/1.52  
% 7.47/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.47/1.52  
% 7.47/1.52  ------                               Statistics
% 7.47/1.52  
% 7.47/1.52  ------ General
% 7.47/1.52  
% 7.47/1.52  abstr_ref_over_cycles:                  0
% 7.47/1.52  abstr_ref_under_cycles:                 0
% 7.47/1.52  gc_basic_clause_elim:                   0
% 7.47/1.52  forced_gc_time:                         0
% 7.47/1.52  parsing_time:                           0.004
% 7.47/1.52  unif_index_cands_time:                  0.
% 7.47/1.52  unif_index_add_time:                    0.
% 7.47/1.52  orderings_time:                         0.
% 7.47/1.52  out_proof_time:                         0.011
% 7.47/1.52  total_time:                             0.515
% 7.47/1.52  num_of_symbols:                         46
% 7.47/1.52  num_of_terms:                           19759
% 7.47/1.52  
% 7.47/1.52  ------ Preprocessing
% 7.47/1.52  
% 7.47/1.52  num_of_splits:                          0
% 7.47/1.52  num_of_split_atoms:                     0
% 7.47/1.52  num_of_reused_defs:                     0
% 7.47/1.52  num_eq_ax_congr_red:                    24
% 7.47/1.52  num_of_sem_filtered_clauses:            1
% 7.47/1.52  num_of_subtypes:                        0
% 7.47/1.52  monotx_restored_types:                  0
% 7.47/1.52  sat_num_of_epr_types:                   0
% 7.47/1.52  sat_num_of_non_cyclic_types:            0
% 7.47/1.52  sat_guarded_non_collapsed_types:        0
% 7.47/1.52  num_pure_diseq_elim:                    0
% 7.47/1.52  simp_replaced_by:                       0
% 7.47/1.52  res_preprocessed:                       102
% 7.47/1.52  prep_upred:                             0
% 7.47/1.52  prep_unflattend:                        45
% 7.47/1.52  smt_new_axioms:                         0
% 7.47/1.52  pred_elim_cands:                        4
% 7.47/1.52  pred_elim:                              1
% 7.47/1.52  pred_elim_cl:                           1
% 7.47/1.52  pred_elim_cycles:                       3
% 7.47/1.52  merged_defs:                            8
% 7.47/1.52  merged_defs_ncl:                        0
% 7.47/1.52  bin_hyper_res:                          9
% 7.47/1.52  prep_cycles:                            4
% 7.47/1.52  pred_elim_time:                         0.005
% 7.47/1.52  splitting_time:                         0.
% 7.47/1.52  sem_filter_time:                        0.
% 7.47/1.52  monotx_time:                            0.
% 7.47/1.52  subtype_inf_time:                       0.
% 7.47/1.52  
% 7.47/1.52  ------ Problem properties
% 7.47/1.52  
% 7.47/1.52  clauses:                                20
% 7.47/1.52  conjectures:                            4
% 7.47/1.52  epr:                                    2
% 7.47/1.52  horn:                                   16
% 7.47/1.52  ground:                                 4
% 7.47/1.52  unary:                                  5
% 7.47/1.52  binary:                                 9
% 7.47/1.52  lits:                                   44
% 7.47/1.52  lits_eq:                                6
% 7.47/1.52  fd_pure:                                0
% 7.47/1.52  fd_pseudo:                              0
% 7.47/1.52  fd_cond:                                0
% 7.47/1.52  fd_pseudo_cond:                         3
% 7.47/1.52  ac_symbols:                             0
% 7.47/1.52  
% 7.47/1.52  ------ Propositional Solver
% 7.47/1.52  
% 7.47/1.52  prop_solver_calls:                      33
% 7.47/1.52  prop_fast_solver_calls:                 977
% 7.47/1.52  smt_solver_calls:                       0
% 7.47/1.52  smt_fast_solver_calls:                  0
% 7.47/1.52  prop_num_of_clauses:                    6884
% 7.47/1.52  prop_preprocess_simplified:             11670
% 7.47/1.52  prop_fo_subsumed:                       13
% 7.47/1.52  prop_solver_time:                       0.
% 7.47/1.52  smt_solver_time:                        0.
% 7.47/1.52  smt_fast_solver_time:                   0.
% 7.47/1.52  prop_fast_solver_time:                  0.
% 7.47/1.52  prop_unsat_core_time:                   0.
% 7.47/1.52  
% 7.47/1.52  ------ QBF
% 7.47/1.52  
% 7.47/1.52  qbf_q_res:                              0
% 7.47/1.52  qbf_num_tautologies:                    0
% 7.47/1.52  qbf_prep_cycles:                        0
% 7.47/1.52  
% 7.47/1.52  ------ BMC1
% 7.47/1.52  
% 7.47/1.52  bmc1_current_bound:                     -1
% 7.47/1.52  bmc1_last_solved_bound:                 -1
% 7.47/1.52  bmc1_unsat_core_size:                   -1
% 7.47/1.52  bmc1_unsat_core_parents_size:           -1
% 7.47/1.52  bmc1_merge_next_fun:                    0
% 7.47/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.47/1.52  
% 7.47/1.52  ------ Instantiation
% 7.47/1.52  
% 7.47/1.52  inst_num_of_clauses:                    1663
% 7.47/1.52  inst_num_in_passive:                    356
% 7.47/1.52  inst_num_in_active:                     693
% 7.47/1.52  inst_num_in_unprocessed:                614
% 7.47/1.52  inst_num_of_loops:                      900
% 7.47/1.52  inst_num_of_learning_restarts:          0
% 7.47/1.52  inst_num_moves_active_passive:          201
% 7.47/1.52  inst_lit_activity:                      0
% 7.47/1.52  inst_lit_activity_moves:                0
% 7.47/1.52  inst_num_tautologies:                   0
% 7.47/1.52  inst_num_prop_implied:                  0
% 7.47/1.52  inst_num_existing_simplified:           0
% 7.47/1.52  inst_num_eq_res_simplified:             0
% 7.47/1.52  inst_num_child_elim:                    0
% 7.47/1.52  inst_num_of_dismatching_blockings:      1111
% 7.47/1.52  inst_num_of_non_proper_insts:           1872
% 7.47/1.52  inst_num_of_duplicates:                 0
% 7.47/1.52  inst_inst_num_from_inst_to_res:         0
% 7.47/1.52  inst_dismatching_checking_time:         0.
% 7.47/1.52  
% 7.47/1.52  ------ Resolution
% 7.47/1.52  
% 7.47/1.52  res_num_of_clauses:                     0
% 7.47/1.52  res_num_in_passive:                     0
% 7.47/1.52  res_num_in_active:                      0
% 7.47/1.52  res_num_of_loops:                       106
% 7.47/1.52  res_forward_subset_subsumed:            169
% 7.47/1.52  res_backward_subset_subsumed:           6
% 7.47/1.52  res_forward_subsumed:                   0
% 7.47/1.52  res_backward_subsumed:                  0
% 7.47/1.52  res_forward_subsumption_resolution:     0
% 7.47/1.52  res_backward_subsumption_resolution:    0
% 7.47/1.52  res_clause_to_clause_subsumption:       10230
% 7.47/1.52  res_orphan_elimination:                 0
% 7.47/1.52  res_tautology_del:                      224
% 7.47/1.52  res_num_eq_res_simplified:              0
% 7.47/1.52  res_num_sel_changes:                    0
% 7.47/1.52  res_moves_from_active_to_pass:          0
% 7.47/1.52  
% 7.47/1.52  ------ Superposition
% 7.47/1.52  
% 7.47/1.52  sup_time_total:                         0.
% 7.47/1.52  sup_time_generating:                    0.
% 7.47/1.52  sup_time_sim_full:                      0.
% 7.47/1.52  sup_time_sim_immed:                     0.
% 7.47/1.52  
% 7.47/1.52  sup_num_of_clauses:                     691
% 7.47/1.52  sup_num_in_active:                      130
% 7.47/1.52  sup_num_in_passive:                     561
% 7.47/1.52  sup_num_of_loops:                       178
% 7.47/1.52  sup_fw_superposition:                   1960
% 7.47/1.52  sup_bw_superposition:                   1786
% 7.47/1.52  sup_immediate_simplified:               1291
% 7.47/1.52  sup_given_eliminated:                   6
% 7.47/1.52  comparisons_done:                       0
% 7.47/1.52  comparisons_avoided:                    0
% 7.47/1.52  
% 7.47/1.52  ------ Simplifications
% 7.47/1.52  
% 7.47/1.52  
% 7.47/1.52  sim_fw_subset_subsumed:                 13
% 7.47/1.52  sim_bw_subset_subsumed:                 6
% 7.47/1.52  sim_fw_subsumed:                        446
% 7.47/1.52  sim_bw_subsumed:                        21
% 7.47/1.52  sim_fw_subsumption_res:                 0
% 7.47/1.52  sim_bw_subsumption_res:                 0
% 7.47/1.52  sim_tautology_del:                      75
% 7.47/1.52  sim_eq_tautology_del:                   91
% 7.47/1.52  sim_eq_res_simp:                        2
% 7.47/1.52  sim_fw_demodulated:                     527
% 7.47/1.52  sim_bw_demodulated:                     105
% 7.47/1.52  sim_light_normalised:                   424
% 7.47/1.52  sim_joinable_taut:                      0
% 7.47/1.52  sim_joinable_simp:                      0
% 7.47/1.52  sim_ac_normalised:                      0
% 7.47/1.52  sim_smt_subsumption:                    0
% 7.47/1.52  
%------------------------------------------------------------------------------
