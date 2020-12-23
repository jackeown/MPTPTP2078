%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:49 EST 2020

% Result     : Theorem 11.75s
% Output     : CNFRefutation 11.75s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 214 expanded)
%              Number of clauses        :   57 (  71 expanded)
%              Number of leaves         :   14 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  292 ( 894 expanded)
%              Number of equality atoms :   41 (  55 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
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

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f43,f43])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f15])).

fof(f29,plain,(
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

fof(f28,plain,(
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

fof(f27,plain,
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

fof(f30,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    & ( v2_tex_2(sK4,sK2)
      | v2_tex_2(sK3,sK2) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f29,f28,f27])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f13])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,
    ( v2_tex_2(sK4,sK2)
    | v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_891,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1670,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK3)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_891])).

cnf(c_2142,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK3)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK3,X0)),sK3)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_1670])).

cnf(c_35222,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK3)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK3,sK4)),sK3)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2142])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_5964,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,sK4)
    | ~ r1_tarski(X1,sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_21459,plain,
    ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(X0)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(X0)),sK4)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_5964])).

cnf(c_21461,plain,
    ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),sK4)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_21459])).

cnf(c_10,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1632,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK4,X0)),sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_10276,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK4,sK3)),sK4) ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_1533,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(X1,sK4)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_891])).

cnf(c_1715,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1533])).

cnf(c_2867,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK4,X0)),sK4)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK4,X0)) ),
    inference(instantiation,[status(thm)],[c_1715])).

cnf(c_4872,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK4,sK3)),sK4)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_2867])).

cnf(c_2720,plain,
    ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),X0)
    | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4578,plain,
    ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),sK4)
    | ~ r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2720])).

cnf(c_2754,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK3,sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_0,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2297,plain,
    ( k1_setfam_1(k2_tarski(sK4,sK3)) = k1_setfam_1(k2_tarski(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_889,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1587,plain,
    ( X0 != X1
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X1
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_889])).

cnf(c_1742,plain,
    ( X0 != k1_setfam_1(k2_tarski(sK3,sK4))
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) = X0
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_1900,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k1_setfam_1(k2_tarski(sK4,sK3))
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK3,sK4))
    | k1_setfam_1(k2_tarski(sK4,sK3)) != k1_setfam_1(k2_tarski(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1742])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1425,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK2)),X0)
    | r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1801,plain,
    ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
    | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1425])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1424,plain,
    ( ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),u1_struct_0(sK2))
    | r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1803,plain,
    ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2))
    | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1424])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1331,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1334,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1773,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1331,c_1334])).

cnf(c_1775,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1773])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

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
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_147])).

cnf(c_1690,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK2))
    | k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k1_setfam_1(k2_tarski(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_184])).

cnf(c_1691,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k1_setfam_1(k2_tarski(sK3,sK4))
    | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1690])).

cnf(c_1386,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1675,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(c_14,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

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

cnf(c_1503,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_1611,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_1503])).

cnf(c_1374,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v2_tex_2(sK4,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_1599,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
    | ~ v2_tex_2(sK4,sK2)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_15,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_16,negated_conjecture,
    ( v2_tex_2(sK4,sK2)
    | v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35222,c_21461,c_10276,c_4872,c_4578,c_2754,c_2297,c_1900,c_1801,c_1803,c_1775,c_1773,c_1691,c_1675,c_1611,c_1599,c_15,c_16,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:03:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.75/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.75/1.99  
% 11.75/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.75/1.99  
% 11.75/1.99  ------  iProver source info
% 11.75/1.99  
% 11.75/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.75/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.75/1.99  git: non_committed_changes: false
% 11.75/1.99  git: last_make_outside_of_git: false
% 11.75/1.99  
% 11.75/1.99  ------ 
% 11.75/1.99  
% 11.75/1.99  ------ Input Options
% 11.75/1.99  
% 11.75/1.99  --out_options                           all
% 11.75/1.99  --tptp_safe_out                         true
% 11.75/1.99  --problem_path                          ""
% 11.75/1.99  --include_path                          ""
% 11.75/1.99  --clausifier                            res/vclausify_rel
% 11.75/1.99  --clausifier_options                    ""
% 11.75/1.99  --stdin                                 false
% 11.75/1.99  --stats_out                             all
% 11.75/1.99  
% 11.75/1.99  ------ General Options
% 11.75/1.99  
% 11.75/1.99  --fof                                   false
% 11.75/1.99  --time_out_real                         305.
% 11.75/1.99  --time_out_virtual                      -1.
% 11.75/1.99  --symbol_type_check                     false
% 11.75/1.99  --clausify_out                          false
% 11.75/1.99  --sig_cnt_out                           false
% 11.75/1.99  --trig_cnt_out                          false
% 11.75/1.99  --trig_cnt_out_tolerance                1.
% 11.75/1.99  --trig_cnt_out_sk_spl                   false
% 11.75/1.99  --abstr_cl_out                          false
% 11.75/1.99  
% 11.75/1.99  ------ Global Options
% 11.75/1.99  
% 11.75/1.99  --schedule                              default
% 11.75/1.99  --add_important_lit                     false
% 11.75/1.99  --prop_solver_per_cl                    1000
% 11.75/1.99  --min_unsat_core                        false
% 11.75/1.99  --soft_assumptions                      false
% 11.75/1.99  --soft_lemma_size                       3
% 11.75/1.99  --prop_impl_unit_size                   0
% 11.75/1.99  --prop_impl_unit                        []
% 11.75/1.99  --share_sel_clauses                     true
% 11.75/1.99  --reset_solvers                         false
% 11.75/1.99  --bc_imp_inh                            [conj_cone]
% 11.75/1.99  --conj_cone_tolerance                   3.
% 11.75/1.99  --extra_neg_conj                        none
% 11.75/1.99  --large_theory_mode                     true
% 11.75/1.99  --prolific_symb_bound                   200
% 11.75/1.99  --lt_threshold                          2000
% 11.75/1.99  --clause_weak_htbl                      true
% 11.75/1.99  --gc_record_bc_elim                     false
% 11.75/1.99  
% 11.75/1.99  ------ Preprocessing Options
% 11.75/1.99  
% 11.75/1.99  --preprocessing_flag                    true
% 11.75/1.99  --time_out_prep_mult                    0.1
% 11.75/1.99  --splitting_mode                        input
% 11.75/1.99  --splitting_grd                         true
% 11.75/1.99  --splitting_cvd                         false
% 11.75/1.99  --splitting_cvd_svl                     false
% 11.75/1.99  --splitting_nvd                         32
% 11.75/1.99  --sub_typing                            true
% 11.75/1.99  --prep_gs_sim                           true
% 11.75/1.99  --prep_unflatten                        true
% 11.75/1.99  --prep_res_sim                          true
% 11.75/1.99  --prep_upred                            true
% 11.75/1.99  --prep_sem_filter                       exhaustive
% 11.75/1.99  --prep_sem_filter_out                   false
% 11.75/1.99  --pred_elim                             true
% 11.75/1.99  --res_sim_input                         true
% 11.75/1.99  --eq_ax_congr_red                       true
% 11.75/1.99  --pure_diseq_elim                       true
% 11.75/1.99  --brand_transform                       false
% 11.75/1.99  --non_eq_to_eq                          false
% 11.75/1.99  --prep_def_merge                        true
% 11.75/1.99  --prep_def_merge_prop_impl              false
% 11.75/1.99  --prep_def_merge_mbd                    true
% 11.75/1.99  --prep_def_merge_tr_red                 false
% 11.75/1.99  --prep_def_merge_tr_cl                  false
% 11.75/1.99  --smt_preprocessing                     true
% 11.75/1.99  --smt_ac_axioms                         fast
% 11.75/1.99  --preprocessed_out                      false
% 11.75/1.99  --preprocessed_stats                    false
% 11.75/1.99  
% 11.75/1.99  ------ Abstraction refinement Options
% 11.75/1.99  
% 11.75/1.99  --abstr_ref                             []
% 11.75/1.99  --abstr_ref_prep                        false
% 11.75/1.99  --abstr_ref_until_sat                   false
% 11.75/1.99  --abstr_ref_sig_restrict                funpre
% 11.75/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.75/1.99  --abstr_ref_under                       []
% 11.75/1.99  
% 11.75/1.99  ------ SAT Options
% 11.75/1.99  
% 11.75/1.99  --sat_mode                              false
% 11.75/1.99  --sat_fm_restart_options                ""
% 11.75/1.99  --sat_gr_def                            false
% 11.75/1.99  --sat_epr_types                         true
% 11.75/1.99  --sat_non_cyclic_types                  false
% 11.75/1.99  --sat_finite_models                     false
% 11.75/1.99  --sat_fm_lemmas                         false
% 11.75/1.99  --sat_fm_prep                           false
% 11.75/1.99  --sat_fm_uc_incr                        true
% 11.75/1.99  --sat_out_model                         small
% 11.75/1.99  --sat_out_clauses                       false
% 11.75/1.99  
% 11.75/1.99  ------ QBF Options
% 11.75/1.99  
% 11.75/1.99  --qbf_mode                              false
% 11.75/1.99  --qbf_elim_univ                         false
% 11.75/1.99  --qbf_dom_inst                          none
% 11.75/1.99  --qbf_dom_pre_inst                      false
% 11.75/1.99  --qbf_sk_in                             false
% 11.75/1.99  --qbf_pred_elim                         true
% 11.75/1.99  --qbf_split                             512
% 11.75/1.99  
% 11.75/1.99  ------ BMC1 Options
% 11.75/1.99  
% 11.75/1.99  --bmc1_incremental                      false
% 11.75/1.99  --bmc1_axioms                           reachable_all
% 11.75/1.99  --bmc1_min_bound                        0
% 11.75/1.99  --bmc1_max_bound                        -1
% 11.75/1.99  --bmc1_max_bound_default                -1
% 11.75/1.99  --bmc1_symbol_reachability              true
% 11.75/1.99  --bmc1_property_lemmas                  false
% 11.75/1.99  --bmc1_k_induction                      false
% 11.75/1.99  --bmc1_non_equiv_states                 false
% 11.75/1.99  --bmc1_deadlock                         false
% 11.75/1.99  --bmc1_ucm                              false
% 11.75/1.99  --bmc1_add_unsat_core                   none
% 11.75/1.99  --bmc1_unsat_core_children              false
% 11.75/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.75/1.99  --bmc1_out_stat                         full
% 11.75/1.99  --bmc1_ground_init                      false
% 11.75/1.99  --bmc1_pre_inst_next_state              false
% 11.75/1.99  --bmc1_pre_inst_state                   false
% 11.75/1.99  --bmc1_pre_inst_reach_state             false
% 11.75/1.99  --bmc1_out_unsat_core                   false
% 11.75/1.99  --bmc1_aig_witness_out                  false
% 11.75/1.99  --bmc1_verbose                          false
% 11.75/1.99  --bmc1_dump_clauses_tptp                false
% 11.75/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.75/1.99  --bmc1_dump_file                        -
% 11.75/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.75/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.75/1.99  --bmc1_ucm_extend_mode                  1
% 11.75/1.99  --bmc1_ucm_init_mode                    2
% 11.75/1.99  --bmc1_ucm_cone_mode                    none
% 11.75/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.75/1.99  --bmc1_ucm_relax_model                  4
% 11.75/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.75/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.75/1.99  --bmc1_ucm_layered_model                none
% 11.75/1.99  --bmc1_ucm_max_lemma_size               10
% 11.75/1.99  
% 11.75/1.99  ------ AIG Options
% 11.75/1.99  
% 11.75/1.99  --aig_mode                              false
% 11.75/1.99  
% 11.75/1.99  ------ Instantiation Options
% 11.75/1.99  
% 11.75/1.99  --instantiation_flag                    true
% 11.75/1.99  --inst_sos_flag                         true
% 11.75/1.99  --inst_sos_phase                        true
% 11.75/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.75/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.75/1.99  --inst_lit_sel_side                     num_symb
% 11.75/1.99  --inst_solver_per_active                1400
% 11.75/1.99  --inst_solver_calls_frac                1.
% 11.75/1.99  --inst_passive_queue_type               priority_queues
% 11.75/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.75/1.99  --inst_passive_queues_freq              [25;2]
% 11.75/1.99  --inst_dismatching                      true
% 11.75/1.99  --inst_eager_unprocessed_to_passive     true
% 11.75/1.99  --inst_prop_sim_given                   true
% 11.75/1.99  --inst_prop_sim_new                     false
% 11.75/1.99  --inst_subs_new                         false
% 11.75/1.99  --inst_eq_res_simp                      false
% 11.75/1.99  --inst_subs_given                       false
% 11.75/1.99  --inst_orphan_elimination               true
% 11.75/1.99  --inst_learning_loop_flag               true
% 11.75/1.99  --inst_learning_start                   3000
% 11.75/1.99  --inst_learning_factor                  2
% 11.75/1.99  --inst_start_prop_sim_after_learn       3
% 11.75/1.99  --inst_sel_renew                        solver
% 11.75/1.99  --inst_lit_activity_flag                true
% 11.75/1.99  --inst_restr_to_given                   false
% 11.75/1.99  --inst_activity_threshold               500
% 11.75/1.99  --inst_out_proof                        true
% 11.75/1.99  
% 11.75/1.99  ------ Resolution Options
% 11.75/1.99  
% 11.75/1.99  --resolution_flag                       true
% 11.75/1.99  --res_lit_sel                           adaptive
% 11.75/1.99  --res_lit_sel_side                      none
% 11.75/1.99  --res_ordering                          kbo
% 11.75/1.99  --res_to_prop_solver                    active
% 11.75/1.99  --res_prop_simpl_new                    false
% 11.75/1.99  --res_prop_simpl_given                  true
% 11.75/1.99  --res_passive_queue_type                priority_queues
% 11.75/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.75/1.99  --res_passive_queues_freq               [15;5]
% 11.75/1.99  --res_forward_subs                      full
% 11.75/1.99  --res_backward_subs                     full
% 11.75/1.99  --res_forward_subs_resolution           true
% 11.75/1.99  --res_backward_subs_resolution          true
% 11.75/1.99  --res_orphan_elimination                true
% 11.75/1.99  --res_time_limit                        2.
% 11.75/1.99  --res_out_proof                         true
% 11.75/1.99  
% 11.75/1.99  ------ Superposition Options
% 11.75/1.99  
% 11.75/1.99  --superposition_flag                    true
% 11.75/1.99  --sup_passive_queue_type                priority_queues
% 11.75/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.75/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.75/1.99  --demod_completeness_check              fast
% 11.75/1.99  --demod_use_ground                      true
% 11.75/1.99  --sup_to_prop_solver                    passive
% 11.75/1.99  --sup_prop_simpl_new                    true
% 11.75/1.99  --sup_prop_simpl_given                  true
% 11.75/1.99  --sup_fun_splitting                     true
% 11.75/1.99  --sup_smt_interval                      50000
% 11.75/1.99  
% 11.75/1.99  ------ Superposition Simplification Setup
% 11.75/1.99  
% 11.75/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.75/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.75/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.75/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.75/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.75/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.75/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.75/1.99  --sup_immed_triv                        [TrivRules]
% 11.75/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/1.99  --sup_immed_bw_main                     []
% 11.75/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.75/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.75/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/1.99  --sup_input_bw                          []
% 11.75/1.99  
% 11.75/1.99  ------ Combination Options
% 11.75/1.99  
% 11.75/1.99  --comb_res_mult                         3
% 11.75/1.99  --comb_sup_mult                         2
% 11.75/1.99  --comb_inst_mult                        10
% 11.75/1.99  
% 11.75/1.99  ------ Debug Options
% 11.75/1.99  
% 11.75/1.99  --dbg_backtrace                         false
% 11.75/1.99  --dbg_dump_prop_clauses                 false
% 11.75/1.99  --dbg_dump_prop_clauses_file            -
% 11.75/1.99  --dbg_out_stat                          false
% 11.75/1.99  ------ Parsing...
% 11.75/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.75/1.99  
% 11.75/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.75/1.99  
% 11.75/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.75/1.99  
% 11.75/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.75/1.99  ------ Proving...
% 11.75/1.99  ------ Problem Properties 
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  clauses                                 19
% 11.75/1.99  conjectures                             4
% 11.75/1.99  EPR                                     2
% 11.75/1.99  Horn                                    15
% 11.75/1.99  unary                                   5
% 11.75/1.99  binary                                  8
% 11.75/1.99  lits                                    42
% 11.75/1.99  lits eq                                 5
% 11.75/1.99  fd_pure                                 0
% 11.75/1.99  fd_pseudo                               0
% 11.75/1.99  fd_cond                                 0
% 11.75/1.99  fd_pseudo_cond                          3
% 11.75/1.99  AC symbols                              0
% 11.75/1.99  
% 11.75/1.99  ------ Schedule dynamic 5 is on 
% 11.75/1.99  
% 11.75/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  ------ 
% 11.75/1.99  Current options:
% 11.75/1.99  ------ 
% 11.75/1.99  
% 11.75/1.99  ------ Input Options
% 11.75/1.99  
% 11.75/1.99  --out_options                           all
% 11.75/1.99  --tptp_safe_out                         true
% 11.75/1.99  --problem_path                          ""
% 11.75/1.99  --include_path                          ""
% 11.75/1.99  --clausifier                            res/vclausify_rel
% 11.75/1.99  --clausifier_options                    ""
% 11.75/1.99  --stdin                                 false
% 11.75/1.99  --stats_out                             all
% 11.75/1.99  
% 11.75/1.99  ------ General Options
% 11.75/1.99  
% 11.75/1.99  --fof                                   false
% 11.75/1.99  --time_out_real                         305.
% 11.75/1.99  --time_out_virtual                      -1.
% 11.75/1.99  --symbol_type_check                     false
% 11.75/1.99  --clausify_out                          false
% 11.75/1.99  --sig_cnt_out                           false
% 11.75/1.99  --trig_cnt_out                          false
% 11.75/1.99  --trig_cnt_out_tolerance                1.
% 11.75/1.99  --trig_cnt_out_sk_spl                   false
% 11.75/1.99  --abstr_cl_out                          false
% 11.75/1.99  
% 11.75/1.99  ------ Global Options
% 11.75/1.99  
% 11.75/1.99  --schedule                              default
% 11.75/1.99  --add_important_lit                     false
% 11.75/1.99  --prop_solver_per_cl                    1000
% 11.75/1.99  --min_unsat_core                        false
% 11.75/1.99  --soft_assumptions                      false
% 11.75/1.99  --soft_lemma_size                       3
% 11.75/1.99  --prop_impl_unit_size                   0
% 11.75/1.99  --prop_impl_unit                        []
% 11.75/1.99  --share_sel_clauses                     true
% 11.75/1.99  --reset_solvers                         false
% 11.75/1.99  --bc_imp_inh                            [conj_cone]
% 11.75/1.99  --conj_cone_tolerance                   3.
% 11.75/1.99  --extra_neg_conj                        none
% 11.75/1.99  --large_theory_mode                     true
% 11.75/1.99  --prolific_symb_bound                   200
% 11.75/1.99  --lt_threshold                          2000
% 11.75/1.99  --clause_weak_htbl                      true
% 11.75/1.99  --gc_record_bc_elim                     false
% 11.75/1.99  
% 11.75/1.99  ------ Preprocessing Options
% 11.75/1.99  
% 11.75/1.99  --preprocessing_flag                    true
% 11.75/1.99  --time_out_prep_mult                    0.1
% 11.75/1.99  --splitting_mode                        input
% 11.75/1.99  --splitting_grd                         true
% 11.75/1.99  --splitting_cvd                         false
% 11.75/1.99  --splitting_cvd_svl                     false
% 11.75/1.99  --splitting_nvd                         32
% 11.75/1.99  --sub_typing                            true
% 11.75/1.99  --prep_gs_sim                           true
% 11.75/1.99  --prep_unflatten                        true
% 11.75/1.99  --prep_res_sim                          true
% 11.75/1.99  --prep_upred                            true
% 11.75/1.99  --prep_sem_filter                       exhaustive
% 11.75/1.99  --prep_sem_filter_out                   false
% 11.75/1.99  --pred_elim                             true
% 11.75/1.99  --res_sim_input                         true
% 11.75/1.99  --eq_ax_congr_red                       true
% 11.75/1.99  --pure_diseq_elim                       true
% 11.75/1.99  --brand_transform                       false
% 11.75/1.99  --non_eq_to_eq                          false
% 11.75/1.99  --prep_def_merge                        true
% 11.75/1.99  --prep_def_merge_prop_impl              false
% 11.75/1.99  --prep_def_merge_mbd                    true
% 11.75/1.99  --prep_def_merge_tr_red                 false
% 11.75/1.99  --prep_def_merge_tr_cl                  false
% 11.75/1.99  --smt_preprocessing                     true
% 11.75/1.99  --smt_ac_axioms                         fast
% 11.75/1.99  --preprocessed_out                      false
% 11.75/1.99  --preprocessed_stats                    false
% 11.75/1.99  
% 11.75/1.99  ------ Abstraction refinement Options
% 11.75/1.99  
% 11.75/1.99  --abstr_ref                             []
% 11.75/1.99  --abstr_ref_prep                        false
% 11.75/1.99  --abstr_ref_until_sat                   false
% 11.75/1.99  --abstr_ref_sig_restrict                funpre
% 11.75/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.75/1.99  --abstr_ref_under                       []
% 11.75/1.99  
% 11.75/1.99  ------ SAT Options
% 11.75/1.99  
% 11.75/1.99  --sat_mode                              false
% 11.75/1.99  --sat_fm_restart_options                ""
% 11.75/1.99  --sat_gr_def                            false
% 11.75/1.99  --sat_epr_types                         true
% 11.75/1.99  --sat_non_cyclic_types                  false
% 11.75/2.00  --sat_finite_models                     false
% 11.75/2.00  --sat_fm_lemmas                         false
% 11.75/2.00  --sat_fm_prep                           false
% 11.75/2.00  --sat_fm_uc_incr                        true
% 11.75/2.00  --sat_out_model                         small
% 11.75/2.00  --sat_out_clauses                       false
% 11.75/2.00  
% 11.75/2.00  ------ QBF Options
% 11.75/2.00  
% 11.75/2.00  --qbf_mode                              false
% 11.75/2.00  --qbf_elim_univ                         false
% 11.75/2.00  --qbf_dom_inst                          none
% 11.75/2.00  --qbf_dom_pre_inst                      false
% 11.75/2.00  --qbf_sk_in                             false
% 11.75/2.00  --qbf_pred_elim                         true
% 11.75/2.00  --qbf_split                             512
% 11.75/2.00  
% 11.75/2.00  ------ BMC1 Options
% 11.75/2.00  
% 11.75/2.00  --bmc1_incremental                      false
% 11.75/2.00  --bmc1_axioms                           reachable_all
% 11.75/2.00  --bmc1_min_bound                        0
% 11.75/2.00  --bmc1_max_bound                        -1
% 11.75/2.00  --bmc1_max_bound_default                -1
% 11.75/2.00  --bmc1_symbol_reachability              true
% 11.75/2.00  --bmc1_property_lemmas                  false
% 11.75/2.00  --bmc1_k_induction                      false
% 11.75/2.00  --bmc1_non_equiv_states                 false
% 11.75/2.00  --bmc1_deadlock                         false
% 11.75/2.00  --bmc1_ucm                              false
% 11.75/2.00  --bmc1_add_unsat_core                   none
% 11.75/2.00  --bmc1_unsat_core_children              false
% 11.75/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.75/2.00  --bmc1_out_stat                         full
% 11.75/2.00  --bmc1_ground_init                      false
% 11.75/2.00  --bmc1_pre_inst_next_state              false
% 11.75/2.00  --bmc1_pre_inst_state                   false
% 11.75/2.00  --bmc1_pre_inst_reach_state             false
% 11.75/2.00  --bmc1_out_unsat_core                   false
% 11.75/2.00  --bmc1_aig_witness_out                  false
% 11.75/2.00  --bmc1_verbose                          false
% 11.75/2.00  --bmc1_dump_clauses_tptp                false
% 11.75/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.75/2.00  --bmc1_dump_file                        -
% 11.75/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.75/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.75/2.00  --bmc1_ucm_extend_mode                  1
% 11.75/2.00  --bmc1_ucm_init_mode                    2
% 11.75/2.00  --bmc1_ucm_cone_mode                    none
% 11.75/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.75/2.00  --bmc1_ucm_relax_model                  4
% 11.75/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.75/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.75/2.00  --bmc1_ucm_layered_model                none
% 11.75/2.00  --bmc1_ucm_max_lemma_size               10
% 11.75/2.00  
% 11.75/2.00  ------ AIG Options
% 11.75/2.00  
% 11.75/2.00  --aig_mode                              false
% 11.75/2.00  
% 11.75/2.00  ------ Instantiation Options
% 11.75/2.00  
% 11.75/2.00  --instantiation_flag                    true
% 11.75/2.00  --inst_sos_flag                         true
% 11.75/2.00  --inst_sos_phase                        true
% 11.75/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.75/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.75/2.00  --inst_lit_sel_side                     none
% 11.75/2.00  --inst_solver_per_active                1400
% 11.75/2.00  --inst_solver_calls_frac                1.
% 11.75/2.00  --inst_passive_queue_type               priority_queues
% 11.75/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.75/2.00  --inst_passive_queues_freq              [25;2]
% 11.75/2.00  --inst_dismatching                      true
% 11.75/2.00  --inst_eager_unprocessed_to_passive     true
% 11.75/2.00  --inst_prop_sim_given                   true
% 11.75/2.00  --inst_prop_sim_new                     false
% 11.75/2.00  --inst_subs_new                         false
% 11.75/2.00  --inst_eq_res_simp                      false
% 11.75/2.00  --inst_subs_given                       false
% 11.75/2.00  --inst_orphan_elimination               true
% 11.75/2.00  --inst_learning_loop_flag               true
% 11.75/2.00  --inst_learning_start                   3000
% 11.75/2.00  --inst_learning_factor                  2
% 11.75/2.00  --inst_start_prop_sim_after_learn       3
% 11.75/2.00  --inst_sel_renew                        solver
% 11.75/2.00  --inst_lit_activity_flag                true
% 11.75/2.00  --inst_restr_to_given                   false
% 11.75/2.00  --inst_activity_threshold               500
% 11.75/2.00  --inst_out_proof                        true
% 11.75/2.00  
% 11.75/2.00  ------ Resolution Options
% 11.75/2.00  
% 11.75/2.00  --resolution_flag                       false
% 11.75/2.00  --res_lit_sel                           adaptive
% 11.75/2.00  --res_lit_sel_side                      none
% 11.75/2.00  --res_ordering                          kbo
% 11.75/2.00  --res_to_prop_solver                    active
% 11.75/2.00  --res_prop_simpl_new                    false
% 11.75/2.00  --res_prop_simpl_given                  true
% 11.75/2.00  --res_passive_queue_type                priority_queues
% 11.75/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.75/2.00  --res_passive_queues_freq               [15;5]
% 11.75/2.00  --res_forward_subs                      full
% 11.75/2.00  --res_backward_subs                     full
% 11.75/2.00  --res_forward_subs_resolution           true
% 11.75/2.00  --res_backward_subs_resolution          true
% 11.75/2.00  --res_orphan_elimination                true
% 11.75/2.00  --res_time_limit                        2.
% 11.75/2.00  --res_out_proof                         true
% 11.75/2.00  
% 11.75/2.00  ------ Superposition Options
% 11.75/2.00  
% 11.75/2.00  --superposition_flag                    true
% 11.75/2.00  --sup_passive_queue_type                priority_queues
% 11.75/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.75/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.75/2.00  --demod_completeness_check              fast
% 11.75/2.00  --demod_use_ground                      true
% 11.75/2.00  --sup_to_prop_solver                    passive
% 11.75/2.00  --sup_prop_simpl_new                    true
% 11.75/2.00  --sup_prop_simpl_given                  true
% 11.75/2.00  --sup_fun_splitting                     true
% 11.75/2.00  --sup_smt_interval                      50000
% 11.75/2.00  
% 11.75/2.00  ------ Superposition Simplification Setup
% 11.75/2.00  
% 11.75/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.75/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.75/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.75/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.75/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.75/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.75/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.75/2.00  --sup_immed_triv                        [TrivRules]
% 11.75/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/2.00  --sup_immed_bw_main                     []
% 11.75/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.75/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.75/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.75/2.00  --sup_input_bw                          []
% 11.75/2.00  
% 11.75/2.00  ------ Combination Options
% 11.75/2.00  
% 11.75/2.00  --comb_res_mult                         3
% 11.75/2.00  --comb_sup_mult                         2
% 11.75/2.00  --comb_inst_mult                        10
% 11.75/2.00  
% 11.75/2.00  ------ Debug Options
% 11.75/2.00  
% 11.75/2.00  --dbg_backtrace                         false
% 11.75/2.00  --dbg_dump_prop_clauses                 false
% 11.75/2.00  --dbg_dump_prop_clauses_file            -
% 11.75/2.00  --dbg_out_stat                          false
% 11.75/2.00  
% 11.75/2.00  
% 11.75/2.00  
% 11.75/2.00  
% 11.75/2.00  ------ Proving...
% 11.75/2.00  
% 11.75/2.00  
% 11.75/2.00  % SZS status Theorem for theBenchmark.p
% 11.75/2.00  
% 11.75/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.75/2.00  
% 11.75/2.00  fof(f2,axiom,(
% 11.75/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.75/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/2.00  
% 11.75/2.00  fof(f11,plain,(
% 11.75/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.75/2.00    inference(ennf_transformation,[],[f2])).
% 11.75/2.00  
% 11.75/2.00  fof(f17,plain,(
% 11.75/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.75/2.00    inference(nnf_transformation,[],[f11])).
% 11.75/2.00  
% 11.75/2.00  fof(f18,plain,(
% 11.75/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.75/2.00    inference(rectify,[],[f17])).
% 11.75/2.00  
% 11.75/2.00  fof(f19,plain,(
% 11.75/2.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.75/2.00    introduced(choice_axiom,[])).
% 11.75/2.00  
% 11.75/2.00  fof(f20,plain,(
% 11.75/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.75/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 11.75/2.00  
% 11.75/2.00  fof(f32,plain,(
% 11.75/2.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 11.75/2.00    inference(cnf_transformation,[],[f20])).
% 11.75/2.00  
% 11.75/2.00  fof(f4,axiom,(
% 11.75/2.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 11.75/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/2.00  
% 11.75/2.00  fof(f41,plain,(
% 11.75/2.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 11.75/2.00    inference(cnf_transformation,[],[f4])).
% 11.75/2.00  
% 11.75/2.00  fof(f6,axiom,(
% 11.75/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.75/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/2.00  
% 11.75/2.00  fof(f43,plain,(
% 11.75/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.75/2.00    inference(cnf_transformation,[],[f6])).
% 11.75/2.00  
% 11.75/2.00  fof(f59,plain,(
% 11.75/2.00    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 11.75/2.00    inference(definition_unfolding,[],[f41,f43])).
% 11.75/2.00  
% 11.75/2.00  fof(f1,axiom,(
% 11.75/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.75/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/2.00  
% 11.75/2.00  fof(f31,plain,(
% 11.75/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.75/2.00    inference(cnf_transformation,[],[f1])).
% 11.75/2.00  
% 11.75/2.00  fof(f52,plain,(
% 11.75/2.00    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 11.75/2.00    inference(definition_unfolding,[],[f31,f43,f43])).
% 11.75/2.00  
% 11.75/2.00  fof(f33,plain,(
% 11.75/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.75/2.00    inference(cnf_transformation,[],[f20])).
% 11.75/2.00  
% 11.75/2.00  fof(f34,plain,(
% 11.75/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.75/2.00    inference(cnf_transformation,[],[f20])).
% 11.75/2.00  
% 11.75/2.00  fof(f9,conjecture,(
% 11.75/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 11.75/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/2.00  
% 11.75/2.00  fof(f10,negated_conjecture,(
% 11.75/2.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 11.75/2.00    inference(negated_conjecture,[],[f9])).
% 11.75/2.00  
% 11.75/2.00  fof(f15,plain,(
% 11.75/2.00    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.75/2.00    inference(ennf_transformation,[],[f10])).
% 11.75/2.00  
% 11.75/2.00  fof(f16,plain,(
% 11.75/2.00    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.75/2.00    inference(flattening,[],[f15])).
% 11.75/2.00  
% 11.75/2.00  fof(f29,plain,(
% 11.75/2.00    ( ! [X0,X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK4),X0) & (v2_tex_2(sK4,X0) | v2_tex_2(X1,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.75/2.00    introduced(choice_axiom,[])).
% 11.75/2.00  
% 11.75/2.00  fof(f28,plain,(
% 11.75/2.00    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),sK3,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(sK3,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.75/2.00    introduced(choice_axiom,[])).
% 11.75/2.00  
% 11.75/2.00  fof(f27,plain,(
% 11.75/2.00    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK2),X1,X2),sK2) & (v2_tex_2(X2,sK2) | v2_tex_2(X1,sK2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 11.75/2.00    introduced(choice_axiom,[])).
% 11.75/2.00  
% 11.75/2.00  fof(f30,plain,(
% 11.75/2.00    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) & (v2_tex_2(sK4,sK2) | v2_tex_2(sK3,sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 11.75/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f29,f28,f27])).
% 11.75/2.00  
% 11.75/2.00  fof(f49,plain,(
% 11.75/2.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 11.75/2.00    inference(cnf_transformation,[],[f30])).
% 11.75/2.00  
% 11.75/2.00  fof(f7,axiom,(
% 11.75/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.75/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/2.00  
% 11.75/2.00  fof(f26,plain,(
% 11.75/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.75/2.00    inference(nnf_transformation,[],[f7])).
% 11.75/2.00  
% 11.75/2.00  fof(f44,plain,(
% 11.75/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.75/2.00    inference(cnf_transformation,[],[f26])).
% 11.75/2.00  
% 11.75/2.00  fof(f5,axiom,(
% 11.75/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 11.75/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/2.00  
% 11.75/2.00  fof(f12,plain,(
% 11.75/2.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.75/2.00    inference(ennf_transformation,[],[f5])).
% 11.75/2.00  
% 11.75/2.00  fof(f42,plain,(
% 11.75/2.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.75/2.00    inference(cnf_transformation,[],[f12])).
% 11.75/2.00  
% 11.75/2.00  fof(f60,plain,(
% 11.75/2.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.75/2.00    inference(definition_unfolding,[],[f42,f43])).
% 11.75/2.00  
% 11.75/2.00  fof(f45,plain,(
% 11.75/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.75/2.00    inference(cnf_transformation,[],[f26])).
% 11.75/2.00  
% 11.75/2.00  fof(f8,axiom,(
% 11.75/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 11.75/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/2.00  
% 11.75/2.00  fof(f13,plain,(
% 11.75/2.00    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/2.00    inference(ennf_transformation,[],[f8])).
% 11.75/2.00  
% 11.75/2.00  fof(f14,plain,(
% 11.75/2.00    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/2.00    inference(flattening,[],[f13])).
% 11.75/2.00  
% 11.75/2.00  fof(f46,plain,(
% 11.75/2.00    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/2.00    inference(cnf_transformation,[],[f14])).
% 11.75/2.00  
% 11.75/2.00  fof(f47,plain,(
% 11.75/2.00    l1_pre_topc(sK2)),
% 11.75/2.00    inference(cnf_transformation,[],[f30])).
% 11.75/2.00  
% 11.75/2.00  fof(f51,plain,(
% 11.75/2.00    ~v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)),
% 11.75/2.00    inference(cnf_transformation,[],[f30])).
% 11.75/2.00  
% 11.75/2.00  fof(f50,plain,(
% 11.75/2.00    v2_tex_2(sK4,sK2) | v2_tex_2(sK3,sK2)),
% 11.75/2.00    inference(cnf_transformation,[],[f30])).
% 11.75/2.00  
% 11.75/2.00  fof(f48,plain,(
% 11.75/2.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 11.75/2.00    inference(cnf_transformation,[],[f30])).
% 11.75/2.00  
% 11.75/2.00  cnf(c_891,plain,
% 11.75/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 11.75/2.00      theory(equality) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1670,plain,
% 11.75/2.00      ( ~ r1_tarski(X0,sK3)
% 11.75/2.00      | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK3)
% 11.75/2.00      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X0 ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_891]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_2142,plain,
% 11.75/2.00      ( r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK3)
% 11.75/2.00      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK3,X0)),sK3)
% 11.75/2.00      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK3,X0)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_1670]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_35222,plain,
% 11.75/2.00      ( r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK3)
% 11.75/2.00      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK3,sK4)),sK3)
% 11.75/2.00      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK3,sK4)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_2142]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_3,plain,
% 11.75/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 11.75/2.00      inference(cnf_transformation,[],[f32]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_5964,plain,
% 11.75/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,sK4) | ~ r1_tarski(X1,sK4) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_21459,plain,
% 11.75/2.00      ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(X0)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
% 11.75/2.00      | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(X0)),sK4)
% 11.75/2.00      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_5964]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_21461,plain,
% 11.75/2.00      ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
% 11.75/2.00      | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),sK4)
% 11.75/2.00      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_21459]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_10,plain,
% 11.75/2.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 11.75/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1632,plain,
% 11.75/2.00      ( r1_tarski(k1_setfam_1(k2_tarski(sK4,X0)),sK4) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_10276,plain,
% 11.75/2.00      ( r1_tarski(k1_setfam_1(k2_tarski(sK4,sK3)),sK4) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_1632]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1533,plain,
% 11.75/2.00      ( ~ r1_tarski(X0,sK4) | r1_tarski(X1,sK4) | X1 != X0 ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_891]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1715,plain,
% 11.75/2.00      ( ~ r1_tarski(X0,sK4)
% 11.75/2.00      | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4)
% 11.75/2.00      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X0 ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_1533]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_2867,plain,
% 11.75/2.00      ( r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4)
% 11.75/2.00      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK4,X0)),sK4)
% 11.75/2.00      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK4,X0)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_1715]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_4872,plain,
% 11.75/2.00      ( r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4)
% 11.75/2.00      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK4,sK3)),sK4)
% 11.75/2.00      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK4,sK3)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_2867]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_2720,plain,
% 11.75/2.00      ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),X0)
% 11.75/2.00      | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2))
% 11.75/2.00      | ~ r1_tarski(X0,u1_struct_0(sK2)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_4578,plain,
% 11.75/2.00      ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2))
% 11.75/2.00      | ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),sK4)
% 11.75/2.00      | ~ r1_tarski(sK4,u1_struct_0(sK2)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_2720]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_2754,plain,
% 11.75/2.00      ( r1_tarski(k1_setfam_1(k2_tarski(sK3,sK4)),sK3) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_0,plain,
% 11.75/2.00      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 11.75/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_2297,plain,
% 11.75/2.00      ( k1_setfam_1(k2_tarski(sK4,sK3)) = k1_setfam_1(k2_tarski(sK3,sK4)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_0]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_889,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1587,plain,
% 11.75/2.00      ( X0 != X1
% 11.75/2.00      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != X1
% 11.75/2.00      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) = X0 ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_889]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1742,plain,
% 11.75/2.00      ( X0 != k1_setfam_1(k2_tarski(sK3,sK4))
% 11.75/2.00      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) = X0
% 11.75/2.00      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK3,sK4)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_1587]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1900,plain,
% 11.75/2.00      ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k1_setfam_1(k2_tarski(sK4,sK3))
% 11.75/2.00      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) != k1_setfam_1(k2_tarski(sK3,sK4))
% 11.75/2.00      | k1_setfam_1(k2_tarski(sK4,sK3)) != k1_setfam_1(k2_tarski(sK3,sK4)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_1742]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_2,plain,
% 11.75/2.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.75/2.00      inference(cnf_transformation,[],[f33]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1425,plain,
% 11.75/2.00      ( r2_hidden(sK0(X0,u1_struct_0(sK2)),X0)
% 11.75/2.00      | r1_tarski(X0,u1_struct_0(sK2)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1801,plain,
% 11.75/2.00      ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),k9_subset_1(u1_struct_0(sK2),sK3,sK4))
% 11.75/2.00      | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_1425]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1,plain,
% 11.75/2.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.75/2.00      inference(cnf_transformation,[],[f34]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1424,plain,
% 11.75/2.00      ( ~ r2_hidden(sK0(X0,u1_struct_0(sK2)),u1_struct_0(sK2))
% 11.75/2.00      | r1_tarski(X0,u1_struct_0(sK2)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1803,plain,
% 11.75/2.00      ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)),u1_struct_0(sK2))
% 11.75/2.00      | r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_1424]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_17,negated_conjecture,
% 11.75/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 11.75/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1331,plain,
% 11.75/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 11.75/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_13,plain,
% 11.75/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.75/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1334,plain,
% 11.75/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.75/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.75/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1773,plain,
% 11.75/2.00      ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
% 11.75/2.00      inference(superposition,[status(thm)],[c_1331,c_1334]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1775,plain,
% 11.75/2.00      ( r1_tarski(sK4,u1_struct_0(sK2)) ),
% 11.75/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_1773]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_11,plain,
% 11.75/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.75/2.00      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 11.75/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_12,plain,
% 11.75/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.75/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_146,plain,
% 11.75/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.75/2.00      inference(prop_impl,[status(thm)],[c_12]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_147,plain,
% 11.75/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.75/2.00      inference(renaming,[status(thm)],[c_146]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_184,plain,
% 11.75/2.00      ( ~ r1_tarski(X0,X1)
% 11.75/2.00      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 11.75/2.00      inference(bin_hyper_res,[status(thm)],[c_11,c_147]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1690,plain,
% 11.75/2.00      ( ~ r1_tarski(sK4,u1_struct_0(sK2))
% 11.75/2.00      | k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k1_setfam_1(k2_tarski(sK3,sK4)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_184]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1691,plain,
% 11.75/2.00      ( k9_subset_1(u1_struct_0(sK2),sK3,sK4) = k1_setfam_1(k2_tarski(sK3,sK4))
% 11.75/2.00      | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top ),
% 11.75/2.00      inference(predicate_to_equality,[status(thm)],[c_1690]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1386,plain,
% 11.75/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.75/2.00      | ~ r1_tarski(X0,u1_struct_0(sK2)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_12]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1675,plain,
% 11.75/2.00      ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 11.75/2.00      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),u1_struct_0(sK2)) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_1386]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_14,plain,
% 11.75/2.00      ( ~ v2_tex_2(X0,X1)
% 11.75/2.00      | v2_tex_2(X2,X1)
% 11.75/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.00      | ~ r1_tarski(X2,X0)
% 11.75/2.00      | ~ l1_pre_topc(X1) ),
% 11.75/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_19,negated_conjecture,
% 11.75/2.00      ( l1_pre_topc(sK2) ),
% 11.75/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_258,plain,
% 11.75/2.00      ( ~ v2_tex_2(X0,X1)
% 11.75/2.00      | v2_tex_2(X2,X1)
% 11.75/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/2.00      | ~ r1_tarski(X2,X0)
% 11.75/2.00      | sK2 != X1 ),
% 11.75/2.00      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_259,plain,
% 11.75/2.00      ( ~ v2_tex_2(X0,sK2)
% 11.75/2.00      | v2_tex_2(X1,sK2)
% 11.75/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.75/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.75/2.00      | ~ r1_tarski(X1,X0) ),
% 11.75/2.00      inference(unflattening,[status(thm)],[c_258]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1503,plain,
% 11.75/2.00      ( v2_tex_2(X0,sK2)
% 11.75/2.00      | ~ v2_tex_2(sK3,sK2)
% 11.75/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.75/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.75/2.00      | ~ r1_tarski(X0,sK3) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_259]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1611,plain,
% 11.75/2.00      ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
% 11.75/2.00      | ~ v2_tex_2(sK3,sK2)
% 11.75/2.00      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 11.75/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.75/2.00      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK3) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_1503]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1374,plain,
% 11.75/2.00      ( v2_tex_2(X0,sK2)
% 11.75/2.00      | ~ v2_tex_2(sK4,sK2)
% 11.75/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.75/2.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.75/2.00      | ~ r1_tarski(X0,sK4) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_259]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_1599,plain,
% 11.75/2.00      ( v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2)
% 11.75/2.00      | ~ v2_tex_2(sK4,sK2)
% 11.75/2.00      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 11.75/2.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.75/2.00      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK4) ),
% 11.75/2.00      inference(instantiation,[status(thm)],[c_1374]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_15,negated_conjecture,
% 11.75/2.00      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK2),sK3,sK4),sK2) ),
% 11.75/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_16,negated_conjecture,
% 11.75/2.00      ( v2_tex_2(sK4,sK2) | v2_tex_2(sK3,sK2) ),
% 11.75/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(c_18,negated_conjecture,
% 11.75/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 11.75/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.75/2.00  
% 11.75/2.00  cnf(contradiction,plain,
% 11.75/2.00      ( $false ),
% 11.75/2.00      inference(minisat,
% 11.75/2.00                [status(thm)],
% 11.75/2.00                [c_35222,c_21461,c_10276,c_4872,c_4578,c_2754,c_2297,
% 11.75/2.00                 c_1900,c_1801,c_1803,c_1775,c_1773,c_1691,c_1675,c_1611,
% 11.75/2.00                 c_1599,c_15,c_16,c_17,c_18]) ).
% 11.75/2.00  
% 11.75/2.00  
% 11.75/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.75/2.00  
% 11.75/2.00  ------                               Statistics
% 11.75/2.00  
% 11.75/2.00  ------ General
% 11.75/2.00  
% 11.75/2.00  abstr_ref_over_cycles:                  0
% 11.75/2.00  abstr_ref_under_cycles:                 0
% 11.75/2.00  gc_basic_clause_elim:                   0
% 11.75/2.00  forced_gc_time:                         0
% 11.75/2.00  parsing_time:                           0.008
% 11.75/2.00  unif_index_cands_time:                  0.
% 11.75/2.00  unif_index_add_time:                    0.
% 11.75/2.00  orderings_time:                         0.
% 11.75/2.00  out_proof_time:                         0.011
% 11.75/2.00  total_time:                             1.209
% 11.75/2.00  num_of_symbols:                         46
% 11.75/2.00  num_of_terms:                           36970
% 11.75/2.00  
% 11.75/2.00  ------ Preprocessing
% 11.75/2.00  
% 11.75/2.00  num_of_splits:                          0
% 11.75/2.00  num_of_split_atoms:                     0
% 11.75/2.00  num_of_reused_defs:                     0
% 11.75/2.00  num_eq_ax_congr_red:                    24
% 11.75/2.00  num_of_sem_filtered_clauses:            1
% 11.75/2.00  num_of_subtypes:                        0
% 11.75/2.00  monotx_restored_types:                  0
% 11.75/2.00  sat_num_of_epr_types:                   0
% 11.75/2.00  sat_num_of_non_cyclic_types:            0
% 11.75/2.00  sat_guarded_non_collapsed_types:        0
% 11.75/2.00  num_pure_diseq_elim:                    0
% 11.75/2.00  simp_replaced_by:                       0
% 11.75/2.00  res_preprocessed:                       98
% 11.75/2.00  prep_upred:                             0
% 11.75/2.00  prep_unflattend:                        41
% 11.75/2.00  smt_new_axioms:                         0
% 11.75/2.00  pred_elim_cands:                        4
% 11.75/2.00  pred_elim:                              1
% 11.75/2.00  pred_elim_cl:                           1
% 11.75/2.00  pred_elim_cycles:                       3
% 11.75/2.00  merged_defs:                            8
% 11.75/2.00  merged_defs_ncl:                        0
% 11.75/2.00  bin_hyper_res:                          9
% 11.75/2.00  prep_cycles:                            4
% 11.75/2.00  pred_elim_time:                         0.004
% 11.75/2.00  splitting_time:                         0.
% 11.75/2.00  sem_filter_time:                        0.
% 11.75/2.00  monotx_time:                            0.
% 11.75/2.00  subtype_inf_time:                       0.
% 11.75/2.00  
% 11.75/2.00  ------ Problem properties
% 11.75/2.00  
% 11.75/2.00  clauses:                                19
% 11.75/2.00  conjectures:                            4
% 11.75/2.00  epr:                                    2
% 11.75/2.00  horn:                                   15
% 11.75/2.00  ground:                                 4
% 11.75/2.00  unary:                                  5
% 11.75/2.00  binary:                                 8
% 11.75/2.00  lits:                                   42
% 11.75/2.00  lits_eq:                                5
% 11.75/2.00  fd_pure:                                0
% 11.75/2.00  fd_pseudo:                              0
% 11.75/2.00  fd_cond:                                0
% 11.75/2.00  fd_pseudo_cond:                         3
% 11.75/2.00  ac_symbols:                             0
% 11.75/2.00  
% 11.75/2.00  ------ Propositional Solver
% 11.75/2.00  
% 11.75/2.00  prop_solver_calls:                      33
% 11.75/2.00  prop_fast_solver_calls:                 1345
% 11.75/2.00  smt_solver_calls:                       0
% 11.75/2.00  smt_fast_solver_calls:                  0
% 11.75/2.00  prop_num_of_clauses:                    15298
% 11.75/2.00  prop_preprocess_simplified:             17890
% 11.75/2.00  prop_fo_subsumed:                       89
% 11.75/2.00  prop_solver_time:                       0.
% 11.75/2.00  smt_solver_time:                        0.
% 11.75/2.00  smt_fast_solver_time:                   0.
% 11.75/2.00  prop_fast_solver_time:                  0.
% 11.75/2.00  prop_unsat_core_time:                   0.001
% 11.75/2.00  
% 11.75/2.00  ------ QBF
% 11.75/2.00  
% 11.75/2.00  qbf_q_res:                              0
% 11.75/2.00  qbf_num_tautologies:                    0
% 11.75/2.00  qbf_prep_cycles:                        0
% 11.75/2.00  
% 11.75/2.00  ------ BMC1
% 11.75/2.00  
% 11.75/2.00  bmc1_current_bound:                     -1
% 11.75/2.00  bmc1_last_solved_bound:                 -1
% 11.75/2.00  bmc1_unsat_core_size:                   -1
% 11.75/2.00  bmc1_unsat_core_parents_size:           -1
% 11.75/2.00  bmc1_merge_next_fun:                    0
% 11.75/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.75/2.00  
% 11.75/2.00  ------ Instantiation
% 11.75/2.00  
% 11.75/2.00  inst_num_of_clauses:                    2041
% 11.75/2.00  inst_num_in_passive:                    1177
% 11.75/2.00  inst_num_in_active:                     816
% 11.75/2.00  inst_num_in_unprocessed:                47
% 11.75/2.00  inst_num_of_loops:                      1162
% 11.75/2.00  inst_num_of_learning_restarts:          0
% 11.75/2.00  inst_num_moves_active_passive:          341
% 11.75/2.00  inst_lit_activity:                      0
% 11.75/2.00  inst_lit_activity_moves:                0
% 11.75/2.00  inst_num_tautologies:                   0
% 11.75/2.00  inst_num_prop_implied:                  0
% 11.75/2.00  inst_num_existing_simplified:           0
% 11.75/2.00  inst_num_eq_res_simplified:             0
% 11.75/2.00  inst_num_child_elim:                    0
% 11.75/2.00  inst_num_of_dismatching_blockings:      1543
% 11.75/2.00  inst_num_of_non_proper_insts:           2418
% 11.75/2.00  inst_num_of_duplicates:                 0
% 11.75/2.00  inst_inst_num_from_inst_to_res:         0
% 11.75/2.00  inst_dismatching_checking_time:         0.
% 11.75/2.00  
% 11.75/2.00  ------ Resolution
% 11.75/2.00  
% 11.75/2.00  res_num_of_clauses:                     0
% 11.75/2.00  res_num_in_passive:                     0
% 11.75/2.00  res_num_in_active:                      0
% 11.75/2.00  res_num_of_loops:                       102
% 11.75/2.00  res_forward_subset_subsumed:            359
% 11.75/2.00  res_backward_subset_subsumed:           0
% 11.75/2.00  res_forward_subsumed:                   0
% 11.75/2.00  res_backward_subsumed:                  0
% 11.75/2.00  res_forward_subsumption_resolution:     0
% 11.75/2.00  res_backward_subsumption_resolution:    0
% 11.75/2.00  res_clause_to_clause_subsumption:       79778
% 11.75/2.00  res_orphan_elimination:                 0
% 11.75/2.00  res_tautology_del:                      273
% 11.75/2.00  res_num_eq_res_simplified:              0
% 11.75/2.00  res_num_sel_changes:                    0
% 11.75/2.00  res_moves_from_active_to_pass:          0
% 11.75/2.00  
% 11.75/2.00  ------ Superposition
% 11.75/2.00  
% 11.75/2.00  sup_time_total:                         0.
% 11.75/2.00  sup_time_generating:                    0.
% 11.75/2.00  sup_time_sim_full:                      0.
% 11.75/2.00  sup_time_sim_immed:                     0.
% 11.75/2.00  
% 11.75/2.00  sup_num_of_clauses:                     2868
% 11.75/2.00  sup_num_in_active:                      169
% 11.75/2.00  sup_num_in_passive:                     2699
% 11.75/2.00  sup_num_of_loops:                       232
% 11.75/2.00  sup_fw_superposition:                   6209
% 11.75/2.00  sup_bw_superposition:                   5667
% 11.75/2.00  sup_immediate_simplified:               345
% 11.75/2.00  sup_given_eliminated:                   0
% 11.75/2.00  comparisons_done:                       0
% 11.75/2.00  comparisons_avoided:                    0
% 11.75/2.00  
% 11.75/2.00  ------ Simplifications
% 11.75/2.00  
% 11.75/2.00  
% 11.75/2.00  sim_fw_subset_subsumed:                 34
% 11.75/2.00  sim_bw_subset_subsumed:                 3
% 11.75/2.00  sim_fw_subsumed:                        257
% 11.75/2.00  sim_bw_subsumed:                        23
% 11.75/2.00  sim_fw_subsumption_res:                 0
% 11.75/2.00  sim_bw_subsumption_res:                 0
% 11.75/2.00  sim_tautology_del:                      24
% 11.75/2.00  sim_eq_tautology_del:                   0
% 11.75/2.00  sim_eq_res_simp:                        2
% 11.75/2.00  sim_fw_demodulated:                     0
% 11.75/2.00  sim_bw_demodulated:                     92
% 11.75/2.00  sim_light_normalised:                   0
% 11.75/2.00  sim_joinable_taut:                      0
% 11.75/2.00  sim_joinable_simp:                      0
% 11.75/2.00  sim_ac_normalised:                      0
% 11.75/2.00  sim_smt_subsumption:                    0
% 11.75/2.00  
%------------------------------------------------------------------------------
