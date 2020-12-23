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
% DateTime   : Thu Dec  3 12:25:48 EST 2020

% Result     : Theorem 7.15s
% Output     : CNFRefutation 7.15s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 694 expanded)
%              Number of clauses        :  103 ( 259 expanded)
%              Number of leaves         :   20 ( 178 expanded)
%              Depth                    :   22
%              Number of atoms          :  393 (2756 expanded)
%              Number of equality atoms :   69 ( 141 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & ( v2_tex_2(X2,X0)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK3),X0)
        & ( v2_tex_2(sK3,X0)
          | v2_tex_2(X1,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),sK2,X2),X0)
            & ( v2_tex_2(X2,X0)
              | v2_tex_2(sK2,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
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
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK1),X1,X2),sK1)
              & ( v2_tex_2(X2,sK1)
                | v2_tex_2(X1,sK1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1)
    & ( v2_tex_2(sK3,sK1)
      | v2_tex_2(sK2,sK1) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f25,f24,f23])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f43,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,
    ( v2_tex_2(sK3,sK1)
    | v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f31,f33])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f32,f33,f33])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_800,plain,
    ( ~ r2_hidden(X0_47,X0_43)
    | r2_hidden(X0_47,X1_43)
    | ~ r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_799,plain,
    ( r1_tarski(k4_xboole_0(X0_43,X1_43),X0_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_4869,plain,
    ( r2_hidden(X0_47,X0_43)
    | ~ r2_hidden(X0_47,k4_xboole_0(X0_43,X1_43)) ),
    inference(resolution,[status(thm)],[c_800,c_799])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_801,plain,
    ( r2_hidden(sK0(X0_43,X1_43),X0_43)
    | r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_10409,plain,
    ( r2_hidden(sK0(k4_xboole_0(X0_43,X1_43),X2_43),X0_43)
    | r1_tarski(k4_xboole_0(X0_43,X1_43),X2_43) ),
    inference(resolution,[status(thm)],[c_4869,c_801])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_795,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_792,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1347,plain,
    ( r1_tarski(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_795,c_792])).

cnf(c_4865,plain,
    ( r2_hidden(X0_47,u1_struct_0(sK1))
    | ~ r2_hidden(X0_47,sK3) ),
    inference(resolution,[status(thm)],[c_800,c_1347])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_802,plain,
    ( ~ r2_hidden(sK0(X0_43,X1_43),X1_43)
    | r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_4881,plain,
    ( ~ r2_hidden(sK0(X0_43,u1_struct_0(sK1)),sK3)
    | r1_tarski(X0_43,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_4865,c_802])).

cnf(c_20076,plain,
    ( r1_tarski(k4_xboole_0(sK3,X0_43),u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_10409,c_4881])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_796,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | ~ r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_9,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_186,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_187,plain,
    ( ~ v2_tex_2(X0,sK1)
    | v2_tex_2(X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_186])).

cnf(c_789,plain,
    ( ~ v2_tex_2(X0_43,sK1)
    | v2_tex_2(X1_43,sK1)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_187])).

cnf(c_1778,plain,
    ( ~ v2_tex_2(X0_43,sK1)
    | v2_tex_2(X1_43,sK1)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1_43,X0_43)
    | ~ r1_tarski(X1_43,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_796,c_789])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_791,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1892,plain,
    ( v2_tex_2(X0_43,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ r1_tarski(X0_43,u1_struct_0(sK1))
    | ~ r1_tarski(X0_43,sK2) ),
    inference(resolution,[status(thm)],[c_1778,c_791])).

cnf(c_808,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_804,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_2631,plain,
    ( X0_43 != X1_43
    | X1_43 = X0_43 ),
    inference(resolution,[status(thm)],[c_808,c_804])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_102,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_103,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_102])).

cnf(c_129,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_103])).

cnf(c_790,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | k4_xboole_0(X2_43,k4_xboole_0(X2_43,X0_43)) = k9_subset_1(X1_43,X2_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_129])).

cnf(c_4563,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | k9_subset_1(X1_43,X2_43,X0_43) = k4_xboole_0(X2_43,k4_xboole_0(X2_43,X0_43)) ),
    inference(resolution,[status(thm)],[c_2631,c_790])).

cnf(c_810,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(X2_43,X1_43)
    | X2_43 != X0_43 ),
    theory(equality)).

cnf(c_5192,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(k9_subset_1(X1_43,X2_43,X0_43),X3_43)
    | ~ r1_tarski(k4_xboole_0(X2_43,k4_xboole_0(X2_43,X0_43)),X3_43) ),
    inference(resolution,[status(thm)],[c_4563,c_810])).

cnf(c_5444,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(k9_subset_1(X1_43,X2_43,X0_43),X2_43) ),
    inference(resolution,[status(thm)],[c_5192,c_799])).

cnf(c_8369,plain,
    ( v2_tex_2(k9_subset_1(X0_43,u1_struct_0(sK1),X1_43),sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ r1_tarski(X1_43,X0_43)
    | ~ r1_tarski(k9_subset_1(X0_43,u1_struct_0(sK1),X1_43),sK2) ),
    inference(resolution,[status(thm)],[c_1892,c_5444])).

cnf(c_813,plain,
    ( X0_43 != X1_43
    | X2_43 != X3_43
    | X4_43 != X5_43
    | k9_subset_1(X0_43,X2_43,X4_43) = k9_subset_1(X1_43,X3_43,X5_43) ),
    theory(equality)).

cnf(c_817,plain,
    ( ~ v2_tex_2(X0_43,X0_44)
    | v2_tex_2(X1_43,X0_44)
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_3354,plain,
    ( ~ v2_tex_2(k9_subset_1(X0_43,X1_43,X2_43),X0_44)
    | v2_tex_2(k9_subset_1(X3_43,X4_43,X5_43),X0_44)
    | X4_43 != X1_43
    | X5_43 != X2_43
    | X3_43 != X0_43 ),
    inference(resolution,[status(thm)],[c_813,c_817])).

cnf(c_8796,plain,
    ( v2_tex_2(k9_subset_1(X0_43,X1_43,X2_43),sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ r1_tarski(X3_43,X4_43)
    | ~ r1_tarski(k9_subset_1(X4_43,u1_struct_0(sK1),X3_43),sK2)
    | X2_43 != X3_43
    | X0_43 != X4_43
    | X1_43 != u1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_8369,c_3354])).

cnf(c_10,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1349,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(resolution,[status(thm)],[c_795,c_791])).

cnf(c_1586,plain,
    ( ~ v2_tex_2(X0_43,sK1)
    | v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X0_43) ),
    inference(instantiation,[status(thm)],[c_789])).

cnf(c_1588,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_1826,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_1897,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,sK3) = k9_subset_1(u1_struct_0(sK1),sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_1699,plain,
    ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X0_43),k9_subset_1(u1_struct_0(sK1),sK2,sK3))
    | r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X0_43) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_2148,plain,
    ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),k9_subset_1(u1_struct_0(sK1),sK2,sK3))
    | r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1699])).

cnf(c_1691,plain,
    ( X0_43 != X1_43
    | k9_subset_1(u1_struct_0(sK1),sK2,sK3) != X1_43
    | k9_subset_1(u1_struct_0(sK1),sK2,sK3) = X0_43 ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_1896,plain,
    ( X0_43 != k9_subset_1(u1_struct_0(sK1),sK2,sK3)
    | k9_subset_1(u1_struct_0(sK1),sK2,sK3) = X0_43
    | k9_subset_1(u1_struct_0(sK1),sK2,sK3) != k9_subset_1(u1_struct_0(sK1),sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1691])).

cnf(c_2239,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,sK3) != k9_subset_1(u1_struct_0(sK1),sK2,sK3)
    | k9_subset_1(u1_struct_0(sK1),sK2,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k9_subset_1(u1_struct_0(sK1),sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1896])).

cnf(c_2240,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK1))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k9_subset_1(u1_struct_0(sK1),sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_1709,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X1_43)
    | k9_subset_1(u1_struct_0(sK1),sK2,sK3) != X0_43 ),
    inference(instantiation,[status(thm)],[c_810])).

cnf(c_2529,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X0_43)
    | ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0_43)
    | k9_subset_1(u1_struct_0(sK1),sK2,sK3) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1709])).

cnf(c_2540,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK2)
    | ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK2)
    | k9_subset_1(u1_struct_0(sK1),sK2,sK3) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2529])).

cnf(c_2893,plain,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_2392,plain,
    ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X0_43),X1_43)
    | ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X0_43),k9_subset_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X1_43) ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_4171,plain,
    ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),X0_43)
    | ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),k9_subset_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X0_43) ),
    inference(instantiation,[status(thm)],[c_2392])).

cnf(c_4173,plain,
    ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),k9_subset_1(u1_struct_0(sK1),sK2,sK3))
    | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),sK2)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_4171])).

cnf(c_7376,plain,
    ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),u1_struct_0(sK1))
    | r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_7368,plain,
    ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),X0_43)
    | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),X1_43)
    | ~ r1_tarski(X0_43,X1_43) ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_13791,plain,
    ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),X0_43)
    | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ r1_tarski(X0_43,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_7368])).

cnf(c_13793,plain,
    ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_13791])).

cnf(c_14300,plain,
    ( ~ v2_tex_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8796,c_13,c_10,c_1347,c_1349,c_1588,c_1826,c_1897,c_2148,c_2239,c_2240,c_2540,c_2893,c_4173,c_7376,c_13793])).

cnf(c_11,negated_conjecture,
    ( v2_tex_2(sK3,sK1)
    | v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_793,negated_conjecture,
    ( v2_tex_2(sK3,sK1)
    | v2_tex_2(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_14580,plain,
    ( v2_tex_2(sK3,sK1) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_14300,c_793])).

cnf(c_1890,plain,
    ( v2_tex_2(X0_43,sK1)
    | ~ v2_tex_2(sK3,sK1)
    | ~ r1_tarski(X0_43,u1_struct_0(sK1))
    | ~ r1_tarski(X0_43,sK3) ),
    inference(resolution,[status(thm)],[c_1778,c_792])).

cnf(c_14606,plain,
    ( v2_tex_2(X0_43,sK1)
    | ~ r1_tarski(X0_43,u1_struct_0(sK1))
    | ~ r1_tarski(X0_43,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_14580,c_1890])).

cnf(c_20259,plain,
    ( v2_tex_2(k4_xboole_0(sK3,X0_43),sK1)
    | ~ r1_tarski(k4_xboole_0(sK3,X0_43),sK3) ),
    inference(resolution,[status(thm)],[c_20076,c_14606])).

cnf(c_1311,plain,
    ( v2_tex_2(X0_43,sK1)
    | ~ v2_tex_2(sK3,sK1)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0_43,sK3) ),
    inference(instantiation,[status(thm)],[c_789])).

cnf(c_1481,plain,
    ( v2_tex_2(k4_xboole_0(sK3,X0_43),sK1)
    | ~ v2_tex_2(sK3,sK1)
    | ~ m1_subset_1(k4_xboole_0(sK3,X0_43),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k4_xboole_0(sK3,X0_43),sK3) ),
    inference(instantiation,[status(thm)],[c_1311])).

cnf(c_1482,plain,
    ( r1_tarski(k4_xboole_0(sK3,X0_43),sK3) ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_1596,plain,
    ( m1_subset_1(k4_xboole_0(sK3,X0_43),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k4_xboole_0(sK3,X0_43),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_20279,plain,
    ( v2_tex_2(k4_xboole_0(sK3,X0_43),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20259,c_13,c_12,c_11,c_10,c_1347,c_1349,c_1481,c_1482,c_1588,c_1596,c_1826,c_1897,c_2148,c_2239,c_2240,c_2540,c_2893,c_4173,c_7376,c_13793,c_20076])).

cnf(c_6,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_797,plain,
    ( k1_setfam_1(k1_enumset1(X0_43,X0_43,X1_43)) = k4_xboole_0(X0_43,k4_xboole_0(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_6036,plain,
    ( ~ v2_tex_2(k4_xboole_0(X0_43,k4_xboole_0(X0_43,X1_43)),X0_44)
    | v2_tex_2(k1_setfam_1(k1_enumset1(X0_43,X0_43,X1_43)),X0_44) ),
    inference(resolution,[status(thm)],[c_797,c_817])).

cnf(c_20298,plain,
    ( v2_tex_2(k1_setfam_1(k1_enumset1(sK3,sK3,X0_43)),sK1) ),
    inference(resolution,[status(thm)],[c_20279,c_6036])).

cnf(c_816,plain,
    ( X0_46 != X1_46
    | k1_setfam_1(X0_46) = k1_setfam_1(X1_46) ),
    theory(equality)).

cnf(c_2330,plain,
    ( ~ v2_tex_2(k1_setfam_1(X0_46),X0_44)
    | v2_tex_2(k1_setfam_1(X1_46),X0_44)
    | X1_46 != X0_46 ),
    inference(resolution,[status(thm)],[c_816,c_817])).

cnf(c_4,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_798,plain,
    ( k1_enumset1(X0_43,X0_43,X1_43) = k1_enumset1(X1_43,X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_7311,plain,
    ( ~ v2_tex_2(k1_setfam_1(k1_enumset1(X0_43,X0_43,X1_43)),X0_44)
    | v2_tex_2(k1_setfam_1(k1_enumset1(X1_43,X1_43,X0_43)),X0_44) ),
    inference(resolution,[status(thm)],[c_2330,c_798])).

cnf(c_21231,plain,
    ( v2_tex_2(k1_setfam_1(k1_enumset1(X0_43,X0_43,sK3)),sK1) ),
    inference(resolution,[status(thm)],[c_20298,c_7311])).

cnf(c_21233,plain,
    ( v2_tex_2(k1_setfam_1(k1_enumset1(sK2,sK2,sK3)),sK1) ),
    inference(instantiation,[status(thm)],[c_21231])).

cnf(c_1210,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_1207,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
    | r1_tarski(X0_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_2295,plain,
    ( r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1210,c_1207])).

cnf(c_1212,plain,
    ( k4_xboole_0(X0_43,k4_xboole_0(X0_43,X1_43)) = k9_subset_1(X2_43,X0_43,X1_43)
    | r1_tarski(X1_43,X2_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_1246,plain,
    ( k1_setfam_1(k1_enumset1(X0_43,X0_43,X1_43)) = k9_subset_1(X2_43,X0_43,X1_43)
    | r1_tarski(X1_43,X2_43) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1212,c_797])).

cnf(c_3220,plain,
    ( k1_setfam_1(k1_enumset1(X0_43,X0_43,sK3)) = k9_subset_1(u1_struct_0(sK1),X0_43,sK3) ),
    inference(superposition,[status(thm)],[c_2295,c_1246])).

cnf(c_794,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1208,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_3743,plain,
    ( v2_tex_2(k1_setfam_1(k1_enumset1(sK2,sK2,sK3)),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3220,c_1208])).

cnf(c_3744,plain,
    ( ~ v2_tex_2(k1_setfam_1(k1_enumset1(sK2,sK2,sK3)),sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3743])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21233,c_3744])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.15/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.15/1.50  
% 7.15/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.15/1.50  
% 7.15/1.50  ------  iProver source info
% 7.15/1.50  
% 7.15/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.15/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.15/1.50  git: non_committed_changes: false
% 7.15/1.50  git: last_make_outside_of_git: false
% 7.15/1.50  
% 7.15/1.50  ------ 
% 7.15/1.50  ------ Parsing...
% 7.15/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.15/1.50  
% 7.15/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.15/1.50  
% 7.15/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.15/1.50  
% 7.15/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.15/1.50  ------ Proving...
% 7.15/1.50  ------ Problem Properties 
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  clauses                                 14
% 7.15/1.50  conjectures                             4
% 7.15/1.50  EPR                                     2
% 7.15/1.50  Horn                                    12
% 7.15/1.50  unary                                   6
% 7.15/1.50  binary                                  6
% 7.15/1.50  lits                                    26
% 7.15/1.50  lits eq                                 3
% 7.15/1.50  fd_pure                                 0
% 7.15/1.50  fd_pseudo                               0
% 7.15/1.50  fd_cond                                 0
% 7.15/1.50  fd_pseudo_cond                          0
% 7.15/1.50  AC symbols                              0
% 7.15/1.50  
% 7.15/1.50  ------ Input Options Time Limit: Unbounded
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  ------ 
% 7.15/1.50  Current options:
% 7.15/1.50  ------ 
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  ------ Proving...
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  % SZS status Theorem for theBenchmark.p
% 7.15/1.50  
% 7.15/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.15/1.50  
% 7.15/1.50  fof(f1,axiom,(
% 7.15/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f12,plain,(
% 7.15/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.15/1.50    inference(ennf_transformation,[],[f1])).
% 7.15/1.50  
% 7.15/1.50  fof(f18,plain,(
% 7.15/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.15/1.50    inference(nnf_transformation,[],[f12])).
% 7.15/1.50  
% 7.15/1.50  fof(f19,plain,(
% 7.15/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.15/1.50    inference(rectify,[],[f18])).
% 7.15/1.50  
% 7.15/1.50  fof(f20,plain,(
% 7.15/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.15/1.50    introduced(choice_axiom,[])).
% 7.15/1.50  
% 7.15/1.50  fof(f21,plain,(
% 7.15/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.15/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 7.15/1.50  
% 7.15/1.50  fof(f27,plain,(
% 7.15/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f21])).
% 7.15/1.50  
% 7.15/1.50  fof(f2,axiom,(
% 7.15/1.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f30,plain,(
% 7.15/1.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f2])).
% 7.15/1.50  
% 7.15/1.50  fof(f28,plain,(
% 7.15/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f21])).
% 7.15/1.50  
% 7.15/1.50  fof(f8,axiom,(
% 7.15/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f22,plain,(
% 7.15/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.15/1.50    inference(nnf_transformation,[],[f8])).
% 7.15/1.50  
% 7.15/1.50  fof(f36,plain,(
% 7.15/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f22])).
% 7.15/1.50  
% 7.15/1.50  fof(f10,conjecture,(
% 7.15/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f11,negated_conjecture,(
% 7.15/1.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.15/1.50    inference(negated_conjecture,[],[f10])).
% 7.15/1.50  
% 7.15/1.50  fof(f16,plain,(
% 7.15/1.50    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.15/1.50    inference(ennf_transformation,[],[f11])).
% 7.15/1.50  
% 7.15/1.50  fof(f17,plain,(
% 7.15/1.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.15/1.50    inference(flattening,[],[f16])).
% 7.15/1.50  
% 7.15/1.50  fof(f25,plain,(
% 7.15/1.50    ( ! [X0,X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK3),X0) & (v2_tex_2(sK3,X0) | v2_tex_2(X1,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.15/1.50    introduced(choice_axiom,[])).
% 7.15/1.50  
% 7.15/1.50  fof(f24,plain,(
% 7.15/1.50    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),sK2,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(sK2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.15/1.50    introduced(choice_axiom,[])).
% 7.15/1.50  
% 7.15/1.50  fof(f23,plain,(
% 7.15/1.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK1),X1,X2),sK1) & (v2_tex_2(X2,sK1) | v2_tex_2(X1,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1))),
% 7.15/1.50    introduced(choice_axiom,[])).
% 7.15/1.50  
% 7.15/1.50  fof(f26,plain,(
% 7.15/1.50    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1) & (v2_tex_2(sK3,sK1) | v2_tex_2(sK2,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1)),
% 7.15/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f25,f24,f23])).
% 7.15/1.50  
% 7.15/1.50  fof(f41,plain,(
% 7.15/1.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.15/1.50    inference(cnf_transformation,[],[f26])).
% 7.15/1.50  
% 7.15/1.50  fof(f29,plain,(
% 7.15/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f21])).
% 7.15/1.50  
% 7.15/1.50  fof(f37,plain,(
% 7.15/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f22])).
% 7.15/1.50  
% 7.15/1.50  fof(f9,axiom,(
% 7.15/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f14,plain,(
% 7.15/1.50    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.15/1.50    inference(ennf_transformation,[],[f9])).
% 7.15/1.50  
% 7.15/1.50  fof(f15,plain,(
% 7.15/1.50    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.15/1.50    inference(flattening,[],[f14])).
% 7.15/1.50  
% 7.15/1.50  fof(f38,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f15])).
% 7.15/1.50  
% 7.15/1.50  fof(f39,plain,(
% 7.15/1.50    l1_pre_topc(sK1)),
% 7.15/1.50    inference(cnf_transformation,[],[f26])).
% 7.15/1.50  
% 7.15/1.50  fof(f40,plain,(
% 7.15/1.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.15/1.50    inference(cnf_transformation,[],[f26])).
% 7.15/1.50  
% 7.15/1.50  fof(f6,axiom,(
% 7.15/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f13,plain,(
% 7.15/1.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.15/1.50    inference(ennf_transformation,[],[f6])).
% 7.15/1.50  
% 7.15/1.50  fof(f34,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f13])).
% 7.15/1.50  
% 7.15/1.50  fof(f3,axiom,(
% 7.15/1.50    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f31,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f3])).
% 7.15/1.50  
% 7.15/1.50  fof(f45,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.15/1.50    inference(definition_unfolding,[],[f34,f31])).
% 7.15/1.50  
% 7.15/1.50  fof(f43,plain,(
% 7.15/1.50    ~v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1)),
% 7.15/1.50    inference(cnf_transformation,[],[f26])).
% 7.15/1.50  
% 7.15/1.50  fof(f42,plain,(
% 7.15/1.50    v2_tex_2(sK3,sK1) | v2_tex_2(sK2,sK1)),
% 7.15/1.50    inference(cnf_transformation,[],[f26])).
% 7.15/1.50  
% 7.15/1.50  fof(f7,axiom,(
% 7.15/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f35,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f7])).
% 7.15/1.50  
% 7.15/1.50  fof(f5,axiom,(
% 7.15/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f33,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f5])).
% 7.15/1.50  
% 7.15/1.50  fof(f46,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 7.15/1.50    inference(definition_unfolding,[],[f35,f31,f33])).
% 7.15/1.50  
% 7.15/1.50  fof(f4,axiom,(
% 7.15/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.15/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f32,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f4])).
% 7.15/1.50  
% 7.15/1.50  fof(f44,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 7.15/1.50    inference(definition_unfolding,[],[f32,f33,f33])).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2,plain,
% 7.15/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.15/1.50      inference(cnf_transformation,[],[f27]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_800,plain,
% 7.15/1.50      ( ~ r2_hidden(X0_47,X0_43)
% 7.15/1.50      | r2_hidden(X0_47,X1_43)
% 7.15/1.50      | ~ r1_tarski(X0_43,X1_43) ),
% 7.15/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3,plain,
% 7.15/1.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f30]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_799,plain,
% 7.15/1.50      ( r1_tarski(k4_xboole_0(X0_43,X1_43),X0_43) ),
% 7.15/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4869,plain,
% 7.15/1.50      ( r2_hidden(X0_47,X0_43)
% 7.15/1.50      | ~ r2_hidden(X0_47,k4_xboole_0(X0_43,X1_43)) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_800,c_799]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1,plain,
% 7.15/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f28]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_801,plain,
% 7.15/1.50      ( r2_hidden(sK0(X0_43,X1_43),X0_43) | r1_tarski(X0_43,X1_43) ),
% 7.15/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_10409,plain,
% 7.15/1.50      ( r2_hidden(sK0(k4_xboole_0(X0_43,X1_43),X2_43),X0_43)
% 7.15/1.50      | r1_tarski(k4_xboole_0(X0_43,X1_43),X2_43) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_4869,c_801]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_8,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_795,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 7.15/1.50      | r1_tarski(X0_43,X1_43) ),
% 7.15/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_12,negated_conjecture,
% 7.15/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.15/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_792,negated_conjecture,
% 7.15/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.15/1.50      inference(subtyping,[status(esa)],[c_12]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1347,plain,
% 7.15/1.50      ( r1_tarski(sK3,u1_struct_0(sK1)) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_795,c_792]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4865,plain,
% 7.15/1.50      ( r2_hidden(X0_47,u1_struct_0(sK1)) | ~ r2_hidden(X0_47,sK3) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_800,c_1347]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_0,plain,
% 7.15/1.50      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f29]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_802,plain,
% 7.15/1.50      ( ~ r2_hidden(sK0(X0_43,X1_43),X1_43) | r1_tarski(X0_43,X1_43) ),
% 7.15/1.50      inference(subtyping,[status(esa)],[c_0]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4881,plain,
% 7.15/1.50      ( ~ r2_hidden(sK0(X0_43,u1_struct_0(sK1)),sK3)
% 7.15/1.50      | r1_tarski(X0_43,u1_struct_0(sK1)) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_4865,c_802]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_20076,plain,
% 7.15/1.50      ( r1_tarski(k4_xboole_0(sK3,X0_43),u1_struct_0(sK1)) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_10409,c_4881]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_796,plain,
% 7.15/1.50      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 7.15/1.50      | ~ r1_tarski(X0_43,X1_43) ),
% 7.15/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_9,plain,
% 7.15/1.50      ( ~ v2_tex_2(X0,X1)
% 7.15/1.50      | v2_tex_2(X2,X1)
% 7.15/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.15/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.15/1.50      | ~ r1_tarski(X2,X0)
% 7.15/1.50      | ~ l1_pre_topc(X1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14,negated_conjecture,
% 7.15/1.50      ( l1_pre_topc(sK1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_186,plain,
% 7.15/1.50      ( ~ v2_tex_2(X0,X1)
% 7.15/1.50      | v2_tex_2(X2,X1)
% 7.15/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.15/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.15/1.50      | ~ r1_tarski(X2,X0)
% 7.15/1.50      | sK1 != X1 ),
% 7.15/1.50      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_187,plain,
% 7.15/1.50      ( ~ v2_tex_2(X0,sK1)
% 7.15/1.50      | v2_tex_2(X1,sK1)
% 7.15/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.15/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.15/1.50      | ~ r1_tarski(X1,X0) ),
% 7.15/1.50      inference(unflattening,[status(thm)],[c_186]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_789,plain,
% 7.15/1.50      ( ~ v2_tex_2(X0_43,sK1)
% 7.15/1.50      | v2_tex_2(X1_43,sK1)
% 7.15/1.50      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.15/1.50      | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.15/1.50      | ~ r1_tarski(X1_43,X0_43) ),
% 7.15/1.50      inference(subtyping,[status(esa)],[c_187]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1778,plain,
% 7.15/1.50      ( ~ v2_tex_2(X0_43,sK1)
% 7.15/1.50      | v2_tex_2(X1_43,sK1)
% 7.15/1.50      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.15/1.50      | ~ r1_tarski(X1_43,X0_43)
% 7.15/1.50      | ~ r1_tarski(X1_43,u1_struct_0(sK1)) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_796,c_789]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_13,negated_conjecture,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.15/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_791,negated_conjecture,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.15/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1892,plain,
% 7.15/1.50      ( v2_tex_2(X0_43,sK1)
% 7.15/1.50      | ~ v2_tex_2(sK2,sK1)
% 7.15/1.50      | ~ r1_tarski(X0_43,u1_struct_0(sK1))
% 7.15/1.50      | ~ r1_tarski(X0_43,sK2) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_1778,c_791]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_808,plain,
% 7.15/1.50      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 7.15/1.50      theory(equality) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_804,plain,( X0_43 = X0_43 ),theory(equality) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2631,plain,
% 7.15/1.50      ( X0_43 != X1_43 | X1_43 = X0_43 ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_808,c_804]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.15/1.50      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_102,plain,
% 7.15/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.15/1.50      inference(prop_impl,[status(thm)],[c_7]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_103,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.15/1.50      inference(renaming,[status(thm)],[c_102]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_129,plain,
% 7.15/1.50      ( ~ r1_tarski(X0,X1)
% 7.15/1.50      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 7.15/1.50      inference(bin_hyper_res,[status(thm)],[c_5,c_103]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_790,plain,
% 7.15/1.50      ( ~ r1_tarski(X0_43,X1_43)
% 7.15/1.50      | k4_xboole_0(X2_43,k4_xboole_0(X2_43,X0_43)) = k9_subset_1(X1_43,X2_43,X0_43) ),
% 7.15/1.50      inference(subtyping,[status(esa)],[c_129]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4563,plain,
% 7.15/1.50      ( ~ r1_tarski(X0_43,X1_43)
% 7.15/1.50      | k9_subset_1(X1_43,X2_43,X0_43) = k4_xboole_0(X2_43,k4_xboole_0(X2_43,X0_43)) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_2631,c_790]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_810,plain,
% 7.15/1.50      ( ~ r1_tarski(X0_43,X1_43)
% 7.15/1.50      | r1_tarski(X2_43,X1_43)
% 7.15/1.50      | X2_43 != X0_43 ),
% 7.15/1.50      theory(equality) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5192,plain,
% 7.15/1.50      ( ~ r1_tarski(X0_43,X1_43)
% 7.15/1.50      | r1_tarski(k9_subset_1(X1_43,X2_43,X0_43),X3_43)
% 7.15/1.50      | ~ r1_tarski(k4_xboole_0(X2_43,k4_xboole_0(X2_43,X0_43)),X3_43) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_4563,c_810]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5444,plain,
% 7.15/1.50      ( ~ r1_tarski(X0_43,X1_43)
% 7.15/1.50      | r1_tarski(k9_subset_1(X1_43,X2_43,X0_43),X2_43) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_5192,c_799]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_8369,plain,
% 7.15/1.50      ( v2_tex_2(k9_subset_1(X0_43,u1_struct_0(sK1),X1_43),sK1)
% 7.15/1.50      | ~ v2_tex_2(sK2,sK1)
% 7.15/1.50      | ~ r1_tarski(X1_43,X0_43)
% 7.15/1.50      | ~ r1_tarski(k9_subset_1(X0_43,u1_struct_0(sK1),X1_43),sK2) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_1892,c_5444]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_813,plain,
% 7.15/1.50      ( X0_43 != X1_43
% 7.15/1.50      | X2_43 != X3_43
% 7.15/1.50      | X4_43 != X5_43
% 7.15/1.50      | k9_subset_1(X0_43,X2_43,X4_43) = k9_subset_1(X1_43,X3_43,X5_43) ),
% 7.15/1.50      theory(equality) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_817,plain,
% 7.15/1.50      ( ~ v2_tex_2(X0_43,X0_44)
% 7.15/1.50      | v2_tex_2(X1_43,X0_44)
% 7.15/1.50      | X1_43 != X0_43 ),
% 7.15/1.50      theory(equality) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3354,plain,
% 7.15/1.50      ( ~ v2_tex_2(k9_subset_1(X0_43,X1_43,X2_43),X0_44)
% 7.15/1.50      | v2_tex_2(k9_subset_1(X3_43,X4_43,X5_43),X0_44)
% 7.15/1.50      | X4_43 != X1_43
% 7.15/1.50      | X5_43 != X2_43
% 7.15/1.50      | X3_43 != X0_43 ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_813,c_817]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_8796,plain,
% 7.15/1.50      ( v2_tex_2(k9_subset_1(X0_43,X1_43,X2_43),sK1)
% 7.15/1.50      | ~ v2_tex_2(sK2,sK1)
% 7.15/1.50      | ~ r1_tarski(X3_43,X4_43)
% 7.15/1.50      | ~ r1_tarski(k9_subset_1(X4_43,u1_struct_0(sK1),X3_43),sK2)
% 7.15/1.50      | X2_43 != X3_43
% 7.15/1.50      | X0_43 != X4_43
% 7.15/1.50      | X1_43 != u1_struct_0(sK1) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_8369,c_3354]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_10,negated_conjecture,
% 7.15/1.50      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1349,plain,
% 7.15/1.50      ( r1_tarski(sK2,u1_struct_0(sK1)) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_795,c_791]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1586,plain,
% 7.15/1.50      ( ~ v2_tex_2(X0_43,sK1)
% 7.15/1.50      | v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1)
% 7.15/1.50      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.15/1.50      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.15/1.50      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X0_43) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_789]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1588,plain,
% 7.15/1.50      ( v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1)
% 7.15/1.50      | ~ v2_tex_2(sK2,sK1)
% 7.15/1.50      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.15/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.15/1.50      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK2) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_1586]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1826,plain,
% 7.15/1.50      ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.15/1.50      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_796]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1897,plain,
% 7.15/1.50      ( k9_subset_1(u1_struct_0(sK1),sK2,sK3) = k9_subset_1(u1_struct_0(sK1),sK2,sK3) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_804]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1699,plain,
% 7.15/1.50      ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X0_43),k9_subset_1(u1_struct_0(sK1),sK2,sK3))
% 7.15/1.50      | r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X0_43) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_801]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2148,plain,
% 7.15/1.50      ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),k9_subset_1(u1_struct_0(sK1),sK2,sK3))
% 7.15/1.50      | r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_1699]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1691,plain,
% 7.15/1.50      ( X0_43 != X1_43
% 7.15/1.50      | k9_subset_1(u1_struct_0(sK1),sK2,sK3) != X1_43
% 7.15/1.50      | k9_subset_1(u1_struct_0(sK1),sK2,sK3) = X0_43 ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_808]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1896,plain,
% 7.15/1.50      ( X0_43 != k9_subset_1(u1_struct_0(sK1),sK2,sK3)
% 7.15/1.50      | k9_subset_1(u1_struct_0(sK1),sK2,sK3) = X0_43
% 7.15/1.50      | k9_subset_1(u1_struct_0(sK1),sK2,sK3) != k9_subset_1(u1_struct_0(sK1),sK2,sK3) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_1691]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2239,plain,
% 7.15/1.50      ( k9_subset_1(u1_struct_0(sK1),sK2,sK3) != k9_subset_1(u1_struct_0(sK1),sK2,sK3)
% 7.15/1.50      | k9_subset_1(u1_struct_0(sK1),sK2,sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 7.15/1.50      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k9_subset_1(u1_struct_0(sK1),sK2,sK3) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_1896]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2240,plain,
% 7.15/1.50      ( ~ r1_tarski(sK3,u1_struct_0(sK1))
% 7.15/1.50      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k9_subset_1(u1_struct_0(sK1),sK2,sK3) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_790]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1709,plain,
% 7.15/1.50      ( ~ r1_tarski(X0_43,X1_43)
% 7.15/1.50      | r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X1_43)
% 7.15/1.50      | k9_subset_1(u1_struct_0(sK1),sK2,sK3) != X0_43 ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_810]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2529,plain,
% 7.15/1.50      ( r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X0_43)
% 7.15/1.50      | ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0_43)
% 7.15/1.50      | k9_subset_1(u1_struct_0(sK1),sK2,sK3) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_1709]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2540,plain,
% 7.15/1.50      ( r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK2)
% 7.15/1.50      | ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK2)
% 7.15/1.50      | k9_subset_1(u1_struct_0(sK1),sK2,sK3) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_2529]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2893,plain,
% 7.15/1.50      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK2) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_799]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2392,plain,
% 7.15/1.50      ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X0_43),X1_43)
% 7.15/1.50      | ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X0_43),k9_subset_1(u1_struct_0(sK1),sK2,sK3))
% 7.15/1.50      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X1_43) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_800]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4171,plain,
% 7.15/1.50      ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),X0_43)
% 7.15/1.50      | ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),k9_subset_1(u1_struct_0(sK1),sK2,sK3))
% 7.15/1.50      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),X0_43) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_2392]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4173,plain,
% 7.15/1.50      ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),k9_subset_1(u1_struct_0(sK1),sK2,sK3))
% 7.15/1.50      | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),sK2)
% 7.15/1.50      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK2) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_4171]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7376,plain,
% 7.15/1.50      ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),u1_struct_0(sK1))
% 7.15/1.50      | r1_tarski(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_802]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7368,plain,
% 7.15/1.50      ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),X0_43)
% 7.15/1.50      | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),X1_43)
% 7.15/1.50      | ~ r1_tarski(X0_43,X1_43) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_800]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_13791,plain,
% 7.15/1.50      ( ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),X0_43)
% 7.15/1.50      | r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),u1_struct_0(sK1))
% 7.15/1.50      | ~ r1_tarski(X0_43,u1_struct_0(sK1)) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_7368]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_13793,plain,
% 7.15/1.50      ( r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),u1_struct_0(sK1))
% 7.15/1.50      | ~ r2_hidden(sK0(k9_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)),sK2)
% 7.15/1.50      | ~ r1_tarski(sK2,u1_struct_0(sK1)) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_13791]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14300,plain,
% 7.15/1.50      ( ~ v2_tex_2(sK2,sK1) ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_8796,c_13,c_10,c_1347,c_1349,c_1588,c_1826,c_1897,
% 7.15/1.50                 c_2148,c_2239,c_2240,c_2540,c_2893,c_4173,c_7376,
% 7.15/1.50                 c_13793]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_11,negated_conjecture,
% 7.15/1.50      ( v2_tex_2(sK3,sK1) | v2_tex_2(sK2,sK1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_793,negated_conjecture,
% 7.15/1.50      ( v2_tex_2(sK3,sK1) | v2_tex_2(sK2,sK1) ),
% 7.15/1.50      inference(subtyping,[status(esa)],[c_11]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14580,plain,
% 7.15/1.50      ( v2_tex_2(sK3,sK1) ),
% 7.15/1.50      inference(backward_subsumption_resolution,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_14300,c_793]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1890,plain,
% 7.15/1.50      ( v2_tex_2(X0_43,sK1)
% 7.15/1.50      | ~ v2_tex_2(sK3,sK1)
% 7.15/1.50      | ~ r1_tarski(X0_43,u1_struct_0(sK1))
% 7.15/1.50      | ~ r1_tarski(X0_43,sK3) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_1778,c_792]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14606,plain,
% 7.15/1.50      ( v2_tex_2(X0_43,sK1)
% 7.15/1.50      | ~ r1_tarski(X0_43,u1_struct_0(sK1))
% 7.15/1.50      | ~ r1_tarski(X0_43,sK3) ),
% 7.15/1.50      inference(backward_subsumption_resolution,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_14580,c_1890]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_20259,plain,
% 7.15/1.50      ( v2_tex_2(k4_xboole_0(sK3,X0_43),sK1)
% 7.15/1.50      | ~ r1_tarski(k4_xboole_0(sK3,X0_43),sK3) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_20076,c_14606]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1311,plain,
% 7.15/1.50      ( v2_tex_2(X0_43,sK1)
% 7.15/1.50      | ~ v2_tex_2(sK3,sK1)
% 7.15/1.50      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.15/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.15/1.50      | ~ r1_tarski(X0_43,sK3) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_789]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1481,plain,
% 7.15/1.50      ( v2_tex_2(k4_xboole_0(sK3,X0_43),sK1)
% 7.15/1.50      | ~ v2_tex_2(sK3,sK1)
% 7.15/1.50      | ~ m1_subset_1(k4_xboole_0(sK3,X0_43),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.15/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.15/1.50      | ~ r1_tarski(k4_xboole_0(sK3,X0_43),sK3) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_1311]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1482,plain,
% 7.15/1.50      ( r1_tarski(k4_xboole_0(sK3,X0_43),sK3) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_799]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1596,plain,
% 7.15/1.50      ( m1_subset_1(k4_xboole_0(sK3,X0_43),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.15/1.50      | ~ r1_tarski(k4_xboole_0(sK3,X0_43),u1_struct_0(sK1)) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_796]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_20279,plain,
% 7.15/1.50      ( v2_tex_2(k4_xboole_0(sK3,X0_43),sK1) ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_20259,c_13,c_12,c_11,c_10,c_1347,c_1349,c_1481,c_1482,
% 7.15/1.50                 c_1588,c_1596,c_1826,c_1897,c_2148,c_2239,c_2240,c_2540,
% 7.15/1.50                 c_2893,c_4173,c_7376,c_13793,c_20076]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_6,plain,
% 7.15/1.50      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.15/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_797,plain,
% 7.15/1.50      ( k1_setfam_1(k1_enumset1(X0_43,X0_43,X1_43)) = k4_xboole_0(X0_43,k4_xboole_0(X0_43,X1_43)) ),
% 7.15/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_6036,plain,
% 7.15/1.50      ( ~ v2_tex_2(k4_xboole_0(X0_43,k4_xboole_0(X0_43,X1_43)),X0_44)
% 7.15/1.50      | v2_tex_2(k1_setfam_1(k1_enumset1(X0_43,X0_43,X1_43)),X0_44) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_797,c_817]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_20298,plain,
% 7.15/1.50      ( v2_tex_2(k1_setfam_1(k1_enumset1(sK3,sK3,X0_43)),sK1) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_20279,c_6036]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_816,plain,
% 7.15/1.50      ( X0_46 != X1_46 | k1_setfam_1(X0_46) = k1_setfam_1(X1_46) ),
% 7.15/1.50      theory(equality) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2330,plain,
% 7.15/1.50      ( ~ v2_tex_2(k1_setfam_1(X0_46),X0_44)
% 7.15/1.50      | v2_tex_2(k1_setfam_1(X1_46),X0_44)
% 7.15/1.50      | X1_46 != X0_46 ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_816,c_817]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4,plain,
% 7.15/1.50      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_798,plain,
% 7.15/1.50      ( k1_enumset1(X0_43,X0_43,X1_43) = k1_enumset1(X1_43,X1_43,X0_43) ),
% 7.15/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7311,plain,
% 7.15/1.50      ( ~ v2_tex_2(k1_setfam_1(k1_enumset1(X0_43,X0_43,X1_43)),X0_44)
% 7.15/1.50      | v2_tex_2(k1_setfam_1(k1_enumset1(X1_43,X1_43,X0_43)),X0_44) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_2330,c_798]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_21231,plain,
% 7.15/1.50      ( v2_tex_2(k1_setfam_1(k1_enumset1(X0_43,X0_43,sK3)),sK1) ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_20298,c_7311]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_21233,plain,
% 7.15/1.50      ( v2_tex_2(k1_setfam_1(k1_enumset1(sK2,sK2,sK3)),sK1) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_21231]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1210,plain,
% 7.15/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1207,plain,
% 7.15/1.50      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
% 7.15/1.50      | r1_tarski(X0_43,X1_43) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_795]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2295,plain,
% 7.15/1.50      ( r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1210,c_1207]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1212,plain,
% 7.15/1.50      ( k4_xboole_0(X0_43,k4_xboole_0(X0_43,X1_43)) = k9_subset_1(X2_43,X0_43,X1_43)
% 7.15/1.50      | r1_tarski(X1_43,X2_43) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1246,plain,
% 7.15/1.50      ( k1_setfam_1(k1_enumset1(X0_43,X0_43,X1_43)) = k9_subset_1(X2_43,X0_43,X1_43)
% 7.15/1.50      | r1_tarski(X1_43,X2_43) != iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_1212,c_797]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3220,plain,
% 7.15/1.50      ( k1_setfam_1(k1_enumset1(X0_43,X0_43,sK3)) = k9_subset_1(u1_struct_0(sK1),X0_43,sK3) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_2295,c_1246]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_794,negated_conjecture,
% 7.15/1.50      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1) ),
% 7.15/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1208,plain,
% 7.15/1.50      ( v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3743,plain,
% 7.15/1.50      ( v2_tex_2(k1_setfam_1(k1_enumset1(sK2,sK2,sK3)),sK1) != iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_3220,c_1208]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3744,plain,
% 7.15/1.50      ( ~ v2_tex_2(k1_setfam_1(k1_enumset1(sK2,sK2,sK3)),sK1) ),
% 7.15/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_3743]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(contradiction,plain,
% 7.15/1.50      ( $false ),
% 7.15/1.50      inference(minisat,[status(thm)],[c_21233,c_3744]) ).
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.15/1.50  
% 7.15/1.50  ------                               Statistics
% 7.15/1.50  
% 7.15/1.50  ------ Selected
% 7.15/1.50  
% 7.15/1.50  total_time:                             0.725
% 7.15/1.50  
%------------------------------------------------------------------------------
