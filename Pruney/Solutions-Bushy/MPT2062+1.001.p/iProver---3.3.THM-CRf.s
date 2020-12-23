%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2062+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:06 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 258 expanded)
%              Number of clauses        :   48 (  59 expanded)
%              Number of leaves         :    9 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  318 (1320 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0) )
               => r2_hidden(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X3)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(X2,sK0(X0,X1,X2))
        & v3_pre_topc(sK0(X0,X1,X2),X0)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(X2,sK0(X0,X1,X2))
              & v3_pre_topc(sK0(X0,X1,X2),X0)
              & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2,X3] :
          ( ( r2_waybel_7(X0,X1,X3)
            & r1_tarski(X1,X2) )
         => r2_waybel_7(X0,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2,X3] :
            ( ( r2_waybel_7(X0,X1,X3)
              & r1_tarski(X1,X2) )
           => r2_waybel_7(X0,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f9,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1,X2,X3] :
            ( ( r2_waybel_7(X0,X1,X3)
              & r1_tarski(X1,X2) )
           => r2_waybel_7(X0,X2,X3) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_waybel_7(X0,X2,X3)
          & r2_waybel_7(X0,X1,X3)
          & r1_tarski(X1,X2) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_waybel_7(X0,X2,X3)
          & r2_waybel_7(X0,X1,X3)
          & r1_tarski(X1,X2) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_waybel_7(X0,X2,X3)
          & r2_waybel_7(X0,X1,X3)
          & r1_tarski(X1,X2) )
     => ( ~ r2_waybel_7(X0,sK3,sK4)
        & r2_waybel_7(X0,sK2,sK4)
        & r1_tarski(sK2,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ~ r2_waybel_7(X0,X2,X3)
            & r2_waybel_7(X0,X1,X3)
            & r1_tarski(X1,X2) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X3,X2,X1] :
          ( ~ r2_waybel_7(sK1,X2,X3)
          & r2_waybel_7(sK1,X1,X3)
          & r1_tarski(X1,X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r2_waybel_7(sK1,sK3,sK4)
    & r2_waybel_7(sK1,sK2,sK4)
    & r1_tarski(sK2,sK3)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f19,f25,f24])).

fof(f37,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ~ r2_waybel_7(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | v3_pre_topc(sK0(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | r2_hidden(X2,sK0(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    r2_waybel_7(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_730,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ r2_hidden(X2_44,X0_44)
    | ~ v1_xboole_0(X1_44) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_933,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(sK3))
    | ~ r2_hidden(X1_44,X0_44)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_1019,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(sK3))
    | ~ r2_hidden(sK0(sK1,sK3,sK4),X0_44)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK3))
    | ~ r2_hidden(sK0(sK1,sK3,sK4),sK2)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0_44,X1_44)
    | r2_hidden(X0_44,X1_44)
    | v1_xboole_0(X1_44) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_913,plain,
    ( ~ m1_subset_1(sK0(sK1,sK3,sK4),sK3)
    | r2_hidden(sK0(sK1,sK3,sK4),sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_731,plain,
    ( m1_subset_1(X0_44,X1_44)
    | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
    | ~ r2_hidden(X0_44,X2_44) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_839,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | m1_subset_1(sK0(sK1,sK3,sK4),X1_44)
    | ~ r2_hidden(sK0(sK1,sK3,sK4),X0_44) ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_907,plain,
    ( m1_subset_1(sK0(sK1,sK3,sK4),sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK3))
    | ~ r2_hidden(sK0(sK1,sK3,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_4,plain,
    ( ~ r2_waybel_7(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_pre_topc(X3,X0)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(X3,X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_200,plain,
    ( ~ r2_waybel_7(sK1,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(X2,sK1)
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_4,c_12])).

cnf(c_13,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_202,plain,
    ( r2_hidden(X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ v3_pre_topc(X2,sK1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_waybel_7(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_200,c_13])).

cnf(c_203,plain,
    ( ~ r2_waybel_7(sK1,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(X2,sK1)
    | ~ r2_hidden(X1,X2)
    | r2_hidden(X2,X0) ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_726,plain,
    ( ~ r2_waybel_7(sK1,X0_44,X1_44)
    | ~ m1_subset_1(X2_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(X2_44,sK1)
    | ~ r2_hidden(X1_44,X2_44)
    | r2_hidden(X2_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_203])).

cnf(c_806,plain,
    ( ~ r2_waybel_7(sK1,X0_44,X1_44)
    | ~ m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(sK0(sK1,sK3,sK4),sK1)
    | ~ r2_hidden(X1_44,sK0(sK1,sK3,sK4))
    | r2_hidden(sK0(sK1,sK3,sK4),X0_44) ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_882,plain,
    ( ~ r2_waybel_7(sK1,X0_44,sK4)
    | ~ m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(sK0(sK1,sK3,sK4),sK1)
    | r2_hidden(sK0(sK1,sK3,sK4),X0_44)
    | ~ r2_hidden(sK4,sK0(sK1,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_884,plain,
    ( ~ r2_waybel_7(sK1,sK2,sK4)
    | ~ m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_pre_topc(sK0(sK1,sK3,sK4),sK1)
    | r2_hidden(sK0(sK1,sK3,sK4),sK2)
    | ~ r2_hidden(sK4,sK0(sK1,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_882])).

cnf(c_9,negated_conjecture,
    ( ~ r2_waybel_7(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( r2_waybel_7(X0,X1,X2)
    | m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_222,plain,
    ( r2_waybel_7(sK1,X0,X1)
    | m1_subset_1(sK0(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_3,c_12])).

cnf(c_226,plain,
    ( m1_subset_1(sK0(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_waybel_7(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_222,c_13])).

cnf(c_227,plain,
    ( r2_waybel_7(sK1,X0,X1)
    | m1_subset_1(sK0(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_226])).

cnf(c_420,plain,
    ( m1_subset_1(sK0(sK1,sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[status(thm)],[c_9,c_227])).

cnf(c_2,plain,
    ( r2_waybel_7(X0,X1,X2)
    | v3_pre_topc(sK0(X0,X1,X2),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_239,plain,
    ( r2_waybel_7(sK1,X0,X1)
    | v3_pre_topc(sK0(sK1,X0,X1),sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_2,c_12])).

cnf(c_243,plain,
    ( v3_pre_topc(sK0(sK1,X0,X1),sK1)
    | r2_waybel_7(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_239,c_13])).

cnf(c_244,plain,
    ( r2_waybel_7(sK1,X0,X1)
    | v3_pre_topc(sK0(sK1,X0,X1),sK1) ),
    inference(renaming,[status(thm)],[c_243])).

cnf(c_414,plain,
    ( v3_pre_topc(sK0(sK1,sK3,sK4),sK1) ),
    inference(resolution,[status(thm)],[c_9,c_244])).

cnf(c_1,plain,
    ( r2_waybel_7(X0,X1,X2)
    | r2_hidden(X2,sK0(X0,X1,X2))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_256,plain,
    ( r2_waybel_7(sK1,X0,X1)
    | r2_hidden(X1,sK0(sK1,X0,X1))
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_1,c_12])).

cnf(c_260,plain,
    ( r2_hidden(X1,sK0(sK1,X0,X1))
    | r2_waybel_7(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_256,c_13])).

cnf(c_261,plain,
    ( r2_waybel_7(sK1,X0,X1)
    | r2_hidden(X1,sK0(sK1,X0,X1)) ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_408,plain,
    ( r2_hidden(sK4,sK0(sK1,sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_9,c_261])).

cnf(c_0,plain,
    ( r2_waybel_7(X0,X1,X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_273,plain,
    ( r2_waybel_7(sK1,X0,X1)
    | ~ r2_hidden(sK0(sK1,X0,X1),X0)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_0,c_12])).

cnf(c_277,plain,
    ( ~ r2_hidden(sK0(sK1,X0,X1),X0)
    | r2_waybel_7(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_273,c_13])).

cnf(c_278,plain,
    ( r2_waybel_7(sK1,X0,X1)
    | ~ r2_hidden(sK0(sK1,X0,X1),X0) ),
    inference(renaming,[status(thm)],[c_277])).

cnf(c_402,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,sK4),sK3) ),
    inference(resolution,[status(thm)],[c_9,c_278])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_143,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK3)) ),
    inference(resolution,[status(thm)],[c_6,c_11])).

cnf(c_10,negated_conjecture,
    ( r2_waybel_7(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1021,c_913,c_907,c_884,c_420,c_414,c_408,c_402,c_143,c_10])).


%------------------------------------------------------------------------------
