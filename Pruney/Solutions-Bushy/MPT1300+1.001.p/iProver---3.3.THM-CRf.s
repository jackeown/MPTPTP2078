%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1300+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:23 EST 2020

% Result     : Theorem 0.86s
% Output     : CNFRefutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 141 expanded)
%              Number of clauses        :   33 (  35 expanded)
%              Number of leaves         :   10 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  277 ( 762 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK0(X0,X1),X0)
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v1_tops_2(X2,X0)
                    & r1_tarski(X1,X2) )
                 => v1_tops_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,X0)
              & v1_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,X0)
              & v1_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_2(X1,X0)
          & v1_tops_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v1_tops_2(X1,X0)
        & v1_tops_2(sK3,X0)
        & r1_tarski(X1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,X0)
              & v1_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v1_tops_2(sK2,X0)
            & v1_tops_2(X2,X0)
            & r1_tarski(sK2,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(X1,X0)
                & v1_tops_2(X2,X0)
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,sK1)
              & v1_tops_2(X2,sK1)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ v1_tops_2(sK2,sK1)
    & v1_tops_2(sK3,sK1)
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f25,f24,f23])).

fof(f35,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ~ v1_tops_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    v1_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_566,plain,
    ( ~ r2_hidden(X0_41,X1_41)
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X2_41))
    | ~ v1_xboole_0(X2_41) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_714,plain,
    ( ~ r2_hidden(X0_41,X1_41)
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(sK3))
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_566])).

cnf(c_719,plain,
    ( ~ r2_hidden(sK0(sK1,X0_41),X0_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(sK3))
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_721,plain,
    ( ~ r2_hidden(sK0(sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK3))
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_568,plain,
    ( r2_hidden(X0_41,X1_41)
    | ~ m1_subset_1(X0_41,X1_41)
    | v1_xboole_0(X1_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_688,plain,
    ( r2_hidden(sK0(sK1,sK2),sK3)
    | ~ m1_subset_1(sK0(sK1,sK2),sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_568])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_567,plain,
    ( ~ r2_hidden(X0_41,X1_41)
    | m1_subset_1(X0_41,X2_41)
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X2_41)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_642,plain,
    ( ~ r2_hidden(sK0(sK1,X0_41),X0_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(X1_41))
    | m1_subset_1(sK0(sK1,X0_41),X1_41) ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_670,plain,
    ( ~ r2_hidden(sK0(sK1,sK2),sK2)
    | m1_subset_1(sK0(sK1,sK2),sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v3_pre_topc(sK0(X1,X0),X1)
    | v1_tops_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_170,plain,
    ( ~ r2_hidden(sK0(X0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_tops_2(X2,X0)
    | v1_tops_2(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_3])).

cnf(c_186,plain,
    ( ~ r2_hidden(sK0(X0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ v1_tops_2(X2,X0)
    | v1_tops_2(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_170,c_6])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_215,plain,
    ( ~ r2_hidden(sK0(sK1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ v1_tops_2(X1,sK1)
    | v1_tops_2(X0,sK1) ),
    inference(resolution,[status(thm)],[c_186,c_13])).

cnf(c_559,plain,
    ( ~ r2_hidden(sK0(sK1,X0_41),X1_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ v1_tops_2(X1_41,sK1)
    | v1_tops_2(X0_41,sK1) ),
    inference(subtyping,[status(esa)],[c_215])).

cnf(c_623,plain,
    ( ~ r2_hidden(sK0(sK1,X0_41),sK3)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | v1_tops_2(X0_41,sK1)
    | ~ v1_tops_2(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_559])).

cnf(c_625,plain,
    ( ~ r2_hidden(sK0(sK1,sK2),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ v1_tops_2(sK3,sK1)
    | v1_tops_2(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v1_tops_2(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_233,plain,
    ( r2_hidden(sK0(sK1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | v1_tops_2(X0,sK1) ),
    inference(resolution,[status(thm)],[c_1,c_13])).

cnf(c_558,plain,
    ( r2_hidden(sK0(sK1,X0_41),X0_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | v1_tops_2(X0_41,sK1) ),
    inference(subtyping,[status(esa)],[c_233])).

cnf(c_588,plain,
    ( r2_hidden(sK0(sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | v1_tops_2(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_558])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_143,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK3)) ),
    inference(resolution,[status(thm)],[c_5,c_10])).

cnf(c_8,negated_conjecture,
    ( ~ v1_tops_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_9,negated_conjecture,
    ( v1_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_721,c_688,c_670,c_625,c_588,c_143,c_8,c_9,c_11,c_12])).


%------------------------------------------------------------------------------
