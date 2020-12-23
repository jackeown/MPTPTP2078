%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:16 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 127 expanded)
%              Number of clauses        :   35 (  35 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  339 (1011 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

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

fof(f22,plain,(
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

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & ~ v1_xboole_0(X3) )
                       => ~ ( r1_tarski(X3,X2)
                            & v3_pre_topc(X3,X0)
                            & m1_connsp_2(X3,X0,X1) ) )
                    & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_connsp_2(X3,X0,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X3) )
          & m1_connsp_2(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( ~ r1_tarski(X3,sK2)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_connsp_2(X3,X0,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X3) )
        & m1_connsp_2(sK2,X0,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_connsp_2(X3,X0,sK1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                | v1_xboole_0(X3) )
            & m1_connsp_2(X2,X0,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | v1_xboole_0(X3) )
                & m1_connsp_2(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,sK0)
                  | ~ m1_connsp_2(X3,sK0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK2)
        | ~ v3_pre_topc(X3,sK0)
        | ~ m1_connsp_2(X3,sK0,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X3) )
    & m1_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25,f24,f23])).

fof(f40,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_connsp_2(X3,sK0,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_142,plain,
    ( ~ r2_hidden(X0_44,X1_44)
    | ~ v1_xboole_0(X1_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1302,plain,
    ( ~ r2_hidden(X0_44,k1_tops_1(sK0,sK2))
    | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_1304,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1302])).

cnf(c_5,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_137,plain,
    ( m1_connsp_2(X0_44,X0_43,X1_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
    | ~ m1_subset_1(X1_44,u1_struct_0(X0_43))
    | ~ r2_hidden(X1_44,k1_tops_1(X0_43,X0_44))
    | v2_struct_0(X0_43)
    | ~ v2_pre_topc(X0_43)
    | ~ l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_935,plain,
    ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_137])).

cnf(c_146,plain,
    ( ~ r2_hidden(X0_44,X1_44)
    | r2_hidden(X0_44,X2_44)
    | X2_44 != X1_44 ),
    theory(equality)).

cnf(c_670,plain,
    ( r2_hidden(sK1,X0_44)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | X0_44 != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_823,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_7,negated_conjecture,
    ( ~ m1_connsp_2(X0,sK0,sK1)
    | ~ r1_tarski(X0,sK2)
    | ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_135,negated_conjecture,
    ( ~ m1_connsp_2(X0_44,sK0,sK1)
    | ~ r1_tarski(X0_44,sK2)
    | ~ v3_pre_topc(X0_44,sK0)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0_44) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_655,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_6,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_136,plain,
    ( ~ m1_connsp_2(X0_44,X0_43,X1_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
    | ~ m1_subset_1(X1_44,u1_struct_0(X0_43))
    | r2_hidden(X1_44,k1_tops_1(X0_43,X0_44))
    | v2_struct_0(X0_43)
    | ~ v2_pre_topc(X0_43)
    | ~ l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_600,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_139,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
    | ~ l1_pre_topc(X0_43)
    | k1_tops_1(X0_43,k1_tops_1(X0_43,X0_44)) = k1_tops_1(X0_43,X0_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_592,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_139])).

cnf(c_2,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_140,plain,
    ( v3_pre_topc(k1_tops_1(X0_43,X0_44),X0_43)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
    | ~ v2_pre_topc(X0_43)
    | ~ l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_589,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_141,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
    | m1_subset_1(k1_tops_1(X0_43,X0_44),k1_zfmisc_1(u1_struct_0(X0_43)))
    | ~ l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_562,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_141])).

cnf(c_4,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_138,plain,
    ( r1_tarski(k1_tops_1(X0_43,X0_44),X0_44)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
    | ~ l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_559,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_138])).

cnf(c_8,negated_conjecture,
    ( m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1304,c_935,c_823,c_655,c_600,c_592,c_589,c_562,c_559,c_8,c_9,c_10,c_11,c_12,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:53:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.69/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/0.99  
% 2.69/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/0.99  
% 2.69/0.99  ------  iProver source info
% 2.69/0.99  
% 2.69/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.69/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/0.99  git: non_committed_changes: false
% 2.69/0.99  git: last_make_outside_of_git: false
% 2.69/0.99  
% 2.69/0.99  ------ 
% 2.69/0.99  ------ Parsing...
% 2.69/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/0.99  
% 2.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.69/0.99  ------ Proving...
% 2.69/0.99  ------ Problem Properties 
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  clauses                                 14
% 2.69/0.99  conjectures                             7
% 2.69/0.99  EPR                                     5
% 2.69/0.99  Horn                                    12
% 2.69/0.99  unary                                   6
% 2.69/0.99  binary                                  1
% 2.69/0.99  lits                                    40
% 2.69/0.99  lits eq                                 1
% 2.69/0.99  fd_pure                                 0
% 2.69/0.99  fd_pseudo                               0
% 2.69/0.99  fd_cond                                 0
% 2.69/0.99  fd_pseudo_cond                          0
% 2.69/0.99  AC symbols                              0
% 2.69/0.99  
% 2.69/0.99  ------ Input Options Time Limit: Unbounded
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  ------ 
% 2.69/0.99  Current options:
% 2.69/0.99  ------ 
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  ------ Proving...
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  % SZS status Theorem for theBenchmark.p
% 2.69/0.99  
% 2.69/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/0.99  
% 2.69/0.99  fof(f1,axiom,(
% 2.69/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f9,plain,(
% 2.69/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.69/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 2.69/0.99  
% 2.69/0.99  fof(f10,plain,(
% 2.69/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.69/0.99    inference(ennf_transformation,[],[f9])).
% 2.69/0.99  
% 2.69/0.99  fof(f27,plain,(
% 2.69/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f10])).
% 2.69/0.99  
% 2.69/0.99  fof(f6,axiom,(
% 2.69/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 2.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f18,plain,(
% 2.69/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.69/0.99    inference(ennf_transformation,[],[f6])).
% 2.69/0.99  
% 2.69/0.99  fof(f19,plain,(
% 2.69/0.99    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.69/0.99    inference(flattening,[],[f18])).
% 2.69/0.99  
% 2.69/0.99  fof(f22,plain,(
% 2.69/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.69/0.99    inference(nnf_transformation,[],[f19])).
% 2.69/0.99  
% 2.69/0.99  fof(f33,plain,(
% 2.69/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f22])).
% 2.69/0.99  
% 2.69/0.99  fof(f7,conjecture,(
% 2.69/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f8,negated_conjecture,(
% 2.69/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 2.69/0.99    inference(negated_conjecture,[],[f7])).
% 2.69/0.99  
% 2.69/0.99  fof(f20,plain,(
% 2.69/0.99    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.69/0.99    inference(ennf_transformation,[],[f8])).
% 2.69/0.99  
% 2.69/0.99  fof(f21,plain,(
% 2.69/0.99    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.69/0.99    inference(flattening,[],[f20])).
% 2.69/0.99  
% 2.69/0.99  fof(f25,plain,(
% 2.69/0.99    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,X0,X1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.69/0.99    introduced(choice_axiom,[])).
% 2.69/0.99  
% 2.69/0.99  fof(f24,plain,(
% 2.69/0.99    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 2.69/0.99    introduced(choice_axiom,[])).
% 2.69/0.99  
% 2.69/0.99  fof(f23,plain,(
% 2.69/0.99    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.69/0.99    introduced(choice_axiom,[])).
% 2.69/0.99  
% 2.69/0.99  fof(f26,plain,(
% 2.69/0.99    ((! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25,f24,f23])).
% 2.69/0.99  
% 2.69/0.99  fof(f40,plain,(
% 2.69/0.99    ( ! [X3] : (~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f26])).
% 2.69/0.99  
% 2.69/0.99  fof(f32,plain,(
% 2.69/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f22])).
% 2.69/0.99  
% 2.69/0.99  fof(f4,axiom,(
% 2.69/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 2.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f15,plain,(
% 2.69/0.99    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.69/0.99    inference(ennf_transformation,[],[f4])).
% 2.69/0.99  
% 2.69/0.99  fof(f16,plain,(
% 2.69/0.99    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.69/0.99    inference(flattening,[],[f15])).
% 2.69/0.99  
% 2.69/0.99  fof(f30,plain,(
% 2.69/0.99    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f16])).
% 2.69/0.99  
% 2.69/0.99  fof(f3,axiom,(
% 2.69/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f13,plain,(
% 2.69/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.69/0.99    inference(ennf_transformation,[],[f3])).
% 2.69/0.99  
% 2.69/0.99  fof(f14,plain,(
% 2.69/0.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.69/0.99    inference(flattening,[],[f13])).
% 2.69/0.99  
% 2.69/0.99  fof(f29,plain,(
% 2.69/0.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f14])).
% 2.69/0.99  
% 2.69/0.99  fof(f2,axiom,(
% 2.69/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f11,plain,(
% 2.69/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.69/0.99    inference(ennf_transformation,[],[f2])).
% 2.69/0.99  
% 2.69/0.99  fof(f12,plain,(
% 2.69/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.69/0.99    inference(flattening,[],[f11])).
% 2.69/0.99  
% 2.69/0.99  fof(f28,plain,(
% 2.69/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f12])).
% 2.69/0.99  
% 2.69/0.99  fof(f5,axiom,(
% 2.69/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/0.99  
% 2.69/0.99  fof(f17,plain,(
% 2.69/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.69/0.99    inference(ennf_transformation,[],[f5])).
% 2.69/0.99  
% 2.69/0.99  fof(f31,plain,(
% 2.69/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.69/0.99    inference(cnf_transformation,[],[f17])).
% 2.69/0.99  
% 2.69/0.99  fof(f39,plain,(
% 2.69/0.99    m1_connsp_2(sK2,sK0,sK1)),
% 2.69/0.99    inference(cnf_transformation,[],[f26])).
% 2.69/0.99  
% 2.69/0.99  fof(f38,plain,(
% 2.69/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.69/0.99    inference(cnf_transformation,[],[f26])).
% 2.69/0.99  
% 2.69/0.99  fof(f37,plain,(
% 2.69/0.99    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.69/0.99    inference(cnf_transformation,[],[f26])).
% 2.69/0.99  
% 2.69/0.99  fof(f36,plain,(
% 2.69/0.99    l1_pre_topc(sK0)),
% 2.69/0.99    inference(cnf_transformation,[],[f26])).
% 2.69/0.99  
% 2.69/0.99  fof(f35,plain,(
% 2.69/0.99    v2_pre_topc(sK0)),
% 2.69/0.99    inference(cnf_transformation,[],[f26])).
% 2.69/0.99  
% 2.69/0.99  fof(f34,plain,(
% 2.69/0.99    ~v2_struct_0(sK0)),
% 2.69/0.99    inference(cnf_transformation,[],[f26])).
% 2.69/0.99  
% 2.69/0.99  cnf(c_0,plain,
% 2.69/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.69/0.99      inference(cnf_transformation,[],[f27]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_142,plain,
% 2.69/0.99      ( ~ r2_hidden(X0_44,X1_44) | ~ v1_xboole_0(X1_44) ),
% 2.69/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1302,plain,
% 2.69/0.99      ( ~ r2_hidden(X0_44,k1_tops_1(sK0,sK2))
% 2.69/0.99      | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_142]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1304,plain,
% 2.69/0.99      ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 2.69/0.99      | ~ v1_xboole_0(k1_tops_1(sK0,sK2)) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_1302]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_5,plain,
% 2.69/0.99      ( m1_connsp_2(X0,X1,X2)
% 2.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.69/0.99      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 2.69/0.99      | v2_struct_0(X1)
% 2.69/0.99      | ~ v2_pre_topc(X1)
% 2.69/0.99      | ~ l1_pre_topc(X1) ),
% 2.69/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_137,plain,
% 2.69/0.99      ( m1_connsp_2(X0_44,X0_43,X1_44)
% 2.69/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
% 2.69/0.99      | ~ m1_subset_1(X1_44,u1_struct_0(X0_43))
% 2.69/0.99      | ~ r2_hidden(X1_44,k1_tops_1(X0_43,X0_44))
% 2.69/0.99      | v2_struct_0(X0_43)
% 2.69/0.99      | ~ v2_pre_topc(X0_43)
% 2.69/0.99      | ~ l1_pre_topc(X0_43) ),
% 2.69/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_935,plain,
% 2.69/0.99      ( m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
% 2.69/0.99      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/0.99      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 2.69/0.99      | ~ r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
% 2.69/0.99      | v2_struct_0(sK0)
% 2.69/0.99      | ~ v2_pre_topc(sK0)
% 2.69/0.99      | ~ l1_pre_topc(sK0) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_137]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_146,plain,
% 2.69/0.99      ( ~ r2_hidden(X0_44,X1_44)
% 2.69/0.99      | r2_hidden(X0_44,X2_44)
% 2.69/0.99      | X2_44 != X1_44 ),
% 2.69/0.99      theory(equality) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_670,plain,
% 2.69/0.99      ( r2_hidden(sK1,X0_44)
% 2.69/0.99      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 2.69/0.99      | X0_44 != k1_tops_1(sK0,sK2) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_146]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_823,plain,
% 2.69/0.99      ( r2_hidden(sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK2)))
% 2.69/0.99      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 2.69/0.99      | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) != k1_tops_1(sK0,sK2) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_670]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_7,negated_conjecture,
% 2.69/0.99      ( ~ m1_connsp_2(X0,sK0,sK1)
% 2.69/0.99      | ~ r1_tarski(X0,sK2)
% 2.69/0.99      | ~ v3_pre_topc(X0,sK0)
% 2.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/0.99      | v1_xboole_0(X0) ),
% 2.69/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_135,negated_conjecture,
% 2.69/0.99      ( ~ m1_connsp_2(X0_44,sK0,sK1)
% 2.69/0.99      | ~ r1_tarski(X0_44,sK2)
% 2.69/0.99      | ~ v3_pre_topc(X0_44,sK0)
% 2.69/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/0.99      | v1_xboole_0(X0_44) ),
% 2.69/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_655,plain,
% 2.69/0.99      ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
% 2.69/0.99      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 2.69/0.99      | ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 2.69/0.99      | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/0.99      | v1_xboole_0(k1_tops_1(sK0,sK2)) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_135]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_6,plain,
% 2.69/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 2.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.69/0.99      | r2_hidden(X2,k1_tops_1(X1,X0))
% 2.69/0.99      | v2_struct_0(X1)
% 2.69/0.99      | ~ v2_pre_topc(X1)
% 2.69/0.99      | ~ l1_pre_topc(X1) ),
% 2.69/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_136,plain,
% 2.69/0.99      ( ~ m1_connsp_2(X0_44,X0_43,X1_44)
% 2.69/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
% 2.69/0.99      | ~ m1_subset_1(X1_44,u1_struct_0(X0_43))
% 2.69/0.99      | r2_hidden(X1_44,k1_tops_1(X0_43,X0_44))
% 2.69/0.99      | v2_struct_0(X0_43)
% 2.69/0.99      | ~ v2_pre_topc(X0_43)
% 2.69/0.99      | ~ l1_pre_topc(X0_43) ),
% 2.69/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_600,plain,
% 2.69/0.99      ( ~ m1_connsp_2(sK2,sK0,sK1)
% 2.69/0.99      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
% 2.69/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/0.99      | r2_hidden(sK1,k1_tops_1(sK0,sK2))
% 2.69/0.99      | v2_struct_0(sK0)
% 2.69/0.99      | ~ v2_pre_topc(sK0)
% 2.69/0.99      | ~ l1_pre_topc(sK0) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_136]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_3,plain,
% 2.69/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/0.99      | ~ l1_pre_topc(X1)
% 2.69/0.99      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 2.69/0.99      inference(cnf_transformation,[],[f30]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_139,plain,
% 2.69/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
% 2.69/0.99      | ~ l1_pre_topc(X0_43)
% 2.69/0.99      | k1_tops_1(X0_43,k1_tops_1(X0_43,X0_44)) = k1_tops_1(X0_43,X0_44) ),
% 2.69/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_592,plain,
% 2.69/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/0.99      | ~ l1_pre_topc(sK0)
% 2.69/0.99      | k1_tops_1(sK0,k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,sK2) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_139]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_2,plain,
% 2.69/0.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 2.69/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.69/0.99      | ~ v2_pre_topc(X0)
% 2.69/0.99      | ~ l1_pre_topc(X0) ),
% 2.69/0.99      inference(cnf_transformation,[],[f29]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_140,plain,
% 2.69/0.99      ( v3_pre_topc(k1_tops_1(X0_43,X0_44),X0_43)
% 2.69/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
% 2.69/0.99      | ~ v2_pre_topc(X0_43)
% 2.69/0.99      | ~ l1_pre_topc(X0_43) ),
% 2.69/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_589,plain,
% 2.69/0.99      ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
% 2.69/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/0.99      | ~ v2_pre_topc(sK0)
% 2.69/0.99      | ~ l1_pre_topc(sK0) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_140]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_1,plain,
% 2.69/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/0.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.69/0.99      | ~ l1_pre_topc(X1) ),
% 2.69/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_141,plain,
% 2.69/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
% 2.69/0.99      | m1_subset_1(k1_tops_1(X0_43,X0_44),k1_zfmisc_1(u1_struct_0(X0_43)))
% 2.69/0.99      | ~ l1_pre_topc(X0_43) ),
% 2.69/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_562,plain,
% 2.69/0.99      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/0.99      | ~ l1_pre_topc(sK0) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_141]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_4,plain,
% 2.69/0.99      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 2.69/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.69/0.99      | ~ l1_pre_topc(X0) ),
% 2.69/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_138,plain,
% 2.69/0.99      ( r1_tarski(k1_tops_1(X0_43,X0_44),X0_44)
% 2.69/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
% 2.69/0.99      | ~ l1_pre_topc(X0_43) ),
% 2.69/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_559,plain,
% 2.69/0.99      ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 2.69/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.69/0.99      | ~ l1_pre_topc(sK0) ),
% 2.69/0.99      inference(instantiation,[status(thm)],[c_138]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_8,negated_conjecture,
% 2.69/0.99      ( m1_connsp_2(sK2,sK0,sK1) ),
% 2.69/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_9,negated_conjecture,
% 2.69/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.69/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_10,negated_conjecture,
% 2.69/0.99      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 2.69/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_11,negated_conjecture,
% 2.69/0.99      ( l1_pre_topc(sK0) ),
% 2.69/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_12,negated_conjecture,
% 2.69/0.99      ( v2_pre_topc(sK0) ),
% 2.69/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(c_13,negated_conjecture,
% 2.69/0.99      ( ~ v2_struct_0(sK0) ),
% 2.69/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.69/0.99  
% 2.69/0.99  cnf(contradiction,plain,
% 2.69/0.99      ( $false ),
% 2.69/0.99      inference(minisat,
% 2.69/0.99                [status(thm)],
% 2.69/0.99                [c_1304,c_935,c_823,c_655,c_600,c_592,c_589,c_562,c_559,
% 2.69/0.99                 c_8,c_9,c_10,c_11,c_12,c_13]) ).
% 2.69/0.99  
% 2.69/0.99  
% 2.69/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/0.99  
% 2.69/0.99  ------                               Statistics
% 2.69/0.99  
% 2.69/0.99  ------ Selected
% 2.69/0.99  
% 2.69/0.99  total_time:                             0.052
% 2.69/0.99  
%------------------------------------------------------------------------------
