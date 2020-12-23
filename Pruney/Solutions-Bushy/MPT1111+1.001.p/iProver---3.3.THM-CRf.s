%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1111+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:54 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   53 (  79 expanded)
%              Number of clauses        :   21 (  22 expanded)
%              Number of leaves         :   10 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  149 ( 293 expanded)
%              Number of equality atoms :   18 (  45 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ r2_hidden(X2,X1) )
              & k1_struct_0(X0) != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r2_hidden(X2,X1) )
                & k1_struct_0(X0) != X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & k1_struct_0(X0) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & k1_struct_0(X0) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & k1_struct_0(X0) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X2] :
            ( ~ r2_hidden(X2,sK2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & k1_struct_0(X0) != sK2
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & k1_struct_0(X0) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
          & k1_struct_0(sK1) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    & k1_struct_0(sK1) != sK2
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f21,f20])).

fof(f32,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f18])).

fof(f24,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    k1_struct_0(sK1) != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f29,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_127,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_3,c_4])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK0(X0),X0)
    | m1_subset_1(sK0(X0),X1)
    | v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_127])).

cnf(c_552,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_397])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_389,plain,
    ( ~ v1_xboole_0(k1_struct_0(sK1))
    | ~ v1_xboole_0(sK2)
    | k1_struct_0(sK1) = sK2 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_142,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | v1_xboole_0(X1)
    | X2 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_143,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,sK2)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_142])).

cnf(c_384,plain,
    ( ~ m1_subset_1(sK0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK2),sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_143])).

cnf(c_1,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_383,plain,
    ( m1_subset_1(sK0(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_31,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_25,plain,
    ( v1_xboole_0(k1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7,negated_conjecture,
    ( k1_struct_0(sK1) != sK2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_9,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_552,c_389,c_384,c_383,c_31,c_25,c_7,c_8,c_9])).


%------------------------------------------------------------------------------
