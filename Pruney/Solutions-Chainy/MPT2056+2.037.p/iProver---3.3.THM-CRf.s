%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:11 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 297 expanded)
%              Number of clauses        :   54 (  85 expanded)
%              Number of leaves         :   10 (  78 expanded)
%              Depth                    :   21
%              Number of atoms          :  334 (2044 expanded)
%              Number of equality atoms :   92 ( 316 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
     => ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) != sK2
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != sK2
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))
    & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))
    & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    & ~ v1_xboole_0(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f32,f31])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != sK2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1404,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1406,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2188,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))),sK2,X0) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1404,c_1406])).

cnf(c_20,negated_conjecture,
    ( v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_16,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_365,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_366,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v2_struct_0(sK1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_25])).

cnf(c_371,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) ),
    inference(renaming,[status(thm)],[c_370])).

cnf(c_427,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0))
    | k3_yellow_1(k2_struct_0(sK1)) != k3_yellow_1(k2_struct_0(sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_371])).

cnf(c_428,plain,
    ( ~ v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | v1_xboole_0(sK2)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))),sK2,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_21,negated_conjecture,
    ( v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_430,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))),sK2,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_428,c_23,c_21,c_19])).

cnf(c_2528,plain,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = k4_xboole_0(sK2,k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_2188,c_430])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1417,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1411,plain,
    ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_17,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,negated_conjecture,
    ( v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_317,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_318,plain,
    ( ~ v2_waybel_0(sK2,k3_yellow_1(X0))
    | ~ v13_waybel_0(sK2,k3_yellow_1(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ r2_hidden(X1,sK2)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_320,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v13_waybel_0(sK2,k3_yellow_1(X0))
    | ~ v2_waybel_0(sK2,k3_yellow_1(X0))
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_318,c_23])).

cnf(c_321,plain,
    ( ~ v2_waybel_0(sK2,k3_yellow_1(X0))
    | ~ v13_waybel_0(sK2,k3_yellow_1(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ r2_hidden(X1,sK2)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0)) ),
    inference(renaming,[status(thm)],[c_320])).

cnf(c_400,plain,
    ( ~ v2_waybel_0(sK2,k3_yellow_1(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ r2_hidden(X1,sK2)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0))
    | k3_yellow_1(k2_struct_0(sK1)) != k3_yellow_1(X0)
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_321])).

cnf(c_445,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ r2_hidden(X1,sK2)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0))
    | k3_yellow_1(k2_struct_0(sK1)) != k3_yellow_1(X0)
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_400])).

cnf(c_641,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ r2_hidden(X1,sK2)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0))
    | k3_yellow_1(k2_struct_0(sK1)) != k3_yellow_1(X0) ),
    inference(equality_resolution_simp,[status(thm)],[c_445])).

cnf(c_925,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ v1_xboole_0(X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_641])).

cnf(c_1401,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_925])).

cnf(c_1835,plain,
    ( k4_xboole_0(sK2,k1_tarski(X0)) = sK2
    | v1_xboole_0(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_1401])).

cnf(c_26,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_37,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_39,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_927,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_641])).

cnf(c_957,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_929,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1625,plain,
    ( k3_yellow_1(k2_struct_0(sK1)) = k3_yellow_1(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_926,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0))
    | k3_yellow_1(k2_struct_0(sK1)) != k3_yellow_1(X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_641])).

cnf(c_1400,plain,
    ( u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0))
    | k3_yellow_1(k2_struct_0(sK1)) != k3_yellow_1(X0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_1635,plain,
    ( k3_yellow_1(k2_struct_0(sK1)) != k3_yellow_1(k2_struct_0(sK1))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1400])).

cnf(c_1853,plain,
    ( v1_xboole_0(X0) != iProver_top
    | k4_xboole_0(sK2,k1_tarski(X0)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1835,c_26,c_27,c_32,c_39,c_957,c_1625,c_1635])).

cnf(c_1854,plain,
    ( k4_xboole_0(sK2,k1_tarski(X0)) = sK2
    | v1_xboole_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1853])).

cnf(c_1861,plain,
    ( k4_xboole_0(sK2,k1_tarski(k1_xboole_0)) = sK2 ),
    inference(superposition,[status(thm)],[c_1417,c_1854])).

cnf(c_2529,plain,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2528,c_1861])).

cnf(c_18,negated_conjecture,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != sK2 ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2529,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.76/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.00  
% 1.76/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.76/1.00  
% 1.76/1.00  ------  iProver source info
% 1.76/1.00  
% 1.76/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.76/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.76/1.00  git: non_committed_changes: false
% 1.76/1.00  git: last_make_outside_of_git: false
% 1.76/1.00  
% 1.76/1.00  ------ 
% 1.76/1.00  
% 1.76/1.00  ------ Input Options
% 1.76/1.00  
% 1.76/1.00  --out_options                           all
% 1.76/1.00  --tptp_safe_out                         true
% 1.76/1.00  --problem_path                          ""
% 1.76/1.00  --include_path                          ""
% 1.76/1.00  --clausifier                            res/vclausify_rel
% 1.76/1.00  --clausifier_options                    --mode clausify
% 1.76/1.00  --stdin                                 false
% 1.76/1.00  --stats_out                             all
% 1.76/1.00  
% 1.76/1.00  ------ General Options
% 1.76/1.00  
% 1.76/1.00  --fof                                   false
% 1.76/1.00  --time_out_real                         305.
% 1.76/1.00  --time_out_virtual                      -1.
% 1.76/1.00  --symbol_type_check                     false
% 1.76/1.00  --clausify_out                          false
% 1.76/1.00  --sig_cnt_out                           false
% 1.76/1.00  --trig_cnt_out                          false
% 1.76/1.00  --trig_cnt_out_tolerance                1.
% 1.76/1.00  --trig_cnt_out_sk_spl                   false
% 1.76/1.00  --abstr_cl_out                          false
% 1.76/1.00  
% 1.76/1.00  ------ Global Options
% 1.76/1.00  
% 1.76/1.00  --schedule                              default
% 1.76/1.00  --add_important_lit                     false
% 1.76/1.00  --prop_solver_per_cl                    1000
% 1.76/1.00  --min_unsat_core                        false
% 1.76/1.00  --soft_assumptions                      false
% 1.76/1.00  --soft_lemma_size                       3
% 1.76/1.00  --prop_impl_unit_size                   0
% 1.76/1.00  --prop_impl_unit                        []
% 1.76/1.00  --share_sel_clauses                     true
% 1.76/1.00  --reset_solvers                         false
% 1.76/1.00  --bc_imp_inh                            [conj_cone]
% 1.76/1.00  --conj_cone_tolerance                   3.
% 1.76/1.00  --extra_neg_conj                        none
% 1.76/1.00  --large_theory_mode                     true
% 1.76/1.00  --prolific_symb_bound                   200
% 1.76/1.00  --lt_threshold                          2000
% 1.76/1.00  --clause_weak_htbl                      true
% 1.76/1.00  --gc_record_bc_elim                     false
% 1.76/1.00  
% 1.76/1.00  ------ Preprocessing Options
% 1.76/1.00  
% 1.76/1.00  --preprocessing_flag                    true
% 1.76/1.00  --time_out_prep_mult                    0.1
% 1.76/1.00  --splitting_mode                        input
% 1.76/1.00  --splitting_grd                         true
% 1.76/1.00  --splitting_cvd                         false
% 1.76/1.00  --splitting_cvd_svl                     false
% 1.76/1.00  --splitting_nvd                         32
% 1.76/1.00  --sub_typing                            true
% 1.76/1.00  --prep_gs_sim                           true
% 1.76/1.00  --prep_unflatten                        true
% 1.76/1.00  --prep_res_sim                          true
% 1.76/1.00  --prep_upred                            true
% 1.76/1.00  --prep_sem_filter                       exhaustive
% 1.76/1.00  --prep_sem_filter_out                   false
% 1.76/1.00  --pred_elim                             true
% 1.76/1.00  --res_sim_input                         true
% 1.76/1.00  --eq_ax_congr_red                       true
% 1.76/1.00  --pure_diseq_elim                       true
% 1.76/1.00  --brand_transform                       false
% 1.76/1.00  --non_eq_to_eq                          false
% 1.76/1.00  --prep_def_merge                        true
% 1.76/1.00  --prep_def_merge_prop_impl              false
% 1.76/1.00  --prep_def_merge_mbd                    true
% 1.76/1.00  --prep_def_merge_tr_red                 false
% 1.76/1.00  --prep_def_merge_tr_cl                  false
% 1.76/1.00  --smt_preprocessing                     true
% 1.76/1.00  --smt_ac_axioms                         fast
% 1.76/1.00  --preprocessed_out                      false
% 1.76/1.00  --preprocessed_stats                    false
% 1.76/1.00  
% 1.76/1.00  ------ Abstraction refinement Options
% 1.76/1.00  
% 1.76/1.00  --abstr_ref                             []
% 1.76/1.00  --abstr_ref_prep                        false
% 1.76/1.00  --abstr_ref_until_sat                   false
% 1.76/1.00  --abstr_ref_sig_restrict                funpre
% 1.76/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.76/1.00  --abstr_ref_under                       []
% 1.76/1.00  
% 1.76/1.00  ------ SAT Options
% 1.76/1.00  
% 1.76/1.00  --sat_mode                              false
% 1.76/1.00  --sat_fm_restart_options                ""
% 1.76/1.00  --sat_gr_def                            false
% 1.76/1.00  --sat_epr_types                         true
% 1.76/1.00  --sat_non_cyclic_types                  false
% 1.76/1.00  --sat_finite_models                     false
% 1.76/1.00  --sat_fm_lemmas                         false
% 1.76/1.00  --sat_fm_prep                           false
% 1.76/1.00  --sat_fm_uc_incr                        true
% 1.76/1.00  --sat_out_model                         small
% 1.76/1.00  --sat_out_clauses                       false
% 1.76/1.00  
% 1.76/1.00  ------ QBF Options
% 1.76/1.00  
% 1.76/1.00  --qbf_mode                              false
% 1.76/1.00  --qbf_elim_univ                         false
% 1.76/1.00  --qbf_dom_inst                          none
% 1.76/1.00  --qbf_dom_pre_inst                      false
% 1.76/1.00  --qbf_sk_in                             false
% 1.76/1.00  --qbf_pred_elim                         true
% 1.76/1.00  --qbf_split                             512
% 1.76/1.00  
% 1.76/1.00  ------ BMC1 Options
% 1.76/1.00  
% 1.76/1.00  --bmc1_incremental                      false
% 1.76/1.00  --bmc1_axioms                           reachable_all
% 1.76/1.00  --bmc1_min_bound                        0
% 1.76/1.00  --bmc1_max_bound                        -1
% 1.76/1.00  --bmc1_max_bound_default                -1
% 1.76/1.00  --bmc1_symbol_reachability              true
% 1.76/1.00  --bmc1_property_lemmas                  false
% 1.76/1.00  --bmc1_k_induction                      false
% 1.76/1.00  --bmc1_non_equiv_states                 false
% 1.76/1.00  --bmc1_deadlock                         false
% 1.76/1.00  --bmc1_ucm                              false
% 1.76/1.00  --bmc1_add_unsat_core                   none
% 1.76/1.00  --bmc1_unsat_core_children              false
% 1.76/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.76/1.00  --bmc1_out_stat                         full
% 1.76/1.00  --bmc1_ground_init                      false
% 1.76/1.00  --bmc1_pre_inst_next_state              false
% 1.76/1.00  --bmc1_pre_inst_state                   false
% 1.76/1.00  --bmc1_pre_inst_reach_state             false
% 1.76/1.00  --bmc1_out_unsat_core                   false
% 1.76/1.00  --bmc1_aig_witness_out                  false
% 1.76/1.00  --bmc1_verbose                          false
% 1.76/1.00  --bmc1_dump_clauses_tptp                false
% 1.76/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.76/1.00  --bmc1_dump_file                        -
% 1.76/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.76/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.76/1.00  --bmc1_ucm_extend_mode                  1
% 1.76/1.00  --bmc1_ucm_init_mode                    2
% 1.76/1.00  --bmc1_ucm_cone_mode                    none
% 1.76/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.76/1.00  --bmc1_ucm_relax_model                  4
% 1.76/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.76/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.76/1.00  --bmc1_ucm_layered_model                none
% 1.76/1.00  --bmc1_ucm_max_lemma_size               10
% 1.76/1.00  
% 1.76/1.00  ------ AIG Options
% 1.76/1.00  
% 1.76/1.00  --aig_mode                              false
% 1.76/1.00  
% 1.76/1.00  ------ Instantiation Options
% 1.76/1.00  
% 1.76/1.00  --instantiation_flag                    true
% 1.76/1.00  --inst_sos_flag                         false
% 1.76/1.00  --inst_sos_phase                        true
% 1.76/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.76/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.76/1.00  --inst_lit_sel_side                     num_symb
% 1.76/1.00  --inst_solver_per_active                1400
% 1.76/1.00  --inst_solver_calls_frac                1.
% 1.76/1.00  --inst_passive_queue_type               priority_queues
% 1.76/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.76/1.00  --inst_passive_queues_freq              [25;2]
% 1.76/1.00  --inst_dismatching                      true
% 1.76/1.00  --inst_eager_unprocessed_to_passive     true
% 1.76/1.00  --inst_prop_sim_given                   true
% 1.76/1.00  --inst_prop_sim_new                     false
% 1.76/1.00  --inst_subs_new                         false
% 1.76/1.00  --inst_eq_res_simp                      false
% 1.76/1.00  --inst_subs_given                       false
% 1.76/1.00  --inst_orphan_elimination               true
% 1.76/1.00  --inst_learning_loop_flag               true
% 1.76/1.00  --inst_learning_start                   3000
% 1.76/1.00  --inst_learning_factor                  2
% 1.76/1.00  --inst_start_prop_sim_after_learn       3
% 1.76/1.00  --inst_sel_renew                        solver
% 1.76/1.00  --inst_lit_activity_flag                true
% 1.76/1.00  --inst_restr_to_given                   false
% 1.76/1.00  --inst_activity_threshold               500
% 1.76/1.00  --inst_out_proof                        true
% 1.76/1.00  
% 1.76/1.00  ------ Resolution Options
% 1.76/1.00  
% 1.76/1.00  --resolution_flag                       true
% 1.76/1.00  --res_lit_sel                           adaptive
% 1.76/1.00  --res_lit_sel_side                      none
% 1.76/1.00  --res_ordering                          kbo
% 1.76/1.00  --res_to_prop_solver                    active
% 1.76/1.00  --res_prop_simpl_new                    false
% 1.76/1.00  --res_prop_simpl_given                  true
% 1.76/1.00  --res_passive_queue_type                priority_queues
% 1.76/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.76/1.00  --res_passive_queues_freq               [15;5]
% 1.76/1.00  --res_forward_subs                      full
% 1.76/1.00  --res_backward_subs                     full
% 1.76/1.00  --res_forward_subs_resolution           true
% 1.76/1.00  --res_backward_subs_resolution          true
% 1.76/1.00  --res_orphan_elimination                true
% 1.76/1.00  --res_time_limit                        2.
% 1.76/1.00  --res_out_proof                         true
% 1.76/1.00  
% 1.76/1.00  ------ Superposition Options
% 1.76/1.00  
% 1.76/1.00  --superposition_flag                    true
% 1.76/1.00  --sup_passive_queue_type                priority_queues
% 1.76/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.76/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.76/1.00  --demod_completeness_check              fast
% 1.76/1.00  --demod_use_ground                      true
% 1.76/1.00  --sup_to_prop_solver                    passive
% 1.76/1.00  --sup_prop_simpl_new                    true
% 1.76/1.00  --sup_prop_simpl_given                  true
% 1.76/1.00  --sup_fun_splitting                     false
% 1.76/1.00  --sup_smt_interval                      50000
% 1.76/1.00  
% 1.76/1.00  ------ Superposition Simplification Setup
% 1.76/1.00  
% 1.76/1.00  --sup_indices_passive                   []
% 1.76/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.76/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/1.00  --sup_full_bw                           [BwDemod]
% 1.76/1.00  --sup_immed_triv                        [TrivRules]
% 1.76/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.76/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/1.00  --sup_immed_bw_main                     []
% 1.76/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.76/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/1.00  
% 1.76/1.00  ------ Combination Options
% 1.76/1.00  
% 1.76/1.00  --comb_res_mult                         3
% 1.76/1.00  --comb_sup_mult                         2
% 1.76/1.00  --comb_inst_mult                        10
% 1.76/1.00  
% 1.76/1.00  ------ Debug Options
% 1.76/1.00  
% 1.76/1.00  --dbg_backtrace                         false
% 1.76/1.00  --dbg_dump_prop_clauses                 false
% 1.76/1.00  --dbg_dump_prop_clauses_file            -
% 1.76/1.00  --dbg_out_stat                          false
% 1.76/1.00  ------ Parsing...
% 1.76/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.76/1.00  
% 1.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.76/1.00  
% 1.76/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.76/1.00  
% 1.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.76/1.00  ------ Proving...
% 1.76/1.00  ------ Problem Properties 
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  clauses                                 22
% 1.76/1.00  conjectures                             3
% 1.76/1.00  EPR                                     9
% 1.76/1.00  Horn                                    16
% 1.76/1.00  unary                                   8
% 1.76/1.00  binary                                  7
% 1.76/1.00  lits                                    45
% 1.76/1.00  lits eq                                 13
% 1.76/1.00  fd_pure                                 0
% 1.76/1.00  fd_pseudo                               0
% 1.76/1.00  fd_cond                                 0
% 1.76/1.00  fd_pseudo_cond                          1
% 1.76/1.00  AC symbols                              0
% 1.76/1.00  
% 1.76/1.00  ------ Schedule dynamic 5 is on 
% 1.76/1.00  
% 1.76/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  ------ 
% 1.76/1.00  Current options:
% 1.76/1.00  ------ 
% 1.76/1.00  
% 1.76/1.00  ------ Input Options
% 1.76/1.00  
% 1.76/1.00  --out_options                           all
% 1.76/1.00  --tptp_safe_out                         true
% 1.76/1.00  --problem_path                          ""
% 1.76/1.00  --include_path                          ""
% 1.76/1.00  --clausifier                            res/vclausify_rel
% 1.76/1.00  --clausifier_options                    --mode clausify
% 1.76/1.00  --stdin                                 false
% 1.76/1.00  --stats_out                             all
% 1.76/1.00  
% 1.76/1.00  ------ General Options
% 1.76/1.00  
% 1.76/1.00  --fof                                   false
% 1.76/1.00  --time_out_real                         305.
% 1.76/1.00  --time_out_virtual                      -1.
% 1.76/1.00  --symbol_type_check                     false
% 1.76/1.00  --clausify_out                          false
% 1.76/1.00  --sig_cnt_out                           false
% 1.76/1.00  --trig_cnt_out                          false
% 1.76/1.00  --trig_cnt_out_tolerance                1.
% 1.76/1.00  --trig_cnt_out_sk_spl                   false
% 1.76/1.00  --abstr_cl_out                          false
% 1.76/1.00  
% 1.76/1.00  ------ Global Options
% 1.76/1.00  
% 1.76/1.00  --schedule                              default
% 1.76/1.00  --add_important_lit                     false
% 1.76/1.00  --prop_solver_per_cl                    1000
% 1.76/1.00  --min_unsat_core                        false
% 1.76/1.00  --soft_assumptions                      false
% 1.76/1.00  --soft_lemma_size                       3
% 1.76/1.00  --prop_impl_unit_size                   0
% 1.76/1.00  --prop_impl_unit                        []
% 1.76/1.00  --share_sel_clauses                     true
% 1.76/1.00  --reset_solvers                         false
% 1.76/1.00  --bc_imp_inh                            [conj_cone]
% 1.76/1.00  --conj_cone_tolerance                   3.
% 1.76/1.00  --extra_neg_conj                        none
% 1.76/1.00  --large_theory_mode                     true
% 1.76/1.00  --prolific_symb_bound                   200
% 1.76/1.00  --lt_threshold                          2000
% 1.76/1.00  --clause_weak_htbl                      true
% 1.76/1.00  --gc_record_bc_elim                     false
% 1.76/1.00  
% 1.76/1.00  ------ Preprocessing Options
% 1.76/1.00  
% 1.76/1.00  --preprocessing_flag                    true
% 1.76/1.00  --time_out_prep_mult                    0.1
% 1.76/1.00  --splitting_mode                        input
% 1.76/1.00  --splitting_grd                         true
% 1.76/1.00  --splitting_cvd                         false
% 1.76/1.00  --splitting_cvd_svl                     false
% 1.76/1.00  --splitting_nvd                         32
% 1.76/1.00  --sub_typing                            true
% 1.76/1.00  --prep_gs_sim                           true
% 1.76/1.00  --prep_unflatten                        true
% 1.76/1.00  --prep_res_sim                          true
% 1.76/1.00  --prep_upred                            true
% 1.76/1.00  --prep_sem_filter                       exhaustive
% 1.76/1.00  --prep_sem_filter_out                   false
% 1.76/1.00  --pred_elim                             true
% 1.76/1.00  --res_sim_input                         true
% 1.76/1.00  --eq_ax_congr_red                       true
% 1.76/1.00  --pure_diseq_elim                       true
% 1.76/1.00  --brand_transform                       false
% 1.76/1.00  --non_eq_to_eq                          false
% 1.76/1.00  --prep_def_merge                        true
% 1.76/1.00  --prep_def_merge_prop_impl              false
% 1.76/1.00  --prep_def_merge_mbd                    true
% 1.76/1.00  --prep_def_merge_tr_red                 false
% 1.76/1.00  --prep_def_merge_tr_cl                  false
% 1.76/1.00  --smt_preprocessing                     true
% 1.76/1.00  --smt_ac_axioms                         fast
% 1.76/1.00  --preprocessed_out                      false
% 1.76/1.00  --preprocessed_stats                    false
% 1.76/1.00  
% 1.76/1.00  ------ Abstraction refinement Options
% 1.76/1.00  
% 1.76/1.00  --abstr_ref                             []
% 1.76/1.00  --abstr_ref_prep                        false
% 1.76/1.00  --abstr_ref_until_sat                   false
% 1.76/1.00  --abstr_ref_sig_restrict                funpre
% 1.76/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.76/1.00  --abstr_ref_under                       []
% 1.76/1.00  
% 1.76/1.00  ------ SAT Options
% 1.76/1.00  
% 1.76/1.00  --sat_mode                              false
% 1.76/1.00  --sat_fm_restart_options                ""
% 1.76/1.00  --sat_gr_def                            false
% 1.76/1.00  --sat_epr_types                         true
% 1.76/1.00  --sat_non_cyclic_types                  false
% 1.76/1.00  --sat_finite_models                     false
% 1.76/1.00  --sat_fm_lemmas                         false
% 1.76/1.00  --sat_fm_prep                           false
% 1.76/1.00  --sat_fm_uc_incr                        true
% 1.76/1.00  --sat_out_model                         small
% 1.76/1.00  --sat_out_clauses                       false
% 1.76/1.00  
% 1.76/1.00  ------ QBF Options
% 1.76/1.00  
% 1.76/1.00  --qbf_mode                              false
% 1.76/1.00  --qbf_elim_univ                         false
% 1.76/1.00  --qbf_dom_inst                          none
% 1.76/1.00  --qbf_dom_pre_inst                      false
% 1.76/1.00  --qbf_sk_in                             false
% 1.76/1.00  --qbf_pred_elim                         true
% 1.76/1.00  --qbf_split                             512
% 1.76/1.00  
% 1.76/1.00  ------ BMC1 Options
% 1.76/1.00  
% 1.76/1.00  --bmc1_incremental                      false
% 1.76/1.00  --bmc1_axioms                           reachable_all
% 1.76/1.00  --bmc1_min_bound                        0
% 1.76/1.00  --bmc1_max_bound                        -1
% 1.76/1.00  --bmc1_max_bound_default                -1
% 1.76/1.00  --bmc1_symbol_reachability              true
% 1.76/1.00  --bmc1_property_lemmas                  false
% 1.76/1.00  --bmc1_k_induction                      false
% 1.76/1.00  --bmc1_non_equiv_states                 false
% 1.76/1.00  --bmc1_deadlock                         false
% 1.76/1.00  --bmc1_ucm                              false
% 1.76/1.00  --bmc1_add_unsat_core                   none
% 1.76/1.00  --bmc1_unsat_core_children              false
% 1.76/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.76/1.00  --bmc1_out_stat                         full
% 1.76/1.00  --bmc1_ground_init                      false
% 1.76/1.00  --bmc1_pre_inst_next_state              false
% 1.76/1.00  --bmc1_pre_inst_state                   false
% 1.76/1.00  --bmc1_pre_inst_reach_state             false
% 1.76/1.00  --bmc1_out_unsat_core                   false
% 1.76/1.00  --bmc1_aig_witness_out                  false
% 1.76/1.00  --bmc1_verbose                          false
% 1.76/1.00  --bmc1_dump_clauses_tptp                false
% 1.76/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.76/1.00  --bmc1_dump_file                        -
% 1.76/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.76/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.76/1.00  --bmc1_ucm_extend_mode                  1
% 1.76/1.00  --bmc1_ucm_init_mode                    2
% 1.76/1.00  --bmc1_ucm_cone_mode                    none
% 1.76/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.76/1.00  --bmc1_ucm_relax_model                  4
% 1.76/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.76/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.76/1.00  --bmc1_ucm_layered_model                none
% 1.76/1.00  --bmc1_ucm_max_lemma_size               10
% 1.76/1.00  
% 1.76/1.00  ------ AIG Options
% 1.76/1.00  
% 1.76/1.00  --aig_mode                              false
% 1.76/1.00  
% 1.76/1.00  ------ Instantiation Options
% 1.76/1.00  
% 1.76/1.00  --instantiation_flag                    true
% 1.76/1.00  --inst_sos_flag                         false
% 1.76/1.00  --inst_sos_phase                        true
% 1.76/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.76/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.76/1.00  --inst_lit_sel_side                     none
% 1.76/1.00  --inst_solver_per_active                1400
% 1.76/1.00  --inst_solver_calls_frac                1.
% 1.76/1.00  --inst_passive_queue_type               priority_queues
% 1.76/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.76/1.00  --inst_passive_queues_freq              [25;2]
% 1.76/1.00  --inst_dismatching                      true
% 1.76/1.00  --inst_eager_unprocessed_to_passive     true
% 1.76/1.00  --inst_prop_sim_given                   true
% 1.76/1.00  --inst_prop_sim_new                     false
% 1.76/1.00  --inst_subs_new                         false
% 1.76/1.00  --inst_eq_res_simp                      false
% 1.76/1.00  --inst_subs_given                       false
% 1.76/1.00  --inst_orphan_elimination               true
% 1.76/1.00  --inst_learning_loop_flag               true
% 1.76/1.00  --inst_learning_start                   3000
% 1.76/1.00  --inst_learning_factor                  2
% 1.76/1.00  --inst_start_prop_sim_after_learn       3
% 1.76/1.00  --inst_sel_renew                        solver
% 1.76/1.00  --inst_lit_activity_flag                true
% 1.76/1.00  --inst_restr_to_given                   false
% 1.76/1.00  --inst_activity_threshold               500
% 1.76/1.00  --inst_out_proof                        true
% 1.76/1.00  
% 1.76/1.00  ------ Resolution Options
% 1.76/1.00  
% 1.76/1.00  --resolution_flag                       false
% 1.76/1.00  --res_lit_sel                           adaptive
% 1.76/1.00  --res_lit_sel_side                      none
% 1.76/1.00  --res_ordering                          kbo
% 1.76/1.00  --res_to_prop_solver                    active
% 1.76/1.00  --res_prop_simpl_new                    false
% 1.76/1.00  --res_prop_simpl_given                  true
% 1.76/1.00  --res_passive_queue_type                priority_queues
% 1.76/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.76/1.00  --res_passive_queues_freq               [15;5]
% 1.76/1.00  --res_forward_subs                      full
% 1.76/1.00  --res_backward_subs                     full
% 1.76/1.00  --res_forward_subs_resolution           true
% 1.76/1.00  --res_backward_subs_resolution          true
% 1.76/1.00  --res_orphan_elimination                true
% 1.76/1.00  --res_time_limit                        2.
% 1.76/1.00  --res_out_proof                         true
% 1.76/1.00  
% 1.76/1.00  ------ Superposition Options
% 1.76/1.00  
% 1.76/1.00  --superposition_flag                    true
% 1.76/1.00  --sup_passive_queue_type                priority_queues
% 1.76/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.76/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.76/1.00  --demod_completeness_check              fast
% 1.76/1.00  --demod_use_ground                      true
% 1.76/1.00  --sup_to_prop_solver                    passive
% 1.76/1.00  --sup_prop_simpl_new                    true
% 1.76/1.00  --sup_prop_simpl_given                  true
% 1.76/1.00  --sup_fun_splitting                     false
% 1.76/1.00  --sup_smt_interval                      50000
% 1.76/1.00  
% 1.76/1.00  ------ Superposition Simplification Setup
% 1.76/1.00  
% 1.76/1.00  --sup_indices_passive                   []
% 1.76/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.76/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/1.00  --sup_full_bw                           [BwDemod]
% 1.76/1.00  --sup_immed_triv                        [TrivRules]
% 1.76/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.76/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/1.00  --sup_immed_bw_main                     []
% 1.76/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.76/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/1.00  
% 1.76/1.00  ------ Combination Options
% 1.76/1.00  
% 1.76/1.00  --comb_res_mult                         3
% 1.76/1.00  --comb_sup_mult                         2
% 1.76/1.00  --comb_inst_mult                        10
% 1.76/1.00  
% 1.76/1.00  ------ Debug Options
% 1.76/1.00  
% 1.76/1.00  --dbg_backtrace                         false
% 1.76/1.00  --dbg_dump_prop_clauses                 false
% 1.76/1.00  --dbg_dump_prop_clauses_file            -
% 1.76/1.00  --dbg_out_stat                          false
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  ------ Proving...
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  % SZS status Theorem for theBenchmark.p
% 1.76/1.00  
% 1.76/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.76/1.00  
% 1.76/1.00  fof(f12,conjecture,(
% 1.76/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f13,negated_conjecture,(
% 1.76/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.76/1.00    inference(negated_conjecture,[],[f12])).
% 1.76/1.00  
% 1.76/1.00  fof(f23,plain,(
% 1.76/1.00    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.76/1.00    inference(ennf_transformation,[],[f13])).
% 1.76/1.00  
% 1.76/1.00  fof(f24,plain,(
% 1.76/1.00    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.76/1.00    inference(flattening,[],[f23])).
% 1.76/1.00  
% 1.76/1.00  fof(f32,plain,(
% 1.76/1.00    ( ! [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) != sK2 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK2))) )),
% 1.76/1.00    introduced(choice_axiom,[])).
% 1.76/1.00  
% 1.76/1.00  fof(f31,plain,(
% 1.76/1.00    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 1.76/1.00    introduced(choice_axiom,[])).
% 1.76/1.00  
% 1.76/1.00  fof(f33,plain,(
% 1.76/1.00    (k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != sK2 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)),
% 1.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f32,f31])).
% 1.76/1.00  
% 1.76/1.00  fof(f58,plain,(
% 1.76/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))),
% 1.76/1.00    inference(cnf_transformation,[],[f33])).
% 1.76/1.00  
% 1.76/1.00  fof(f7,axiom,(
% 1.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f15,plain,(
% 1.76/1.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.76/1.00    inference(ennf_transformation,[],[f7])).
% 1.76/1.00  
% 1.76/1.00  fof(f47,plain,(
% 1.76/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.76/1.00    inference(cnf_transformation,[],[f15])).
% 1.76/1.00  
% 1.76/1.00  fof(f57,plain,(
% 1.76/1.00    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 1.76/1.00    inference(cnf_transformation,[],[f33])).
% 1.76/1.00  
% 1.76/1.00  fof(f10,axiom,(
% 1.76/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 1.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f19,plain,(
% 1.76/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.76/1.00    inference(ennf_transformation,[],[f10])).
% 1.76/1.00  
% 1.76/1.00  fof(f20,plain,(
% 1.76/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.76/1.00    inference(flattening,[],[f19])).
% 1.76/1.00  
% 1.76/1.00  fof(f50,plain,(
% 1.76/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.76/1.00    inference(cnf_transformation,[],[f20])).
% 1.76/1.00  
% 1.76/1.00  fof(f53,plain,(
% 1.76/1.00    l1_struct_0(sK1)),
% 1.76/1.00    inference(cnf_transformation,[],[f33])).
% 1.76/1.00  
% 1.76/1.00  fof(f52,plain,(
% 1.76/1.00    ~v2_struct_0(sK1)),
% 1.76/1.00    inference(cnf_transformation,[],[f33])).
% 1.76/1.00  
% 1.76/1.00  fof(f54,plain,(
% 1.76/1.00    ~v1_xboole_0(sK2)),
% 1.76/1.00    inference(cnf_transformation,[],[f33])).
% 1.76/1.00  
% 1.76/1.00  fof(f56,plain,(
% 1.76/1.00    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 1.76/1.00    inference(cnf_transformation,[],[f33])).
% 1.76/1.00  
% 1.76/1.00  fof(f1,axiom,(
% 1.76/1.00    v1_xboole_0(k1_xboole_0)),
% 1.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f34,plain,(
% 1.76/1.00    v1_xboole_0(k1_xboole_0)),
% 1.76/1.00    inference(cnf_transformation,[],[f1])).
% 1.76/1.00  
% 1.76/1.00  fof(f5,axiom,(
% 1.76/1.00    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f29,plain,(
% 1.76/1.00    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.76/1.00    inference(nnf_transformation,[],[f5])).
% 1.76/1.00  
% 1.76/1.00  fof(f42,plain,(
% 1.76/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.76/1.00    inference(cnf_transformation,[],[f29])).
% 1.76/1.00  
% 1.76/1.00  fof(f11,axiom,(
% 1.76/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 1.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f21,plain,(
% 1.76/1.00    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.76/1.00    inference(ennf_transformation,[],[f11])).
% 1.76/1.00  
% 1.76/1.00  fof(f22,plain,(
% 1.76/1.00    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.76/1.00    inference(flattening,[],[f21])).
% 1.76/1.00  
% 1.76/1.00  fof(f51,plain,(
% 1.76/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.76/1.00    inference(cnf_transformation,[],[f22])).
% 1.76/1.00  
% 1.76/1.00  fof(f55,plain,(
% 1.76/1.00    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))),
% 1.76/1.00    inference(cnf_transformation,[],[f33])).
% 1.76/1.00  
% 1.76/1.00  fof(f9,axiom,(
% 1.76/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.76/1.00  
% 1.76/1.00  fof(f17,plain,(
% 1.76/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.76/1.00    inference(ennf_transformation,[],[f9])).
% 1.76/1.00  
% 1.76/1.00  fof(f18,plain,(
% 1.76/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.76/1.00    inference(flattening,[],[f17])).
% 1.76/1.00  
% 1.76/1.00  fof(f49,plain,(
% 1.76/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.76/1.00    inference(cnf_transformation,[],[f18])).
% 1.76/1.00  
% 1.76/1.00  fof(f59,plain,(
% 1.76/1.00    k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != sK2),
% 1.76/1.00    inference(cnf_transformation,[],[f33])).
% 1.76/1.00  
% 1.76/1.00  cnf(c_19,negated_conjecture,
% 1.76/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) ),
% 1.76/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1404,plain,
% 1.76/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) = iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_13,plain,
% 1.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.76/1.00      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 1.76/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1406,plain,
% 1.76/1.00      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 1.76/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_2188,plain,
% 1.76/1.00      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))),sK2,X0) = k4_xboole_0(sK2,X0) ),
% 1.76/1.00      inference(superposition,[status(thm)],[c_1404,c_1406]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_20,negated_conjecture,
% 1.76/1.00      ( v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
% 1.76/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_16,plain,
% 1.76/1.00      ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
% 1.76/1.00      | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
% 1.76/1.00      | v2_struct_0(X1)
% 1.76/1.00      | ~ l1_struct_0(X1)
% 1.76/1.00      | v1_xboole_0(X0)
% 1.76/1.00      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
% 1.76/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_24,negated_conjecture,
% 1.76/1.00      ( l1_struct_0(sK1) ),
% 1.76/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_365,plain,
% 1.76/1.00      ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
% 1.76/1.00      | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
% 1.76/1.00      | v2_struct_0(X1)
% 1.76/1.00      | v1_xboole_0(X0)
% 1.76/1.00      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
% 1.76/1.00      | sK1 != X1 ),
% 1.76/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_366,plain,
% 1.76/1.00      ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
% 1.76/1.00      | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
% 1.76/1.00      | v2_struct_0(sK1)
% 1.76/1.00      | v1_xboole_0(X0)
% 1.76/1.00      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) ),
% 1.76/1.00      inference(unflattening,[status(thm)],[c_365]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_25,negated_conjecture,
% 1.76/1.00      ( ~ v2_struct_0(sK1) ),
% 1.76/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_370,plain,
% 1.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
% 1.76/1.00      | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
% 1.76/1.00      | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
% 1.76/1.00      | v1_xboole_0(X0)
% 1.76/1.00      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) ),
% 1.76/1.00      inference(global_propositional_subsumption,
% 1.76/1.00                [status(thm)],
% 1.76/1.00                [c_366,c_25]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_371,plain,
% 1.76/1.00      ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
% 1.76/1.00      | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
% 1.76/1.00      | v1_xboole_0(X0)
% 1.76/1.00      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) ),
% 1.76/1.00      inference(renaming,[status(thm)],[c_370]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_427,plain,
% 1.76/1.00      ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK1)))
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
% 1.76/1.00      | v1_xboole_0(X0)
% 1.76/1.00      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0))
% 1.76/1.00      | k3_yellow_1(k2_struct_0(sK1)) != k3_yellow_1(k2_struct_0(sK1))
% 1.76/1.00      | sK2 != X0 ),
% 1.76/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_371]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_428,plain,
% 1.76/1.00      ( ~ v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))
% 1.76/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
% 1.76/1.00      | v1_xboole_0(sK2)
% 1.76/1.00      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))),sK2,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 1.76/1.00      inference(unflattening,[status(thm)],[c_427]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_23,negated_conjecture,
% 1.76/1.00      ( ~ v1_xboole_0(sK2) ),
% 1.76/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_21,negated_conjecture,
% 1.76/1.00      ( v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
% 1.76/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_430,plain,
% 1.76/1.00      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))),sK2,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 1.76/1.00      inference(global_propositional_subsumption,
% 1.76/1.00                [status(thm)],
% 1.76/1.00                [c_428,c_23,c_21,c_19]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_2528,plain,
% 1.76/1.00      ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = k4_xboole_0(sK2,k1_tarski(k1_xboole_0)) ),
% 1.76/1.00      inference(demodulation,[status(thm)],[c_2188,c_430]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_0,plain,
% 1.76/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 1.76/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1417,plain,
% 1.76/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_7,plain,
% 1.76/1.00      ( r2_hidden(X0,X1) | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
% 1.76/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1411,plain,
% 1.76/1.00      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
% 1.76/1.00      | r2_hidden(X1,X0) = iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_17,plain,
% 1.76/1.00      ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
% 1.76/1.00      | ~ v2_waybel_0(X0,k3_yellow_1(X1))
% 1.76/1.00      | ~ v13_waybel_0(X0,k3_yellow_1(X1))
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
% 1.76/1.00      | ~ r2_hidden(X2,X0)
% 1.76/1.00      | ~ v1_xboole_0(X2)
% 1.76/1.00      | v1_xboole_0(X0)
% 1.76/1.00      | v1_xboole_0(X1) ),
% 1.76/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_22,negated_conjecture,
% 1.76/1.00      ( v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) ),
% 1.76/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_317,plain,
% 1.76/1.00      ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
% 1.76/1.00      | ~ v13_waybel_0(X0,k3_yellow_1(X1))
% 1.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
% 1.76/1.00      | ~ r2_hidden(X2,X0)
% 1.76/1.00      | ~ v1_xboole_0(X2)
% 1.76/1.00      | v1_xboole_0(X0)
% 1.76/1.00      | v1_xboole_0(X1)
% 1.76/1.00      | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X1))
% 1.76/1.00      | sK2 != X0 ),
% 1.76/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_318,plain,
% 1.76/1.00      ( ~ v2_waybel_0(sK2,k3_yellow_1(X0))
% 1.76/1.00      | ~ v13_waybel_0(sK2,k3_yellow_1(X0))
% 1.76/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.76/1.00      | ~ r2_hidden(X1,sK2)
% 1.76/1.00      | ~ v1_xboole_0(X1)
% 1.76/1.00      | v1_xboole_0(X0)
% 1.76/1.00      | v1_xboole_0(sK2)
% 1.76/1.00      | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0)) ),
% 1.76/1.00      inference(unflattening,[status(thm)],[c_317]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_320,plain,
% 1.76/1.00      ( v1_xboole_0(X0)
% 1.76/1.00      | ~ v1_xboole_0(X1)
% 1.76/1.00      | ~ r2_hidden(X1,sK2)
% 1.76/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.76/1.00      | ~ v13_waybel_0(sK2,k3_yellow_1(X0))
% 1.76/1.00      | ~ v2_waybel_0(sK2,k3_yellow_1(X0))
% 1.76/1.00      | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0)) ),
% 1.76/1.00      inference(global_propositional_subsumption,
% 1.76/1.00                [status(thm)],
% 1.76/1.00                [c_318,c_23]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_321,plain,
% 1.76/1.00      ( ~ v2_waybel_0(sK2,k3_yellow_1(X0))
% 1.76/1.00      | ~ v13_waybel_0(sK2,k3_yellow_1(X0))
% 1.76/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.76/1.00      | ~ r2_hidden(X1,sK2)
% 1.76/1.00      | ~ v1_xboole_0(X1)
% 1.76/1.00      | v1_xboole_0(X0)
% 1.76/1.00      | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0)) ),
% 1.76/1.00      inference(renaming,[status(thm)],[c_320]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_400,plain,
% 1.76/1.00      ( ~ v2_waybel_0(sK2,k3_yellow_1(X0))
% 1.76/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.76/1.00      | ~ r2_hidden(X1,sK2)
% 1.76/1.00      | ~ v1_xboole_0(X1)
% 1.76/1.00      | v1_xboole_0(X0)
% 1.76/1.00      | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0))
% 1.76/1.00      | k3_yellow_1(k2_struct_0(sK1)) != k3_yellow_1(X0)
% 1.76/1.00      | sK2 != sK2 ),
% 1.76/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_321]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_445,plain,
% 1.76/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.76/1.00      | ~ r2_hidden(X1,sK2)
% 1.76/1.00      | ~ v1_xboole_0(X1)
% 1.76/1.00      | v1_xboole_0(X0)
% 1.76/1.00      | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0))
% 1.76/1.00      | k3_yellow_1(k2_struct_0(sK1)) != k3_yellow_1(X0)
% 1.76/1.00      | sK2 != sK2 ),
% 1.76/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_400]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_641,plain,
% 1.76/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.76/1.00      | ~ r2_hidden(X1,sK2)
% 1.76/1.00      | ~ v1_xboole_0(X1)
% 1.76/1.00      | v1_xboole_0(X0)
% 1.76/1.00      | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0))
% 1.76/1.00      | k3_yellow_1(k2_struct_0(sK1)) != k3_yellow_1(X0) ),
% 1.76/1.00      inference(equality_resolution_simp,[status(thm)],[c_445]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_925,plain,
% 1.76/1.00      ( ~ r2_hidden(X0,sK2) | ~ v1_xboole_0(X0) | ~ sP0_iProver_split ),
% 1.76/1.00      inference(splitting,
% 1.76/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.76/1.00                [c_641]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1401,plain,
% 1.76/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 1.76/1.00      | v1_xboole_0(X0) != iProver_top
% 1.76/1.00      | sP0_iProver_split != iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_925]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1835,plain,
% 1.76/1.00      ( k4_xboole_0(sK2,k1_tarski(X0)) = sK2
% 1.76/1.00      | v1_xboole_0(X0) != iProver_top
% 1.76/1.00      | sP0_iProver_split != iProver_top ),
% 1.76/1.00      inference(superposition,[status(thm)],[c_1411,c_1401]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_26,plain,
% 1.76/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_27,plain,
% 1.76/1.00      ( l1_struct_0(sK1) = iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_32,plain,
% 1.76/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) = iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_15,plain,
% 1.76/1.00      ( v2_struct_0(X0)
% 1.76/1.00      | ~ l1_struct_0(X0)
% 1.76/1.00      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 1.76/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_37,plain,
% 1.76/1.00      ( v2_struct_0(X0) = iProver_top
% 1.76/1.00      | l1_struct_0(X0) != iProver_top
% 1.76/1.00      | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_39,plain,
% 1.76/1.00      ( v2_struct_0(sK1) = iProver_top
% 1.76/1.00      | l1_struct_0(sK1) != iProver_top
% 1.76/1.00      | v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_37]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_927,plain,
% 1.76/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 1.76/1.00      inference(splitting,
% 1.76/1.00                [splitting(split),new_symbols(definition,[])],
% 1.76/1.00                [c_641]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_957,plain,
% 1.76/1.00      ( sP1_iProver_split = iProver_top
% 1.76/1.00      | sP0_iProver_split = iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_929,plain,( X0 = X0 ),theory(equality) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1625,plain,
% 1.76/1.00      ( k3_yellow_1(k2_struct_0(sK1)) = k3_yellow_1(k2_struct_0(sK1)) ),
% 1.76/1.00      inference(instantiation,[status(thm)],[c_929]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_926,plain,
% 1.76/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
% 1.76/1.00      | v1_xboole_0(X0)
% 1.76/1.00      | u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0))
% 1.76/1.00      | k3_yellow_1(k2_struct_0(sK1)) != k3_yellow_1(X0)
% 1.76/1.00      | ~ sP1_iProver_split ),
% 1.76/1.00      inference(splitting,
% 1.76/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.76/1.00                [c_641]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1400,plain,
% 1.76/1.00      ( u1_struct_0(k3_yellow_1(k2_struct_0(sK1))) != u1_struct_0(k3_yellow_1(X0))
% 1.76/1.00      | k3_yellow_1(k2_struct_0(sK1)) != k3_yellow_1(X0)
% 1.76/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) != iProver_top
% 1.76/1.00      | v1_xboole_0(X0) = iProver_top
% 1.76/1.00      | sP1_iProver_split != iProver_top ),
% 1.76/1.00      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1635,plain,
% 1.76/1.00      ( k3_yellow_1(k2_struct_0(sK1)) != k3_yellow_1(k2_struct_0(sK1))
% 1.76/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) != iProver_top
% 1.76/1.00      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
% 1.76/1.00      | sP1_iProver_split != iProver_top ),
% 1.76/1.00      inference(equality_resolution,[status(thm)],[c_1400]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1853,plain,
% 1.76/1.00      ( v1_xboole_0(X0) != iProver_top
% 1.76/1.00      | k4_xboole_0(sK2,k1_tarski(X0)) = sK2 ),
% 1.76/1.00      inference(global_propositional_subsumption,
% 1.76/1.00                [status(thm)],
% 1.76/1.00                [c_1835,c_26,c_27,c_32,c_39,c_957,c_1625,c_1635]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1854,plain,
% 1.76/1.00      ( k4_xboole_0(sK2,k1_tarski(X0)) = sK2
% 1.76/1.00      | v1_xboole_0(X0) != iProver_top ),
% 1.76/1.00      inference(renaming,[status(thm)],[c_1853]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_1861,plain,
% 1.76/1.00      ( k4_xboole_0(sK2,k1_tarski(k1_xboole_0)) = sK2 ),
% 1.76/1.00      inference(superposition,[status(thm)],[c_1417,c_1854]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_2529,plain,
% 1.76/1.00      ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
% 1.76/1.00      inference(light_normalisation,[status(thm)],[c_2528,c_1861]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(c_18,negated_conjecture,
% 1.76/1.00      ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != sK2 ),
% 1.76/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.76/1.00  
% 1.76/1.00  cnf(contradiction,plain,
% 1.76/1.00      ( $false ),
% 1.76/1.00      inference(minisat,[status(thm)],[c_2529,c_18]) ).
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.76/1.00  
% 1.76/1.00  ------                               Statistics
% 1.76/1.00  
% 1.76/1.00  ------ General
% 1.76/1.00  
% 1.76/1.00  abstr_ref_over_cycles:                  0
% 1.76/1.00  abstr_ref_under_cycles:                 0
% 1.76/1.00  gc_basic_clause_elim:                   0
% 1.76/1.00  forced_gc_time:                         0
% 1.76/1.00  parsing_time:                           0.008
% 1.76/1.00  unif_index_cands_time:                  0.
% 1.76/1.00  unif_index_add_time:                    0.
% 1.76/1.00  orderings_time:                         0.
% 1.76/1.00  out_proof_time:                         0.007
% 1.76/1.00  total_time:                             0.105
% 1.76/1.00  num_of_symbols:                         55
% 1.76/1.00  num_of_terms:                           1736
% 1.76/1.00  
% 1.76/1.00  ------ Preprocessing
% 1.76/1.00  
% 1.76/1.00  num_of_splits:                          2
% 1.76/1.00  num_of_split_atoms:                     2
% 1.76/1.00  num_of_reused_defs:                     0
% 1.76/1.00  num_eq_ax_congr_red:                    11
% 1.76/1.00  num_of_sem_filtered_clauses:            1
% 1.76/1.00  num_of_subtypes:                        0
% 1.76/1.00  monotx_restored_types:                  0
% 1.76/1.00  sat_num_of_epr_types:                   0
% 1.76/1.00  sat_num_of_non_cyclic_types:            0
% 1.76/1.00  sat_guarded_non_collapsed_types:        0
% 1.76/1.00  num_pure_diseq_elim:                    0
% 1.76/1.00  simp_replaced_by:                       0
% 1.76/1.00  res_preprocessed:                       118
% 1.76/1.00  prep_upred:                             0
% 1.76/1.00  prep_unflattend:                        30
% 1.76/1.00  smt_new_axioms:                         0
% 1.76/1.00  pred_elim_cands:                        3
% 1.76/1.00  pred_elim:                              5
% 1.76/1.00  pred_elim_cl:                           5
% 1.76/1.00  pred_elim_cycles:                       7
% 1.76/1.00  merged_defs:                            8
% 1.76/1.00  merged_defs_ncl:                        0
% 1.76/1.00  bin_hyper_res:                          8
% 1.76/1.00  prep_cycles:                            4
% 1.76/1.00  pred_elim_time:                         0.012
% 1.76/1.00  splitting_time:                         0.
% 1.76/1.00  sem_filter_time:                        0.
% 1.76/1.00  monotx_time:                            0.001
% 1.76/1.00  subtype_inf_time:                       0.
% 1.76/1.00  
% 1.76/1.00  ------ Problem properties
% 1.76/1.00  
% 1.76/1.00  clauses:                                22
% 1.76/1.00  conjectures:                            3
% 1.76/1.00  epr:                                    9
% 1.76/1.00  horn:                                   16
% 1.76/1.00  ground:                                 9
% 1.76/1.00  unary:                                  8
% 1.76/1.00  binary:                                 7
% 1.76/1.00  lits:                                   45
% 1.76/1.00  lits_eq:                                13
% 1.76/1.00  fd_pure:                                0
% 1.76/1.00  fd_pseudo:                              0
% 1.76/1.00  fd_cond:                                0
% 1.76/1.00  fd_pseudo_cond:                         1
% 1.76/1.00  ac_symbols:                             0
% 1.76/1.00  
% 1.76/1.00  ------ Propositional Solver
% 1.76/1.00  
% 1.76/1.00  prop_solver_calls:                      26
% 1.76/1.00  prop_fast_solver_calls:                 692
% 1.76/1.00  smt_solver_calls:                       0
% 1.76/1.00  smt_fast_solver_calls:                  0
% 1.76/1.00  prop_num_of_clauses:                    710
% 1.76/1.00  prop_preprocess_simplified:             3670
% 1.76/1.00  prop_fo_subsumed:                       14
% 1.76/1.00  prop_solver_time:                       0.
% 1.76/1.00  smt_solver_time:                        0.
% 1.76/1.00  smt_fast_solver_time:                   0.
% 1.76/1.00  prop_fast_solver_time:                  0.
% 1.76/1.00  prop_unsat_core_time:                   0.
% 1.76/1.00  
% 1.76/1.00  ------ QBF
% 1.76/1.00  
% 1.76/1.00  qbf_q_res:                              0
% 1.76/1.00  qbf_num_tautologies:                    0
% 1.76/1.00  qbf_prep_cycles:                        0
% 1.76/1.00  
% 1.76/1.00  ------ BMC1
% 1.76/1.00  
% 1.76/1.00  bmc1_current_bound:                     -1
% 1.76/1.00  bmc1_last_solved_bound:                 -1
% 1.76/1.00  bmc1_unsat_core_size:                   -1
% 1.76/1.00  bmc1_unsat_core_parents_size:           -1
% 1.76/1.00  bmc1_merge_next_fun:                    0
% 1.76/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.76/1.00  
% 1.76/1.00  ------ Instantiation
% 1.76/1.00  
% 1.76/1.00  inst_num_of_clauses:                    210
% 1.76/1.00  inst_num_in_passive:                    37
% 1.76/1.00  inst_num_in_active:                     115
% 1.76/1.00  inst_num_in_unprocessed:                58
% 1.76/1.00  inst_num_of_loops:                      140
% 1.76/1.00  inst_num_of_learning_restarts:          0
% 1.76/1.00  inst_num_moves_active_passive:          23
% 1.76/1.00  inst_lit_activity:                      0
% 1.76/1.00  inst_lit_activity_moves:                0
% 1.76/1.00  inst_num_tautologies:                   0
% 1.76/1.00  inst_num_prop_implied:                  0
% 1.76/1.00  inst_num_existing_simplified:           0
% 1.76/1.00  inst_num_eq_res_simplified:             0
% 1.76/1.00  inst_num_child_elim:                    0
% 1.76/1.00  inst_num_of_dismatching_blockings:      17
% 1.76/1.00  inst_num_of_non_proper_insts:           162
% 1.76/1.00  inst_num_of_duplicates:                 0
% 1.76/1.00  inst_inst_num_from_inst_to_res:         0
% 1.76/1.00  inst_dismatching_checking_time:         0.
% 1.76/1.00  
% 1.76/1.00  ------ Resolution
% 1.76/1.00  
% 1.76/1.00  res_num_of_clauses:                     0
% 1.76/1.00  res_num_in_passive:                     0
% 1.76/1.00  res_num_in_active:                      0
% 1.76/1.00  res_num_of_loops:                       122
% 1.76/1.00  res_forward_subset_subsumed:            22
% 1.76/1.00  res_backward_subset_subsumed:           0
% 1.76/1.00  res_forward_subsumed:                   0
% 1.76/1.00  res_backward_subsumed:                  0
% 1.76/1.00  res_forward_subsumption_resolution:     0
% 1.76/1.00  res_backward_subsumption_resolution:    1
% 1.76/1.00  res_clause_to_clause_subsumption:       153
% 1.76/1.00  res_orphan_elimination:                 0
% 1.76/1.00  res_tautology_del:                      38
% 1.76/1.00  res_num_eq_res_simplified:              1
% 1.76/1.00  res_num_sel_changes:                    0
% 1.76/1.00  res_moves_from_active_to_pass:          0
% 1.76/1.00  
% 1.76/1.00  ------ Superposition
% 1.76/1.00  
% 1.76/1.00  sup_time_total:                         0.
% 1.76/1.00  sup_time_generating:                    0.
% 1.76/1.00  sup_time_sim_full:                      0.
% 1.76/1.00  sup_time_sim_immed:                     0.
% 1.76/1.00  
% 1.76/1.00  sup_num_of_clauses:                     37
% 1.76/1.00  sup_num_in_active:                      25
% 1.76/1.00  sup_num_in_passive:                     12
% 1.76/1.00  sup_num_of_loops:                       26
% 1.76/1.00  sup_fw_superposition:                   10
% 1.76/1.00  sup_bw_superposition:                   6
% 1.76/1.00  sup_immediate_simplified:               1
% 1.76/1.00  sup_given_eliminated:                   0
% 1.76/1.00  comparisons_done:                       0
% 1.76/1.00  comparisons_avoided:                    0
% 1.76/1.00  
% 1.76/1.00  ------ Simplifications
% 1.76/1.00  
% 1.76/1.00  
% 1.76/1.00  sim_fw_subset_subsumed:                 0
% 1.76/1.00  sim_bw_subset_subsumed:                 0
% 1.76/1.00  sim_fw_subsumed:                        0
% 1.76/1.00  sim_bw_subsumed:                        0
% 1.76/1.00  sim_fw_subsumption_res:                 0
% 1.76/1.00  sim_bw_subsumption_res:                 0
% 1.76/1.00  sim_tautology_del:                      0
% 1.76/1.00  sim_eq_tautology_del:                   0
% 1.76/1.00  sim_eq_res_simp:                        1
% 1.76/1.00  sim_fw_demodulated:                     0
% 1.76/1.00  sim_bw_demodulated:                     1
% 1.76/1.00  sim_light_normalised:                   1
% 1.76/1.00  sim_joinable_taut:                      0
% 1.76/1.00  sim_joinable_simp:                      0
% 1.76/1.00  sim_ac_normalised:                      0
% 1.76/1.00  sim_smt_subsumption:                    0
% 1.76/1.00  
%------------------------------------------------------------------------------
