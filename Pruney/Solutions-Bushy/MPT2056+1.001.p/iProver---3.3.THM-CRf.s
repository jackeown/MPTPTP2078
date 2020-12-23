%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2056+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:05 EST 2020

% Result     : Theorem 1.30s
% Output     : CNFRefutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 336 expanded)
%              Number of clauses        :   53 (  96 expanded)
%              Number of leaves         :   13 (  89 expanded)
%              Depth                    :   20
%              Number of atoms          :  359 (2287 expanded)
%              Number of equality atoms :   96 ( 386 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
     => ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) != sK1
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
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
          ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f32,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
     => k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_434,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_700,plain,
    ( u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) = u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_340,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) != k1_zfmisc_1(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_7])).

cnf(c_341,plain,
    ( k7_subset_1(X0,sK1,X1) = k4_xboole_0(sK1,X1)
    | k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_422,plain,
    ( k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) != k1_zfmisc_1(X0_50)
    | k7_subset_1(X0_50,sK1,X0_49) = k4_xboole_0(sK1,X0_49) ),
    inference(subtyping,[status(esa)],[c_341])).

cnf(c_641,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,X0_49) = k4_xboole_0(sK1,X0_49) ),
    inference(equality_resolution,[status(thm)],[c_422])).

cnf(c_8,negated_conjecture,
    ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X0,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_12,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_228,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))),X0,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_12])).

cnf(c_229,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),X0,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) ),
    inference(unflattening,[status(thm)],[c_228])).

cnf(c_13,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),X0,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_229,c_13])).

cnf(c_234,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),X0,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) ),
    inference(renaming,[status(thm)],[c_233])).

cnf(c_290,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),X0,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_234])).

cnf(c_291,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_11,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,negated_conjecture,
    ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_293,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_291,c_11,c_9,c_7])).

cnf(c_423,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))),sK1,k1_tarski(o_0_0_xboole_0)) = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subtyping,[status(esa)],[c_293])).

cnf(c_656,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_641,c_423])).

cnf(c_6,negated_conjecture,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != sK1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_426,negated_conjecture,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != sK1 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_684,plain,
    ( k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)) != sK1 ),
    inference(demodulation,[status(thm)],[c_656,c_426])).

cnf(c_435,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_672,plain,
    ( k3_yellow_1(k2_struct_0(sK0)) = k3_yellow_1(k2_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_4,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,negated_conjecture,
    ( v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_147,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v2_waybel_0(X1,k3_yellow_1(X2))
    | ~ v13_waybel_0(X1,k3_yellow_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_148,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(X1))
    | ~ v13_waybel_0(sK1,k3_yellow_1(X1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK1)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X1)) ),
    inference(unflattening,[status(thm)],[c_147])).

cnf(c_150,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(X1))
    | ~ v2_waybel_0(sK1,k3_yellow_1(X1))
    | ~ r2_hidden(X0,sK1)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_148,c_11])).

cnf(c_151,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(X1))
    | ~ v13_waybel_0(sK1,k3_yellow_1(X1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X1)) ),
    inference(renaming,[status(thm)],[c_150])).

cnf(c_184,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(X0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 != X2
    | k4_xboole_0(X3,k1_tarski(X2)) = X3
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0))
    | sK1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_151])).

cnf(c_185,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(X0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k4_xboole_0(sK1,k1_tarski(X1)) = sK1
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_184])).

cnf(c_263,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(X0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k4_xboole_0(sK1,k1_tarski(X1)) = sK1
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_185])).

cnf(c_308,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k4_xboole_0(sK1,k1_tarski(X1)) = sK1
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0)
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_263])).

cnf(c_349,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k4_xboole_0(sK1,k1_tarski(X0)) = sK1
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
    | k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) != k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_308])).

cnf(c_387,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k4_xboole_0(sK1,k1_tarski(X0)) = sK1
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X1))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1)
    | k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) != k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))) ),
    inference(equality_resolution_simp,[status(thm)],[c_349])).

cnf(c_421,plain,
    ( ~ v1_xboole_0(X0_48)
    | v1_xboole_0(X1_48)
    | k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) != k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1_48)))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X1_48)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X1_48))
    | k4_xboole_0(sK1,k1_tarski(X0_48)) = sK1 ),
    inference(subtyping,[status(esa)],[c_387])).

cnf(c_428,plain,
    ( v1_xboole_0(X0_48)
    | k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) != k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0_48)))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(X0_48)
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(X0_48))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_421])).

cnf(c_671,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ sP0_iProver_split
    | k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) != k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | k3_yellow_1(k2_struct_0(sK0)) != k3_yellow_1(k2_struct_0(sK0))
    | u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) != u1_struct_0(k3_yellow_1(k2_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_428])).

cnf(c_436,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_628,plain,
    ( k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) = k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_429,plain,
    ( ~ v1_xboole_0(X0_48)
    | k4_xboole_0(sK1,k1_tarski(X0_48)) = sK1
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_421])).

cnf(c_622,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ sP1_iProver_split
    | k4_xboole_0(sK1,k1_tarski(o_0_0_xboole_0)) = sK1 ),
    inference(instantiation,[status(thm)],[c_429])).

cnf(c_430,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_421])).

cnf(c_0,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_32,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_700,c_684,c_672,c_671,c_628,c_622,c_430,c_0,c_32,c_12,c_13])).


%------------------------------------------------------------------------------
