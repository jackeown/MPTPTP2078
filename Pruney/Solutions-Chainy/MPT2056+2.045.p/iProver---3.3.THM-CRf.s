%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:12 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 464 expanded)
%              Number of clauses        :   76 ( 115 expanded)
%              Number of leaves         :   17 ( 128 expanded)
%              Depth                    :   28
%              Number of atoms          :  458 (2472 expanded)
%              Number of equality atoms :  143 ( 476 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f34,plain,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != sK2
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))
    & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))
    & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    & ~ v1_xboole_0(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f33,f32])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
    inference(definition_unfolding,[],[f57,f48])).

fof(f55,plain,(
    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f55,f48])).

fof(f56,plain,(
    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f56,f48])).

fof(f13,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f50,f48,f48,f48,f48])).

fof(f54,plain,(
    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
    inference(definition_unfolding,[],[f54,f48])).

fof(f53,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f46,f41])).

fof(f12,axiom,(
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

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f49,f48,f48,f48,f48])).

fof(f58,plain,(
    k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f42,f41])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1396,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1394,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9,plain,
    ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1390,plain,
    ( X0 = X1
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1391,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(k1_tarski(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1853,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1390,c_1391])).

cnf(c_2114,plain,
    ( sK0(X0,k1_tarski(X1)) = X1
    | r1_xboole_0(X0,k1_tarski(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1394,c_1853])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1397,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2706,plain,
    ( sK0(X0,k1_tarski(X1)) = X1
    | k3_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2114,c_1397])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1393,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_17,negated_conjecture,
    ( v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_16,negated_conjecture,
    ( v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_13,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_18,negated_conjecture,
    ( v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_281,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_282,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK2)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_19,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_284,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_282,c_19])).

cnf(c_285,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK2)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_284])).

cnf(c_364,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK2)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_285])).

cnf(c_409,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK2)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_364])).

cnf(c_450,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_409])).

cnf(c_689,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
    inference(equality_resolution_simp,[status(thm)],[c_450])).

cnf(c_976,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ v1_xboole_0(X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_689])).

cnf(c_1386,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_976])).

cnf(c_1865,plain,
    ( r1_xboole_0(sK2,X0) = iProver_top
    | v1_xboole_0(sK0(sK2,X0)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_1386])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_33,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_977,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_689])).

cnf(c_1011,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_977])).

cnf(c_975,plain,
    ( v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_689])).

cnf(c_1387,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_975])).

cnf(c_1666,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1387])).

cnf(c_1700,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1666])).

cnf(c_2044,plain,
    ( v1_xboole_0(sK0(sK2,X0)) != iProver_top
    | r1_xboole_0(sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1865,c_22,c_23,c_35,c_1011,c_1700])).

cnf(c_2045,plain,
    ( r1_xboole_0(sK2,X0) = iProver_top
    | v1_xboole_0(sK0(sK2,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2044])).

cnf(c_2826,plain,
    ( k3_xboole_0(sK2,k1_tarski(X0)) = k1_xboole_0
    | r1_xboole_0(sK2,k1_tarski(X0)) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2706,c_2045])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1398,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2876,plain,
    ( r1_xboole_0(sK2,k1_tarski(X0)) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2826,c_1398])).

cnf(c_2881,plain,
    ( k3_xboole_0(sK2,k1_tarski(X0)) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2876,c_1397])).

cnf(c_2968,plain,
    ( k3_xboole_0(sK2,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1396,c_2881])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_441,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != k1_zfmisc_1(X2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_442,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) = k7_subset_1(X1,sK2,X0)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_1530,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))),sK2,X0) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
    inference(equality_resolution,[status(thm)],[c_442])).

cnf(c_12,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_329,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_330,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | v2_struct_0(sK1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_21])).

cnf(c_335,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) ),
    inference(renaming,[status(thm)],[c_334])).

cnf(c_391,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_335])).

cnf(c_392,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | v1_xboole_0(sK2)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))),sK2,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_394,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))),sK2,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_19,c_17,c_15])).

cnf(c_1554,plain,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_1530,c_394])).

cnf(c_14,negated_conjecture,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != sK2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1590,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0))) != sK2 ),
    inference(demodulation,[status(thm)],[c_1554,c_14])).

cnf(c_3061,plain,
    ( k5_xboole_0(sK2,k1_xboole_0) != sK2 ),
    inference(demodulation,[status(thm)],[c_2968,c_1590])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1392,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1746,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1392,c_1397])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1755,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1746,c_6])).

cnf(c_3067,plain,
    ( sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_3061,c_1755])).

cnf(c_3068,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3067])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.91/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/0.99  
% 1.91/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.91/0.99  
% 1.91/0.99  ------  iProver source info
% 1.91/0.99  
% 1.91/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.91/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.91/0.99  git: non_committed_changes: false
% 1.91/0.99  git: last_make_outside_of_git: false
% 1.91/0.99  
% 1.91/0.99  ------ 
% 1.91/0.99  
% 1.91/0.99  ------ Input Options
% 1.91/0.99  
% 1.91/0.99  --out_options                           all
% 1.91/0.99  --tptp_safe_out                         true
% 1.91/0.99  --problem_path                          ""
% 1.91/0.99  --include_path                          ""
% 1.91/0.99  --clausifier                            res/vclausify_rel
% 1.91/0.99  --clausifier_options                    --mode clausify
% 1.91/0.99  --stdin                                 false
% 1.91/0.99  --stats_out                             all
% 1.91/0.99  
% 1.91/0.99  ------ General Options
% 1.91/0.99  
% 1.91/0.99  --fof                                   false
% 1.91/0.99  --time_out_real                         305.
% 1.91/0.99  --time_out_virtual                      -1.
% 1.91/0.99  --symbol_type_check                     false
% 1.91/0.99  --clausify_out                          false
% 1.91/0.99  --sig_cnt_out                           false
% 1.91/1.00  --trig_cnt_out                          false
% 1.91/1.00  --trig_cnt_out_tolerance                1.
% 1.91/1.00  --trig_cnt_out_sk_spl                   false
% 1.91/1.00  --abstr_cl_out                          false
% 1.91/1.00  
% 1.91/1.00  ------ Global Options
% 1.91/1.00  
% 1.91/1.00  --schedule                              default
% 1.91/1.00  --add_important_lit                     false
% 1.91/1.00  --prop_solver_per_cl                    1000
% 1.91/1.00  --min_unsat_core                        false
% 1.91/1.00  --soft_assumptions                      false
% 1.91/1.00  --soft_lemma_size                       3
% 1.91/1.00  --prop_impl_unit_size                   0
% 1.91/1.00  --prop_impl_unit                        []
% 1.91/1.00  --share_sel_clauses                     true
% 1.91/1.00  --reset_solvers                         false
% 1.91/1.00  --bc_imp_inh                            [conj_cone]
% 1.91/1.00  --conj_cone_tolerance                   3.
% 1.91/1.00  --extra_neg_conj                        none
% 1.91/1.00  --large_theory_mode                     true
% 1.91/1.00  --prolific_symb_bound                   200
% 1.91/1.00  --lt_threshold                          2000
% 1.91/1.00  --clause_weak_htbl                      true
% 1.91/1.00  --gc_record_bc_elim                     false
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing Options
% 1.91/1.00  
% 1.91/1.00  --preprocessing_flag                    true
% 1.91/1.00  --time_out_prep_mult                    0.1
% 1.91/1.00  --splitting_mode                        input
% 1.91/1.00  --splitting_grd                         true
% 1.91/1.00  --splitting_cvd                         false
% 1.91/1.00  --splitting_cvd_svl                     false
% 1.91/1.00  --splitting_nvd                         32
% 1.91/1.00  --sub_typing                            true
% 1.91/1.00  --prep_gs_sim                           true
% 1.91/1.00  --prep_unflatten                        true
% 1.91/1.00  --prep_res_sim                          true
% 1.91/1.00  --prep_upred                            true
% 1.91/1.00  --prep_sem_filter                       exhaustive
% 1.91/1.00  --prep_sem_filter_out                   false
% 1.91/1.00  --pred_elim                             true
% 1.91/1.00  --res_sim_input                         true
% 1.91/1.00  --eq_ax_congr_red                       true
% 1.91/1.00  --pure_diseq_elim                       true
% 1.91/1.00  --brand_transform                       false
% 1.91/1.00  --non_eq_to_eq                          false
% 1.91/1.00  --prep_def_merge                        true
% 1.91/1.00  --prep_def_merge_prop_impl              false
% 1.91/1.00  --prep_def_merge_mbd                    true
% 1.91/1.00  --prep_def_merge_tr_red                 false
% 1.91/1.00  --prep_def_merge_tr_cl                  false
% 1.91/1.00  --smt_preprocessing                     true
% 1.91/1.00  --smt_ac_axioms                         fast
% 1.91/1.00  --preprocessed_out                      false
% 1.91/1.00  --preprocessed_stats                    false
% 1.91/1.00  
% 1.91/1.00  ------ Abstraction refinement Options
% 1.91/1.00  
% 1.91/1.00  --abstr_ref                             []
% 1.91/1.00  --abstr_ref_prep                        false
% 1.91/1.00  --abstr_ref_until_sat                   false
% 1.91/1.00  --abstr_ref_sig_restrict                funpre
% 1.91/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.91/1.00  --abstr_ref_under                       []
% 1.91/1.00  
% 1.91/1.00  ------ SAT Options
% 1.91/1.00  
% 1.91/1.00  --sat_mode                              false
% 1.91/1.00  --sat_fm_restart_options                ""
% 1.91/1.00  --sat_gr_def                            false
% 1.91/1.00  --sat_epr_types                         true
% 1.91/1.00  --sat_non_cyclic_types                  false
% 1.91/1.00  --sat_finite_models                     false
% 1.91/1.00  --sat_fm_lemmas                         false
% 1.91/1.00  --sat_fm_prep                           false
% 1.91/1.00  --sat_fm_uc_incr                        true
% 1.91/1.00  --sat_out_model                         small
% 1.91/1.00  --sat_out_clauses                       false
% 1.91/1.00  
% 1.91/1.00  ------ QBF Options
% 1.91/1.00  
% 1.91/1.00  --qbf_mode                              false
% 1.91/1.00  --qbf_elim_univ                         false
% 1.91/1.00  --qbf_dom_inst                          none
% 1.91/1.00  --qbf_dom_pre_inst                      false
% 1.91/1.00  --qbf_sk_in                             false
% 1.91/1.00  --qbf_pred_elim                         true
% 1.91/1.00  --qbf_split                             512
% 1.91/1.00  
% 1.91/1.00  ------ BMC1 Options
% 1.91/1.00  
% 1.91/1.00  --bmc1_incremental                      false
% 1.91/1.00  --bmc1_axioms                           reachable_all
% 1.91/1.00  --bmc1_min_bound                        0
% 1.91/1.00  --bmc1_max_bound                        -1
% 1.91/1.00  --bmc1_max_bound_default                -1
% 1.91/1.00  --bmc1_symbol_reachability              true
% 1.91/1.00  --bmc1_property_lemmas                  false
% 1.91/1.00  --bmc1_k_induction                      false
% 1.91/1.00  --bmc1_non_equiv_states                 false
% 1.91/1.00  --bmc1_deadlock                         false
% 1.91/1.00  --bmc1_ucm                              false
% 1.91/1.00  --bmc1_add_unsat_core                   none
% 1.91/1.00  --bmc1_unsat_core_children              false
% 1.91/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.91/1.00  --bmc1_out_stat                         full
% 1.91/1.00  --bmc1_ground_init                      false
% 1.91/1.00  --bmc1_pre_inst_next_state              false
% 1.91/1.00  --bmc1_pre_inst_state                   false
% 1.91/1.00  --bmc1_pre_inst_reach_state             false
% 1.91/1.00  --bmc1_out_unsat_core                   false
% 1.91/1.00  --bmc1_aig_witness_out                  false
% 1.91/1.00  --bmc1_verbose                          false
% 1.91/1.00  --bmc1_dump_clauses_tptp                false
% 1.91/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.91/1.00  --bmc1_dump_file                        -
% 1.91/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.91/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.91/1.00  --bmc1_ucm_extend_mode                  1
% 1.91/1.00  --bmc1_ucm_init_mode                    2
% 1.91/1.00  --bmc1_ucm_cone_mode                    none
% 1.91/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.91/1.00  --bmc1_ucm_relax_model                  4
% 1.91/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.91/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.91/1.00  --bmc1_ucm_layered_model                none
% 1.91/1.00  --bmc1_ucm_max_lemma_size               10
% 1.91/1.00  
% 1.91/1.00  ------ AIG Options
% 1.91/1.00  
% 1.91/1.00  --aig_mode                              false
% 1.91/1.00  
% 1.91/1.00  ------ Instantiation Options
% 1.91/1.00  
% 1.91/1.00  --instantiation_flag                    true
% 1.91/1.00  --inst_sos_flag                         false
% 1.91/1.00  --inst_sos_phase                        true
% 1.91/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.91/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.91/1.00  --inst_lit_sel_side                     num_symb
% 1.91/1.00  --inst_solver_per_active                1400
% 1.91/1.00  --inst_solver_calls_frac                1.
% 1.91/1.00  --inst_passive_queue_type               priority_queues
% 1.91/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.91/1.00  --inst_passive_queues_freq              [25;2]
% 1.91/1.00  --inst_dismatching                      true
% 1.91/1.00  --inst_eager_unprocessed_to_passive     true
% 1.91/1.00  --inst_prop_sim_given                   true
% 1.91/1.00  --inst_prop_sim_new                     false
% 1.91/1.00  --inst_subs_new                         false
% 1.91/1.00  --inst_eq_res_simp                      false
% 1.91/1.00  --inst_subs_given                       false
% 1.91/1.00  --inst_orphan_elimination               true
% 1.91/1.00  --inst_learning_loop_flag               true
% 1.91/1.00  --inst_learning_start                   3000
% 1.91/1.00  --inst_learning_factor                  2
% 1.91/1.00  --inst_start_prop_sim_after_learn       3
% 1.91/1.00  --inst_sel_renew                        solver
% 1.91/1.00  --inst_lit_activity_flag                true
% 1.91/1.00  --inst_restr_to_given                   false
% 1.91/1.00  --inst_activity_threshold               500
% 1.91/1.00  --inst_out_proof                        true
% 1.91/1.00  
% 1.91/1.00  ------ Resolution Options
% 1.91/1.00  
% 1.91/1.00  --resolution_flag                       true
% 1.91/1.00  --res_lit_sel                           adaptive
% 1.91/1.00  --res_lit_sel_side                      none
% 1.91/1.00  --res_ordering                          kbo
% 1.91/1.00  --res_to_prop_solver                    active
% 1.91/1.00  --res_prop_simpl_new                    false
% 1.91/1.00  --res_prop_simpl_given                  true
% 1.91/1.00  --res_passive_queue_type                priority_queues
% 1.91/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.91/1.00  --res_passive_queues_freq               [15;5]
% 1.91/1.00  --res_forward_subs                      full
% 1.91/1.00  --res_backward_subs                     full
% 1.91/1.00  --res_forward_subs_resolution           true
% 1.91/1.00  --res_backward_subs_resolution          true
% 1.91/1.00  --res_orphan_elimination                true
% 1.91/1.00  --res_time_limit                        2.
% 1.91/1.00  --res_out_proof                         true
% 1.91/1.00  
% 1.91/1.00  ------ Superposition Options
% 1.91/1.00  
% 1.91/1.00  --superposition_flag                    true
% 1.91/1.00  --sup_passive_queue_type                priority_queues
% 1.91/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.91/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.91/1.00  --demod_completeness_check              fast
% 1.91/1.00  --demod_use_ground                      true
% 1.91/1.00  --sup_to_prop_solver                    passive
% 1.91/1.00  --sup_prop_simpl_new                    true
% 1.91/1.00  --sup_prop_simpl_given                  true
% 1.91/1.00  --sup_fun_splitting                     false
% 1.91/1.00  --sup_smt_interval                      50000
% 1.91/1.00  
% 1.91/1.00  ------ Superposition Simplification Setup
% 1.91/1.00  
% 1.91/1.00  --sup_indices_passive                   []
% 1.91/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.91/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.00  --sup_full_bw                           [BwDemod]
% 1.91/1.00  --sup_immed_triv                        [TrivRules]
% 1.91/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.91/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.00  --sup_immed_bw_main                     []
% 1.91/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.00  
% 1.91/1.00  ------ Combination Options
% 1.91/1.00  
% 1.91/1.00  --comb_res_mult                         3
% 1.91/1.00  --comb_sup_mult                         2
% 1.91/1.00  --comb_inst_mult                        10
% 1.91/1.00  
% 1.91/1.00  ------ Debug Options
% 1.91/1.00  
% 1.91/1.00  --dbg_backtrace                         false
% 1.91/1.00  --dbg_dump_prop_clauses                 false
% 1.91/1.00  --dbg_dump_prop_clauses_file            -
% 1.91/1.00  --dbg_out_stat                          false
% 1.91/1.00  ------ Parsing...
% 1.91/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.91/1.00  ------ Proving...
% 1.91/1.00  ------ Problem Properties 
% 1.91/1.00  
% 1.91/1.00  
% 1.91/1.00  clauses                                 18
% 1.91/1.00  conjectures                             2
% 1.91/1.00  EPR                                     6
% 1.91/1.00  Horn                                    14
% 1.91/1.00  unary                                   7
% 1.91/1.00  binary                                  8
% 1.91/1.00  lits                                    34
% 1.91/1.00  lits eq                                 11
% 1.91/1.00  fd_pure                                 0
% 1.91/1.00  fd_pseudo                               0
% 1.91/1.00  fd_cond                                 0
% 1.91/1.00  fd_pseudo_cond                          1
% 1.91/1.00  AC symbols                              0
% 1.91/1.00  
% 1.91/1.00  ------ Schedule dynamic 5 is on 
% 1.91/1.00  
% 1.91/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.91/1.00  
% 1.91/1.00  
% 1.91/1.00  ------ 
% 1.91/1.00  Current options:
% 1.91/1.00  ------ 
% 1.91/1.00  
% 1.91/1.00  ------ Input Options
% 1.91/1.00  
% 1.91/1.00  --out_options                           all
% 1.91/1.00  --tptp_safe_out                         true
% 1.91/1.00  --problem_path                          ""
% 1.91/1.00  --include_path                          ""
% 1.91/1.00  --clausifier                            res/vclausify_rel
% 1.91/1.00  --clausifier_options                    --mode clausify
% 1.91/1.00  --stdin                                 false
% 1.91/1.00  --stats_out                             all
% 1.91/1.00  
% 1.91/1.00  ------ General Options
% 1.91/1.00  
% 1.91/1.00  --fof                                   false
% 1.91/1.00  --time_out_real                         305.
% 1.91/1.00  --time_out_virtual                      -1.
% 1.91/1.00  --symbol_type_check                     false
% 1.91/1.00  --clausify_out                          false
% 1.91/1.00  --sig_cnt_out                           false
% 1.91/1.00  --trig_cnt_out                          false
% 1.91/1.00  --trig_cnt_out_tolerance                1.
% 1.91/1.00  --trig_cnt_out_sk_spl                   false
% 1.91/1.00  --abstr_cl_out                          false
% 1.91/1.00  
% 1.91/1.00  ------ Global Options
% 1.91/1.00  
% 1.91/1.00  --schedule                              default
% 1.91/1.00  --add_important_lit                     false
% 1.91/1.00  --prop_solver_per_cl                    1000
% 1.91/1.00  --min_unsat_core                        false
% 1.91/1.00  --soft_assumptions                      false
% 1.91/1.00  --soft_lemma_size                       3
% 1.91/1.00  --prop_impl_unit_size                   0
% 1.91/1.00  --prop_impl_unit                        []
% 1.91/1.00  --share_sel_clauses                     true
% 1.91/1.00  --reset_solvers                         false
% 1.91/1.00  --bc_imp_inh                            [conj_cone]
% 1.91/1.00  --conj_cone_tolerance                   3.
% 1.91/1.00  --extra_neg_conj                        none
% 1.91/1.00  --large_theory_mode                     true
% 1.91/1.00  --prolific_symb_bound                   200
% 1.91/1.00  --lt_threshold                          2000
% 1.91/1.00  --clause_weak_htbl                      true
% 1.91/1.00  --gc_record_bc_elim                     false
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing Options
% 1.91/1.00  
% 1.91/1.00  --preprocessing_flag                    true
% 1.91/1.00  --time_out_prep_mult                    0.1
% 1.91/1.00  --splitting_mode                        input
% 1.91/1.00  --splitting_grd                         true
% 1.91/1.00  --splitting_cvd                         false
% 1.91/1.00  --splitting_cvd_svl                     false
% 1.91/1.00  --splitting_nvd                         32
% 1.91/1.00  --sub_typing                            true
% 1.91/1.00  --prep_gs_sim                           true
% 1.91/1.00  --prep_unflatten                        true
% 1.91/1.00  --prep_res_sim                          true
% 1.91/1.00  --prep_upred                            true
% 1.91/1.00  --prep_sem_filter                       exhaustive
% 1.91/1.00  --prep_sem_filter_out                   false
% 1.91/1.00  --pred_elim                             true
% 1.91/1.00  --res_sim_input                         true
% 1.91/1.00  --eq_ax_congr_red                       true
% 1.91/1.00  --pure_diseq_elim                       true
% 1.91/1.00  --brand_transform                       false
% 1.91/1.00  --non_eq_to_eq                          false
% 1.91/1.00  --prep_def_merge                        true
% 1.91/1.00  --prep_def_merge_prop_impl              false
% 1.91/1.00  --prep_def_merge_mbd                    true
% 1.91/1.00  --prep_def_merge_tr_red                 false
% 1.91/1.00  --prep_def_merge_tr_cl                  false
% 1.91/1.00  --smt_preprocessing                     true
% 1.91/1.00  --smt_ac_axioms                         fast
% 1.91/1.00  --preprocessed_out                      false
% 1.91/1.00  --preprocessed_stats                    false
% 1.91/1.00  
% 1.91/1.00  ------ Abstraction refinement Options
% 1.91/1.00  
% 1.91/1.00  --abstr_ref                             []
% 1.91/1.00  --abstr_ref_prep                        false
% 1.91/1.00  --abstr_ref_until_sat                   false
% 1.91/1.00  --abstr_ref_sig_restrict                funpre
% 1.91/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.91/1.00  --abstr_ref_under                       []
% 1.91/1.00  
% 1.91/1.00  ------ SAT Options
% 1.91/1.00  
% 1.91/1.00  --sat_mode                              false
% 1.91/1.00  --sat_fm_restart_options                ""
% 1.91/1.00  --sat_gr_def                            false
% 1.91/1.00  --sat_epr_types                         true
% 1.91/1.00  --sat_non_cyclic_types                  false
% 1.91/1.00  --sat_finite_models                     false
% 1.91/1.00  --sat_fm_lemmas                         false
% 1.91/1.00  --sat_fm_prep                           false
% 1.91/1.00  --sat_fm_uc_incr                        true
% 1.91/1.00  --sat_out_model                         small
% 1.91/1.00  --sat_out_clauses                       false
% 1.91/1.00  
% 1.91/1.00  ------ QBF Options
% 1.91/1.00  
% 1.91/1.00  --qbf_mode                              false
% 1.91/1.00  --qbf_elim_univ                         false
% 1.91/1.00  --qbf_dom_inst                          none
% 1.91/1.00  --qbf_dom_pre_inst                      false
% 1.91/1.00  --qbf_sk_in                             false
% 1.91/1.00  --qbf_pred_elim                         true
% 1.91/1.00  --qbf_split                             512
% 1.91/1.00  
% 1.91/1.00  ------ BMC1 Options
% 1.91/1.00  
% 1.91/1.00  --bmc1_incremental                      false
% 1.91/1.00  --bmc1_axioms                           reachable_all
% 1.91/1.00  --bmc1_min_bound                        0
% 1.91/1.00  --bmc1_max_bound                        -1
% 1.91/1.00  --bmc1_max_bound_default                -1
% 1.91/1.00  --bmc1_symbol_reachability              true
% 1.91/1.00  --bmc1_property_lemmas                  false
% 1.91/1.00  --bmc1_k_induction                      false
% 1.91/1.00  --bmc1_non_equiv_states                 false
% 1.91/1.00  --bmc1_deadlock                         false
% 1.91/1.00  --bmc1_ucm                              false
% 1.91/1.00  --bmc1_add_unsat_core                   none
% 1.91/1.00  --bmc1_unsat_core_children              false
% 1.91/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.91/1.00  --bmc1_out_stat                         full
% 1.91/1.00  --bmc1_ground_init                      false
% 1.91/1.00  --bmc1_pre_inst_next_state              false
% 1.91/1.00  --bmc1_pre_inst_state                   false
% 1.91/1.00  --bmc1_pre_inst_reach_state             false
% 1.91/1.00  --bmc1_out_unsat_core                   false
% 1.91/1.00  --bmc1_aig_witness_out                  false
% 1.91/1.00  --bmc1_verbose                          false
% 1.91/1.00  --bmc1_dump_clauses_tptp                false
% 1.91/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.91/1.00  --bmc1_dump_file                        -
% 1.91/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.91/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.91/1.00  --bmc1_ucm_extend_mode                  1
% 1.91/1.00  --bmc1_ucm_init_mode                    2
% 1.91/1.00  --bmc1_ucm_cone_mode                    none
% 1.91/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.91/1.00  --bmc1_ucm_relax_model                  4
% 1.91/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.91/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.91/1.00  --bmc1_ucm_layered_model                none
% 1.91/1.00  --bmc1_ucm_max_lemma_size               10
% 1.91/1.00  
% 1.91/1.00  ------ AIG Options
% 1.91/1.00  
% 1.91/1.00  --aig_mode                              false
% 1.91/1.00  
% 1.91/1.00  ------ Instantiation Options
% 1.91/1.00  
% 1.91/1.00  --instantiation_flag                    true
% 1.91/1.00  --inst_sos_flag                         false
% 1.91/1.00  --inst_sos_phase                        true
% 1.91/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.91/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.91/1.00  --inst_lit_sel_side                     none
% 1.91/1.00  --inst_solver_per_active                1400
% 1.91/1.00  --inst_solver_calls_frac                1.
% 1.91/1.00  --inst_passive_queue_type               priority_queues
% 1.91/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.91/1.00  --inst_passive_queues_freq              [25;2]
% 1.91/1.00  --inst_dismatching                      true
% 1.91/1.00  --inst_eager_unprocessed_to_passive     true
% 1.91/1.00  --inst_prop_sim_given                   true
% 1.91/1.00  --inst_prop_sim_new                     false
% 1.91/1.00  --inst_subs_new                         false
% 1.91/1.00  --inst_eq_res_simp                      false
% 1.91/1.00  --inst_subs_given                       false
% 1.91/1.00  --inst_orphan_elimination               true
% 1.91/1.00  --inst_learning_loop_flag               true
% 1.91/1.00  --inst_learning_start                   3000
% 1.91/1.00  --inst_learning_factor                  2
% 1.91/1.00  --inst_start_prop_sim_after_learn       3
% 1.91/1.00  --inst_sel_renew                        solver
% 1.91/1.00  --inst_lit_activity_flag                true
% 1.91/1.00  --inst_restr_to_given                   false
% 1.91/1.00  --inst_activity_threshold               500
% 1.91/1.00  --inst_out_proof                        true
% 1.91/1.00  
% 1.91/1.00  ------ Resolution Options
% 1.91/1.00  
% 1.91/1.00  --resolution_flag                       false
% 1.91/1.00  --res_lit_sel                           adaptive
% 1.91/1.00  --res_lit_sel_side                      none
% 1.91/1.00  --res_ordering                          kbo
% 1.91/1.00  --res_to_prop_solver                    active
% 1.91/1.00  --res_prop_simpl_new                    false
% 1.91/1.00  --res_prop_simpl_given                  true
% 1.91/1.00  --res_passive_queue_type                priority_queues
% 1.91/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.91/1.00  --res_passive_queues_freq               [15;5]
% 1.91/1.00  --res_forward_subs                      full
% 1.91/1.00  --res_backward_subs                     full
% 1.91/1.00  --res_forward_subs_resolution           true
% 1.91/1.00  --res_backward_subs_resolution          true
% 1.91/1.00  --res_orphan_elimination                true
% 1.91/1.00  --res_time_limit                        2.
% 1.91/1.00  --res_out_proof                         true
% 1.91/1.00  
% 1.91/1.00  ------ Superposition Options
% 1.91/1.00  
% 1.91/1.00  --superposition_flag                    true
% 1.91/1.00  --sup_passive_queue_type                priority_queues
% 1.91/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.91/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.91/1.00  --demod_completeness_check              fast
% 1.91/1.00  --demod_use_ground                      true
% 1.91/1.00  --sup_to_prop_solver                    passive
% 1.91/1.00  --sup_prop_simpl_new                    true
% 1.91/1.00  --sup_prop_simpl_given                  true
% 1.91/1.00  --sup_fun_splitting                     false
% 1.91/1.00  --sup_smt_interval                      50000
% 1.91/1.00  
% 1.91/1.00  ------ Superposition Simplification Setup
% 1.91/1.00  
% 1.91/1.00  --sup_indices_passive                   []
% 1.91/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.91/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.00  --sup_full_bw                           [BwDemod]
% 1.91/1.00  --sup_immed_triv                        [TrivRules]
% 1.91/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.91/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.00  --sup_immed_bw_main                     []
% 1.91/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.00  
% 1.91/1.00  ------ Combination Options
% 1.91/1.00  
% 1.91/1.00  --comb_res_mult                         3
% 1.91/1.00  --comb_sup_mult                         2
% 1.91/1.00  --comb_inst_mult                        10
% 1.91/1.00  
% 1.91/1.00  ------ Debug Options
% 1.91/1.00  
% 1.91/1.00  --dbg_backtrace                         false
% 1.91/1.00  --dbg_dump_prop_clauses                 false
% 1.91/1.00  --dbg_dump_prop_clauses_file            -
% 1.91/1.00  --dbg_out_stat                          false
% 1.91/1.00  
% 1.91/1.00  
% 1.91/1.00  
% 1.91/1.00  
% 1.91/1.00  ------ Proving...
% 1.91/1.00  
% 1.91/1.00  
% 1.91/1.00  % SZS status Theorem for theBenchmark.p
% 1.91/1.00  
% 1.91/1.00   Resolution empty clause
% 1.91/1.00  
% 1.91/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.91/1.00  
% 1.91/1.00  fof(f2,axiom,(
% 1.91/1.00    v1_xboole_0(k1_xboole_0)),
% 1.91/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.00  
% 1.91/1.00  fof(f37,plain,(
% 1.91/1.00    v1_xboole_0(k1_xboole_0)),
% 1.91/1.00    inference(cnf_transformation,[],[f2])).
% 1.91/1.00  
% 1.91/1.00  fof(f3,axiom,(
% 1.91/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.91/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.00  
% 1.91/1.00  fof(f16,plain,(
% 1.91/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.91/1.00    inference(rectify,[],[f3])).
% 1.91/1.00  
% 1.91/1.00  fof(f17,plain,(
% 1.91/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.91/1.00    inference(ennf_transformation,[],[f16])).
% 1.91/1.00  
% 1.91/1.00  fof(f30,plain,(
% 1.91/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.91/1.00    introduced(choice_axiom,[])).
% 1.91/1.00  
% 1.91/1.00  fof(f31,plain,(
% 1.91/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f30])).
% 1.91/1.00  
% 1.91/1.00  fof(f39,plain,(
% 1.91/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.91/1.00    inference(cnf_transformation,[],[f31])).
% 1.91/1.00  
% 1.91/1.00  fof(f8,axiom,(
% 1.91/1.00    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.91/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.00  
% 1.91/1.00  fof(f19,plain,(
% 1.91/1.00    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.91/1.00    inference(ennf_transformation,[],[f8])).
% 1.91/1.00  
% 1.91/1.00  fof(f45,plain,(
% 1.91/1.00    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.91/1.00    inference(cnf_transformation,[],[f19])).
% 1.91/1.00  
% 1.91/1.00  fof(f7,axiom,(
% 1.91/1.00    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.91/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.00  
% 1.91/1.00  fof(f18,plain,(
% 1.91/1.00    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.91/1.00    inference(ennf_transformation,[],[f7])).
% 1.91/1.00  
% 1.91/1.00  fof(f44,plain,(
% 1.91/1.00    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.91/1.00    inference(cnf_transformation,[],[f18])).
% 1.91/1.00  
% 1.91/1.00  fof(f1,axiom,(
% 1.91/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.91/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.00  
% 1.91/1.00  fof(f29,plain,(
% 1.91/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.91/1.00    inference(nnf_transformation,[],[f1])).
% 1.91/1.00  
% 1.91/1.00  fof(f35,plain,(
% 1.91/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.91/1.00    inference(cnf_transformation,[],[f29])).
% 1.91/1.00  
% 1.91/1.00  fof(f38,plain,(
% 1.91/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.91/1.00    inference(cnf_transformation,[],[f31])).
% 1.91/1.00  
% 1.91/1.00  fof(f14,conjecture,(
% 1.91/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.91/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.00  
% 1.91/1.00  fof(f15,negated_conjecture,(
% 1.91/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.91/1.00    inference(negated_conjecture,[],[f14])).
% 1.91/1.00  
% 1.91/1.00  fof(f27,plain,(
% 1.91/1.00    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.91/1.00    inference(ennf_transformation,[],[f15])).
% 1.91/1.00  
% 1.91/1.00  fof(f28,plain,(
% 1.91/1.00    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.91/1.00    inference(flattening,[],[f27])).
% 1.91/1.00  
% 1.91/1.00  fof(f33,plain,(
% 1.91/1.00    ( ! [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) != sK2 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK2))) )),
% 1.91/1.00    introduced(choice_axiom,[])).
% 1.91/1.00  
% 1.91/1.00  fof(f32,plain,(
% 1.91/1.00    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 1.91/1.00    introduced(choice_axiom,[])).
% 1.91/1.00  
% 1.91/1.00  fof(f34,plain,(
% 1.91/1.00    (k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != sK2 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)),
% 1.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f33,f32])).
% 1.91/1.00  
% 1.91/1.00  fof(f57,plain,(
% 1.91/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))),
% 1.91/1.00    inference(cnf_transformation,[],[f34])).
% 1.91/1.00  
% 1.91/1.00  fof(f11,axiom,(
% 1.91/1.00    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.91/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.00  
% 1.91/1.00  fof(f48,plain,(
% 1.91/1.00    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.91/1.00    inference(cnf_transformation,[],[f11])).
% 1.91/1.00  
% 1.91/1.00  fof(f63,plain,(
% 1.91/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))),
% 1.91/1.00    inference(definition_unfolding,[],[f57,f48])).
% 1.91/1.00  
% 1.91/1.00  fof(f55,plain,(
% 1.91/1.00    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 1.91/1.00    inference(cnf_transformation,[],[f34])).
% 1.91/1.00  
% 1.91/1.00  fof(f65,plain,(
% 1.91/1.00    v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))),
% 1.91/1.00    inference(definition_unfolding,[],[f55,f48])).
% 1.91/1.00  
% 1.91/1.00  fof(f56,plain,(
% 1.91/1.00    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 1.91/1.00    inference(cnf_transformation,[],[f34])).
% 1.91/1.00  
% 1.91/1.00  fof(f64,plain,(
% 1.91/1.00    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))),
% 1.91/1.00    inference(definition_unfolding,[],[f56,f48])).
% 1.91/1.00  
% 1.91/1.00  fof(f13,axiom,(
% 1.91/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 1.91/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.00  
% 1.91/1.00  fof(f25,plain,(
% 1.91/1.00    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.91/1.00    inference(ennf_transformation,[],[f13])).
% 1.91/1.00  
% 1.91/1.00  fof(f26,plain,(
% 1.91/1.00    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.91/1.00    inference(flattening,[],[f25])).
% 1.91/1.00  
% 1.91/1.00  fof(f50,plain,(
% 1.91/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.91/1.00    inference(cnf_transformation,[],[f26])).
% 1.91/1.00  
% 1.91/1.00  fof(f62,plain,(
% 1.91/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.91/1.00    inference(definition_unfolding,[],[f50,f48,f48,f48,f48])).
% 1.91/1.00  
% 1.91/1.00  fof(f54,plain,(
% 1.91/1.00    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))),
% 1.91/1.00    inference(cnf_transformation,[],[f34])).
% 1.91/1.00  
% 1.91/1.00  fof(f66,plain,(
% 1.91/1.00    v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))),
% 1.91/1.00    inference(definition_unfolding,[],[f54,f48])).
% 1.91/1.00  
% 1.91/1.00  fof(f53,plain,(
% 1.91/1.00    ~v1_xboole_0(sK2)),
% 1.91/1.00    inference(cnf_transformation,[],[f34])).
% 1.91/1.00  
% 1.91/1.00  fof(f51,plain,(
% 1.91/1.00    ~v2_struct_0(sK1)),
% 1.91/1.00    inference(cnf_transformation,[],[f34])).
% 1.91/1.00  
% 1.91/1.00  fof(f52,plain,(
% 1.91/1.00    l1_struct_0(sK1)),
% 1.91/1.00    inference(cnf_transformation,[],[f34])).
% 1.91/1.00  
% 1.91/1.00  fof(f10,axiom,(
% 1.91/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.91/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.00  
% 1.91/1.00  fof(f21,plain,(
% 1.91/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.91/1.00    inference(ennf_transformation,[],[f10])).
% 1.91/1.00  
% 1.91/1.00  fof(f22,plain,(
% 1.91/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.91/1.00    inference(flattening,[],[f21])).
% 1.91/1.00  
% 1.91/1.00  fof(f47,plain,(
% 1.91/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.91/1.00    inference(cnf_transformation,[],[f22])).
% 1.91/1.00  
% 1.91/1.00  fof(f36,plain,(
% 1.91/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.91/1.00    inference(cnf_transformation,[],[f29])).
% 1.91/1.00  
% 1.91/1.00  fof(f9,axiom,(
% 1.91/1.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.91/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.00  
% 1.91/1.00  fof(f20,plain,(
% 1.91/1.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.91/1.00    inference(ennf_transformation,[],[f9])).
% 1.91/1.00  
% 1.91/1.00  fof(f46,plain,(
% 1.91/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.91/1.00    inference(cnf_transformation,[],[f20])).
% 1.91/1.00  
% 1.91/1.00  fof(f4,axiom,(
% 1.91/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.91/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.00  
% 1.91/1.00  fof(f41,plain,(
% 1.91/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.91/1.00    inference(cnf_transformation,[],[f4])).
% 1.91/1.00  
% 1.91/1.00  fof(f60,plain,(
% 1.91/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.91/1.00    inference(definition_unfolding,[],[f46,f41])).
% 1.91/1.00  
% 1.91/1.00  fof(f12,axiom,(
% 1.91/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 1.91/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.00  
% 1.91/1.00  fof(f23,plain,(
% 1.91/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.91/1.00    inference(ennf_transformation,[],[f12])).
% 1.91/1.00  
% 1.91/1.00  fof(f24,plain,(
% 1.91/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.91/1.00    inference(flattening,[],[f23])).
% 1.91/1.00  
% 1.91/1.00  fof(f49,plain,(
% 1.91/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.91/1.00    inference(cnf_transformation,[],[f24])).
% 1.91/1.00  
% 1.91/1.00  fof(f61,plain,(
% 1.91/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.91/1.00    inference(definition_unfolding,[],[f49,f48,f48,f48,f48])).
% 1.91/1.00  
% 1.91/1.00  fof(f58,plain,(
% 1.91/1.00    k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != sK2),
% 1.91/1.00    inference(cnf_transformation,[],[f34])).
% 1.91/1.00  
% 1.91/1.00  fof(f6,axiom,(
% 1.91/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.91/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.00  
% 1.91/1.00  fof(f43,plain,(
% 1.91/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.91/1.00    inference(cnf_transformation,[],[f6])).
% 1.91/1.00  
% 1.91/1.00  fof(f5,axiom,(
% 1.91/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.91/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/1.00  
% 1.91/1.00  fof(f42,plain,(
% 1.91/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.91/1.00    inference(cnf_transformation,[],[f5])).
% 1.91/1.00  
% 1.91/1.00  fof(f59,plain,(
% 1.91/1.00    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.91/1.00    inference(definition_unfolding,[],[f42,f41])).
% 1.91/1.00  
% 1.91/1.00  cnf(c_2,plain,
% 1.91/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 1.91/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1396,plain,
% 1.91/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.91/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_4,plain,
% 1.91/1.00      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 1.91/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1394,plain,
% 1.91/1.00      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 1.91/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 1.91/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_9,plain,
% 1.91/1.00      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X1 = X0 ),
% 1.91/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1390,plain,
% 1.91/1.00      ( X0 = X1 | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) = iProver_top ),
% 1.91/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_8,plain,
% 1.91/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k1_tarski(X0),X1) ),
% 1.91/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1391,plain,
% 1.91/1.00      ( r2_hidden(X0,X1) != iProver_top
% 1.91/1.00      | r1_xboole_0(k1_tarski(X0),X1) != iProver_top ),
% 1.91/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1853,plain,
% 1.91/1.00      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 1.91/1.00      inference(superposition,[status(thm)],[c_1390,c_1391]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_2114,plain,
% 1.91/1.00      ( sK0(X0,k1_tarski(X1)) = X1
% 1.91/1.00      | r1_xboole_0(X0,k1_tarski(X1)) = iProver_top ),
% 1.91/1.00      inference(superposition,[status(thm)],[c_1394,c_1853]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1,plain,
% 1.91/1.00      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 1.91/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1397,plain,
% 1.91/1.00      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 1.91/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_2706,plain,
% 1.91/1.00      ( sK0(X0,k1_tarski(X1)) = X1
% 1.91/1.00      | k3_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0 ),
% 1.91/1.00      inference(superposition,[status(thm)],[c_2114,c_1397]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_5,plain,
% 1.91/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 1.91/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1393,plain,
% 1.91/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 1.91/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 1.91/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_15,negated_conjecture,
% 1.91/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
% 1.91/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_17,negated_conjecture,
% 1.91/1.00      ( v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 1.91/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_16,negated_conjecture,
% 1.91/1.00      ( v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 1.91/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_13,plain,
% 1.91/1.00      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.91/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.91/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.91/1.00      | ~ r2_hidden(X2,X0)
% 1.91/1.00      | ~ v1_xboole_0(X2)
% 1.91/1.00      | v1_xboole_0(X0)
% 1.91/1.00      | v1_xboole_0(X1) ),
% 1.91/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_18,negated_conjecture,
% 1.91/1.00      ( v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
% 1.91/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_281,plain,
% 1.91/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.91/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.91/1.00      | ~ r2_hidden(X2,X0)
% 1.91/1.00      | ~ v1_xboole_0(X2)
% 1.91/1.00      | v1_xboole_0(X1)
% 1.91/1.00      | v1_xboole_0(X0)
% 1.91/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.91/1.00      | sK2 != X0 ),
% 1.91/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_282,plain,
% 1.91/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.91/1.00      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.91/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.91/1.00      | ~ r2_hidden(X1,sK2)
% 1.91/1.00      | ~ v1_xboole_0(X1)
% 1.91/1.00      | v1_xboole_0(X0)
% 1.91/1.00      | v1_xboole_0(sK2)
% 1.91/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.91/1.00      inference(unflattening,[status(thm)],[c_281]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_19,negated_conjecture,
% 1.91/1.00      ( ~ v1_xboole_0(sK2) ),
% 1.91/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_284,plain,
% 1.91/1.00      ( v1_xboole_0(X0)
% 1.91/1.00      | ~ v1_xboole_0(X1)
% 1.91/1.00      | ~ r2_hidden(X1,sK2)
% 1.91/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.91/1.00      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.91/1.00      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.91/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.91/1.00      inference(global_propositional_subsumption,[status(thm)],[c_282,c_19]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_285,plain,
% 1.91/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.91/1.00      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.91/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.91/1.00      | ~ r2_hidden(X1,sK2)
% 1.91/1.00      | ~ v1_xboole_0(X1)
% 1.91/1.00      | v1_xboole_0(X0)
% 1.91/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.91/1.00      inference(renaming,[status(thm)],[c_284]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_364,plain,
% 1.91/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.91/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.91/1.00      | ~ r2_hidden(X1,sK2)
% 1.91/1.00      | ~ v1_xboole_0(X1)
% 1.91/1.00      | v1_xboole_0(X0)
% 1.91/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.91/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.91/1.00      | sK2 != sK2 ),
% 1.91/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_285]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_409,plain,
% 1.91/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.91/1.00      | ~ r2_hidden(X1,sK2)
% 1.91/1.00      | ~ v1_xboole_0(X1)
% 1.91/1.00      | v1_xboole_0(X0)
% 1.91/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.91/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.91/1.00      | sK2 != sK2 ),
% 1.91/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_364]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_450,plain,
% 1.91/1.00      ( ~ r2_hidden(X0,sK2)
% 1.91/1.00      | ~ v1_xboole_0(X0)
% 1.91/1.00      | v1_xboole_0(X1)
% 1.91/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.91/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 1.91/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.91/1.00      | sK2 != sK2 ),
% 1.91/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_409]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_689,plain,
% 1.91/1.00      ( ~ r2_hidden(X0,sK2)
% 1.91/1.00      | ~ v1_xboole_0(X0)
% 1.91/1.00      | v1_xboole_0(X1)
% 1.91/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.91/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 1.91/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
% 1.91/1.00      inference(equality_resolution_simp,[status(thm)],[c_450]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_976,plain,
% 1.91/1.00      ( ~ r2_hidden(X0,sK2) | ~ v1_xboole_0(X0) | ~ sP1_iProver_split ),
% 1.91/1.00      inference(splitting,
% 1.91/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.91/1.00                [c_689]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1386,plain,
% 1.91/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 1.91/1.00      | v1_xboole_0(X0) != iProver_top
% 1.91/1.00      | sP1_iProver_split != iProver_top ),
% 1.91/1.00      inference(predicate_to_equality,[status(thm)],[c_976]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1865,plain,
% 1.91/1.00      ( r1_xboole_0(sK2,X0) = iProver_top
% 1.91/1.00      | v1_xboole_0(sK0(sK2,X0)) != iProver_top
% 1.91/1.00      | sP1_iProver_split != iProver_top ),
% 1.91/1.00      inference(superposition,[status(thm)],[c_1393,c_1386]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_21,negated_conjecture,
% 1.91/1.00      ( ~ v2_struct_0(sK1) ),
% 1.91/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_22,plain,
% 1.91/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 1.91/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_20,negated_conjecture,
% 1.91/1.00      ( l1_struct_0(sK1) ),
% 1.91/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_23,plain,
% 1.91/1.00      ( l1_struct_0(sK1) = iProver_top ),
% 1.91/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_11,plain,
% 1.91/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 1.91/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_33,plain,
% 1.91/1.00      ( v2_struct_0(X0) = iProver_top
% 1.91/1.00      | l1_struct_0(X0) != iProver_top
% 1.91/1.00      | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
% 1.91/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_35,plain,
% 1.91/1.00      ( v2_struct_0(sK1) = iProver_top
% 1.91/1.00      | l1_struct_0(sK1) != iProver_top
% 1.91/1.00      | v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 1.91/1.00      inference(instantiation,[status(thm)],[c_33]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_977,plain,
% 1.91/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 1.91/1.00      inference(splitting,
% 1.91/1.00                [splitting(split),new_symbols(definition,[])],
% 1.91/1.00                [c_689]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1011,plain,
% 1.91/1.00      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 1.91/1.00      inference(predicate_to_equality,[status(thm)],[c_977]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_975,plain,
% 1.91/1.00      ( v1_xboole_0(X0)
% 1.91/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.91/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.91/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 1.91/1.00      | ~ sP0_iProver_split ),
% 1.91/1.00      inference(splitting,
% 1.91/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.91/1.00                [c_689]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1387,plain,
% 1.91/1.00      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.91/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.91/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 1.91/1.00      | v1_xboole_0(X0) = iProver_top
% 1.91/1.00      | sP0_iProver_split != iProver_top ),
% 1.91/1.00      inference(predicate_to_equality,[status(thm)],[c_975]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1666,plain,
% 1.91/1.00      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 1.91/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 1.91/1.00      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
% 1.91/1.00      | sP0_iProver_split != iProver_top ),
% 1.91/1.00      inference(equality_resolution,[status(thm)],[c_1387]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1700,plain,
% 1.91/1.00      ( v1_xboole_0(k2_struct_0(sK1)) = iProver_top
% 1.91/1.00      | sP0_iProver_split != iProver_top ),
% 1.91/1.00      inference(equality_resolution_simp,[status(thm)],[c_1666]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_2044,plain,
% 1.91/1.00      ( v1_xboole_0(sK0(sK2,X0)) != iProver_top
% 1.91/1.00      | r1_xboole_0(sK2,X0) = iProver_top ),
% 1.91/1.00      inference(global_propositional_subsumption,
% 1.91/1.00                [status(thm)],
% 1.91/1.00                [c_1865,c_22,c_23,c_35,c_1011,c_1700]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_2045,plain,
% 1.91/1.00      ( r1_xboole_0(sK2,X0) = iProver_top
% 1.91/1.00      | v1_xboole_0(sK0(sK2,X0)) != iProver_top ),
% 1.91/1.00      inference(renaming,[status(thm)],[c_2044]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_2826,plain,
% 1.91/1.00      ( k3_xboole_0(sK2,k1_tarski(X0)) = k1_xboole_0
% 1.91/1.00      | r1_xboole_0(sK2,k1_tarski(X0)) = iProver_top
% 1.91/1.00      | v1_xboole_0(X0) != iProver_top ),
% 1.91/1.00      inference(superposition,[status(thm)],[c_2706,c_2045]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_0,plain,
% 1.91/1.00      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 1.91/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1398,plain,
% 1.91/1.00      ( k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1) = iProver_top ),
% 1.91/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_2876,plain,
% 1.91/1.00      ( r1_xboole_0(sK2,k1_tarski(X0)) = iProver_top
% 1.91/1.00      | v1_xboole_0(X0) != iProver_top ),
% 1.91/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2826,c_1398]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_2881,plain,
% 1.91/1.00      ( k3_xboole_0(sK2,k1_tarski(X0)) = k1_xboole_0
% 1.91/1.00      | v1_xboole_0(X0) != iProver_top ),
% 1.91/1.00      inference(superposition,[status(thm)],[c_2876,c_1397]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_2968,plain,
% 1.91/1.00      ( k3_xboole_0(sK2,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
% 1.91/1.00      inference(superposition,[status(thm)],[c_1396,c_2881]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_10,plain,
% 1.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.91/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 1.91/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_441,plain,
% 1.91/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 1.91/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != k1_zfmisc_1(X2)
% 1.91/1.00      | sK2 != X0 ),
% 1.91/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_442,plain,
% 1.91/1.00      ( k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) = k7_subset_1(X1,sK2,X0)
% 1.91/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != k1_zfmisc_1(X1) ),
% 1.91/1.00      inference(unflattening,[status(thm)],[c_441]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1530,plain,
% 1.91/1.00      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))),sK2,X0) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
% 1.91/1.00      inference(equality_resolution,[status(thm)],[c_442]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_12,plain,
% 1.91/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.91/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.91/1.00      | v2_struct_0(X1)
% 1.91/1.00      | ~ l1_struct_0(X1)
% 1.91/1.00      | v1_xboole_0(X0)
% 1.91/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
% 1.91/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_329,plain,
% 1.91/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.91/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.91/1.00      | v2_struct_0(X1)
% 1.91/1.00      | v1_xboole_0(X0)
% 1.91/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
% 1.91/1.00      | sK1 != X1 ),
% 1.91/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_330,plain,
% 1.91/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 1.91/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 1.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 1.91/1.00      | v2_struct_0(sK1)
% 1.91/1.00      | v1_xboole_0(X0)
% 1.91/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) ),
% 1.91/1.00      inference(unflattening,[status(thm)],[c_329]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_334,plain,
% 1.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 1.91/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 1.91/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 1.91/1.00      | v1_xboole_0(X0)
% 1.91/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) ),
% 1.91/1.00      inference(global_propositional_subsumption,[status(thm)],[c_330,c_21]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_335,plain,
% 1.91/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 1.91/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 1.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 1.91/1.00      | v1_xboole_0(X0)
% 1.91/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) ),
% 1.91/1.00      inference(renaming,[status(thm)],[c_334]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_391,plain,
% 1.91/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 1.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 1.91/1.00      | v1_xboole_0(X0)
% 1.91/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0))
% 1.91/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 1.91/1.00      | sK2 != X0 ),
% 1.91/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_335]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_392,plain,
% 1.91/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 1.91/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 1.91/1.00      | v1_xboole_0(sK2)
% 1.91/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))),sK2,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 1.91/1.00      inference(unflattening,[status(thm)],[c_391]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_394,plain,
% 1.91/1.00      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))),sK2,k1_tarski(k1_xboole_0)) = k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 1.91/1.00      inference(global_propositional_subsumption,
% 1.91/1.00                [status(thm)],
% 1.91/1.00                [c_392,c_19,c_17,c_15]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1554,plain,
% 1.91/1.00      ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0))) ),
% 1.91/1.00      inference(demodulation,[status(thm)],[c_1530,c_394]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_14,negated_conjecture,
% 1.91/1.00      ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != sK2 ),
% 1.91/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1590,plain,
% 1.91/1.00      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(k1_xboole_0))) != sK2 ),
% 1.91/1.00      inference(demodulation,[status(thm)],[c_1554,c_14]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_3061,plain,
% 1.91/1.00      ( k5_xboole_0(sK2,k1_xboole_0) != sK2 ),
% 1.91/1.00      inference(demodulation,[status(thm)],[c_2968,c_1590]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_7,plain,
% 1.91/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 1.91/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1392,plain,
% 1.91/1.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 1.91/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1746,plain,
% 1.91/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.91/1.00      inference(superposition,[status(thm)],[c_1392,c_1397]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_6,plain,
% 1.91/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 1.91/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_1755,plain,
% 1.91/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.91/1.00      inference(demodulation,[status(thm)],[c_1746,c_6]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_3067,plain,
% 1.91/1.00      ( sK2 != sK2 ),
% 1.91/1.00      inference(demodulation,[status(thm)],[c_3061,c_1755]) ).
% 1.91/1.00  
% 1.91/1.00  cnf(c_3068,plain,
% 1.91/1.00      ( $false ),
% 1.91/1.00      inference(equality_resolution_simp,[status(thm)],[c_3067]) ).
% 1.91/1.00  
% 1.91/1.00  
% 1.91/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.91/1.00  
% 1.91/1.00  ------                               Statistics
% 1.91/1.00  
% 1.91/1.00  ------ General
% 1.91/1.00  
% 1.91/1.00  abstr_ref_over_cycles:                  0
% 1.91/1.00  abstr_ref_under_cycles:                 0
% 1.91/1.00  gc_basic_clause_elim:                   0
% 1.91/1.00  forced_gc_time:                         0
% 1.91/1.00  parsing_time:                           0.012
% 1.91/1.00  unif_index_cands_time:                  0.
% 1.91/1.00  unif_index_add_time:                    0.
% 1.91/1.00  orderings_time:                         0.
% 1.91/1.00  out_proof_time:                         0.011
% 1.91/1.00  total_time:                             0.122
% 1.91/1.00  num_of_symbols:                         57
% 1.91/1.00  num_of_terms:                           2283
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing
% 1.91/1.00  
% 1.91/1.00  num_of_splits:                          2
% 1.91/1.00  num_of_split_atoms:                     2
% 1.91/1.00  num_of_reused_defs:                     0
% 1.91/1.00  num_eq_ax_congr_red:                    10
% 1.91/1.00  num_of_sem_filtered_clauses:            1
% 1.91/1.00  num_of_subtypes:                        0
% 1.91/1.00  monotx_restored_types:                  0
% 1.91/1.00  sat_num_of_epr_types:                   0
% 1.91/1.00  sat_num_of_non_cyclic_types:            0
% 1.91/1.00  sat_guarded_non_collapsed_types:        0
% 1.91/1.00  num_pure_diseq_elim:                    0
% 1.91/1.00  simp_replaced_by:                       0
% 1.91/1.00  res_preprocessed:                       107
% 1.91/1.00  prep_upred:                             0
% 1.91/1.00  prep_unflattend:                        51
% 1.91/1.00  smt_new_axioms:                         0
% 1.91/1.00  pred_elim_cands:                        3
% 1.91/1.00  pred_elim:                              6
% 1.91/1.00  pred_elim_cl:                           6
% 1.91/1.00  pred_elim_cycles:                       8
% 1.91/1.00  merged_defs:                            8
% 1.91/1.00  merged_defs_ncl:                        0
% 1.91/1.00  bin_hyper_res:                          8
% 1.91/1.00  prep_cycles:                            4
% 1.91/1.00  pred_elim_time:                         0.01
% 1.91/1.00  splitting_time:                         0.
% 1.91/1.00  sem_filter_time:                        0.
% 1.91/1.00  monotx_time:                            0.
% 1.91/1.00  subtype_inf_time:                       0.
% 1.91/1.00  
% 1.91/1.00  ------ Problem properties
% 1.91/1.00  
% 1.91/1.00  clauses:                                18
% 1.91/1.00  conjectures:                            2
% 1.91/1.00  epr:                                    6
% 1.91/1.00  horn:                                   14
% 1.91/1.00  ground:                                 6
% 1.91/1.00  unary:                                  7
% 1.91/1.00  binary:                                 8
% 1.91/1.00  lits:                                   34
% 1.91/1.00  lits_eq:                                11
% 1.91/1.00  fd_pure:                                0
% 1.91/1.00  fd_pseudo:                              0
% 1.91/1.00  fd_cond:                                0
% 1.91/1.00  fd_pseudo_cond:                         1
% 1.91/1.00  ac_symbols:                             0
% 1.91/1.00  
% 1.91/1.00  ------ Propositional Solver
% 1.91/1.00  
% 1.91/1.00  prop_solver_calls:                      29
% 1.91/1.00  prop_fast_solver_calls:                 673
% 1.91/1.00  smt_solver_calls:                       0
% 1.91/1.00  smt_fast_solver_calls:                  0
% 1.91/1.00  prop_num_of_clauses:                    929
% 1.91/1.00  prop_preprocess_simplified:             3784
% 1.91/1.00  prop_fo_subsumed:                       10
% 1.91/1.00  prop_solver_time:                       0.
% 1.91/1.00  smt_solver_time:                        0.
% 1.91/1.00  smt_fast_solver_time:                   0.
% 1.91/1.00  prop_fast_solver_time:                  0.
% 1.91/1.00  prop_unsat_core_time:                   0.
% 1.91/1.00  
% 1.91/1.00  ------ QBF
% 1.91/1.00  
% 1.91/1.00  qbf_q_res:                              0
% 1.91/1.00  qbf_num_tautologies:                    0
% 1.91/1.00  qbf_prep_cycles:                        0
% 1.91/1.00  
% 1.91/1.00  ------ BMC1
% 1.91/1.00  
% 1.91/1.00  bmc1_current_bound:                     -1
% 1.91/1.00  bmc1_last_solved_bound:                 -1
% 1.91/1.00  bmc1_unsat_core_size:                   -1
% 1.91/1.00  bmc1_unsat_core_parents_size:           -1
% 1.91/1.00  bmc1_merge_next_fun:                    0
% 1.91/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.91/1.00  
% 1.91/1.00  ------ Instantiation
% 1.91/1.00  
% 1.91/1.00  inst_num_of_clauses:                    335
% 1.91/1.00  inst_num_in_passive:                    153
% 1.91/1.00  inst_num_in_active:                     146
% 1.91/1.00  inst_num_in_unprocessed:                36
% 1.91/1.00  inst_num_of_loops:                      220
% 1.91/1.00  inst_num_of_learning_restarts:          0
% 1.91/1.00  inst_num_moves_active_passive:          69
% 1.91/1.00  inst_lit_activity:                      0
% 1.91/1.00  inst_lit_activity_moves:                0
% 1.91/1.00  inst_num_tautologies:                   0
% 1.91/1.00  inst_num_prop_implied:                  0
% 1.91/1.00  inst_num_existing_simplified:           0
% 1.91/1.00  inst_num_eq_res_simplified:             0
% 1.91/1.00  inst_num_child_elim:                    0
% 1.91/1.00  inst_num_of_dismatching_blockings:      70
% 1.91/1.00  inst_num_of_non_proper_insts:           279
% 1.91/1.00  inst_num_of_duplicates:                 0
% 1.91/1.00  inst_inst_num_from_inst_to_res:         0
% 1.91/1.00  inst_dismatching_checking_time:         0.
% 1.91/1.00  
% 1.91/1.00  ------ Resolution
% 1.91/1.00  
% 1.91/1.00  res_num_of_clauses:                     0
% 1.91/1.00  res_num_in_passive:                     0
% 1.91/1.00  res_num_in_active:                      0
% 1.91/1.00  res_num_of_loops:                       111
% 1.91/1.00  res_forward_subset_subsumed:            42
% 1.91/1.00  res_backward_subset_subsumed:           0
% 1.91/1.00  res_forward_subsumed:                   0
% 1.91/1.00  res_backward_subsumed:                  1
% 1.91/1.00  res_forward_subsumption_resolution:     0
% 1.91/1.00  res_backward_subsumption_resolution:    0
% 1.91/1.00  res_clause_to_clause_subsumption:       190
% 1.91/1.00  res_orphan_elimination:                 0
% 1.91/1.00  res_tautology_del:                      45
% 1.91/1.00  res_num_eq_res_simplified:              1
% 1.91/1.00  res_num_sel_changes:                    0
% 1.91/1.00  res_moves_from_active_to_pass:          0
% 1.91/1.00  
% 1.91/1.00  ------ Superposition
% 1.91/1.00  
% 1.91/1.00  sup_time_total:                         0.
% 1.91/1.00  sup_time_generating:                    0.
% 1.91/1.00  sup_time_sim_full:                      0.
% 1.91/1.00  sup_time_sim_immed:                     0.
% 1.91/1.00  
% 1.91/1.00  sup_num_of_clauses:                     50
% 1.91/1.00  sup_num_in_active:                      36
% 1.91/1.00  sup_num_in_passive:                     14
% 1.91/1.00  sup_num_of_loops:                       42
% 1.91/1.00  sup_fw_superposition:                   25
% 1.91/1.00  sup_bw_superposition:                   25
% 1.91/1.00  sup_immediate_simplified:               0
% 1.91/1.00  sup_given_eliminated:                   0
% 1.91/1.00  comparisons_done:                       0
% 1.91/1.00  comparisons_avoided:                    4
% 1.91/1.00  
% 1.91/1.00  ------ Simplifications
% 1.91/1.00  
% 1.91/1.00  
% 1.91/1.00  sim_fw_subset_subsumed:                 0
% 1.91/1.00  sim_bw_subset_subsumed:                 1
% 1.91/1.00  sim_fw_subsumed:                        0
% 1.91/1.00  sim_bw_subsumed:                        0
% 1.91/1.00  sim_fw_subsumption_res:                 1
% 1.91/1.00  sim_bw_subsumption_res:                 0
% 1.91/1.00  sim_tautology_del:                      1
% 1.91/1.00  sim_eq_tautology_del:                   2
% 1.91/1.00  sim_eq_res_simp:                        1
% 1.91/1.00  sim_fw_demodulated:                     2
% 1.91/1.00  sim_bw_demodulated:                     5
% 1.91/1.00  sim_light_normalised:                   0
% 1.91/1.00  sim_joinable_taut:                      0
% 1.91/1.00  sim_joinable_simp:                      0
% 1.91/1.00  sim_ac_normalised:                      0
% 1.91/1.00  sim_smt_subsumption:                    0
% 1.91/1.00  
%------------------------------------------------------------------------------
