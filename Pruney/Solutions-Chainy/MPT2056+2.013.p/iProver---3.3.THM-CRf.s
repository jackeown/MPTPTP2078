%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:06 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 436 expanded)
%              Number of clauses        :   69 ( 106 expanded)
%              Number of leaves         :   17 ( 124 expanded)
%              Depth                    :   25
%              Number of atoms          :  401 (2369 expanded)
%              Number of equality atoms :  128 ( 451 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
     => ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) != sK4
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
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
          ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))
    & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))
    & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))
    & ~ v1_xboole_0(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f42,f41])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
    inference(definition_unfolding,[],[f69,f60])).

fof(f67,plain,(
    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f67,f60])).

fof(f68,plain,(
    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f68,f60])).

fof(f15,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f62,f60,f60,f60,f60])).

fof(f66,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(definition_unfolding,[],[f66,f60])).

fof(f65,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f56,f52])).

fof(f14,axiom,(
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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f61,f60,f60,f60,f60])).

fof(f70,plain,(
    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f53,f52])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1425,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10,plain,
    ( r1_xboole_0(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1421,plain,
    ( r1_xboole_0(k1_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1426,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2237,plain,
    ( k3_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1426])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_20,negated_conjecture,
    ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_19,negated_conjecture,
    ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_16,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_21,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_317,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_318,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_320,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_318,c_22])).

cnf(c_321,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_320])).

cnf(c_400,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_321])).

cnf(c_445,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_400])).

cnf(c_486,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_445])).

cnf(c_685,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
    inference(equality_resolution_simp,[status(thm)],[c_486])).

cnf(c_958,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_685])).

cnf(c_1415,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_958])).

cnf(c_3258,plain,
    ( k3_xboole_0(k1_tarski(X0),sK4) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_2237,c_1415])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_25,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_36,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_38,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_959,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_685])).

cnf(c_992,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_959])).

cnf(c_974,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1607,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) = u1_struct_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != X0 ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_1720,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) = u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_1607])).

cnf(c_961,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1721,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) = k3_lattice3(k1_lattice3(k2_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_957,plain,
    ( v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_685])).

cnf(c_1416,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_957])).

cnf(c_1809,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1416])).

cnf(c_3291,plain,
    ( v1_xboole_0(X0) != iProver_top
    | k3_xboole_0(k1_tarski(X0),sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3258,c_25,c_26,c_38,c_992,c_1720,c_1721,c_1809])).

cnf(c_3292,plain,
    ( k3_xboole_0(k1_tarski(X0),sK4) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3291])).

cnf(c_3299,plain,
    ( k3_xboole_0(k1_tarski(k1_xboole_0),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1425,c_3292])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3497,plain,
    ( k3_xboole_0(sK4,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3299,c_0])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_477,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_478,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) = k7_subset_1(X1,sK4,X0)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_1575,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,X0) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
    inference(equality_resolution,[status(thm)],[c_478])).

cnf(c_15,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_365,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_366,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v2_struct_0(sK3)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_24])).

cnf(c_371,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(renaming,[status(thm)],[c_370])).

cnf(c_427,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_371])).

cnf(c_428,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v1_xboole_0(sK4)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_430,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_428,c_22,c_20,c_18])).

cnf(c_1594,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_1575,c_430])).

cnf(c_17,negated_conjecture,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1602,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) != sK4 ),
    inference(demodulation,[status(thm)],[c_1594,c_17])).

cnf(c_3515,plain,
    ( k5_xboole_0(sK4,k1_xboole_0) != sK4 ),
    inference(demodulation,[status(thm)],[c_3497,c_1602])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1422,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1956,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1422,c_1426])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2010,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1956,c_8])).

cnf(c_3521,plain,
    ( sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_3515,c_2010])).

cnf(c_3522,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3521])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n025.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.18/0.32  % DateTime   : Tue Dec  1 10:06:20 EST 2020
% 0.18/0.32  % CPUTime    : 
% 0.18/0.32  % Running in FOF mode
% 2.25/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/0.96  
% 2.25/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.25/0.96  
% 2.25/0.96  ------  iProver source info
% 2.25/0.96  
% 2.25/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.25/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.25/0.96  git: non_committed_changes: false
% 2.25/0.96  git: last_make_outside_of_git: false
% 2.25/0.96  
% 2.25/0.96  ------ 
% 2.25/0.96  
% 2.25/0.96  ------ Input Options
% 2.25/0.96  
% 2.25/0.96  --out_options                           all
% 2.25/0.96  --tptp_safe_out                         true
% 2.25/0.96  --problem_path                          ""
% 2.25/0.96  --include_path                          ""
% 2.25/0.96  --clausifier                            res/vclausify_rel
% 2.25/0.96  --clausifier_options                    --mode clausify
% 2.25/0.96  --stdin                                 false
% 2.25/0.96  --stats_out                             all
% 2.25/0.96  
% 2.25/0.96  ------ General Options
% 2.25/0.96  
% 2.25/0.96  --fof                                   false
% 2.25/0.96  --time_out_real                         305.
% 2.25/0.96  --time_out_virtual                      -1.
% 2.25/0.96  --symbol_type_check                     false
% 2.25/0.96  --clausify_out                          false
% 2.25/0.96  --sig_cnt_out                           false
% 2.25/0.96  --trig_cnt_out                          false
% 2.25/0.96  --trig_cnt_out_tolerance                1.
% 2.25/0.96  --trig_cnt_out_sk_spl                   false
% 2.25/0.96  --abstr_cl_out                          false
% 2.25/0.96  
% 2.25/0.96  ------ Global Options
% 2.25/0.96  
% 2.25/0.96  --schedule                              default
% 2.25/0.96  --add_important_lit                     false
% 2.25/0.96  --prop_solver_per_cl                    1000
% 2.25/0.96  --min_unsat_core                        false
% 2.25/0.96  --soft_assumptions                      false
% 2.25/0.96  --soft_lemma_size                       3
% 2.25/0.96  --prop_impl_unit_size                   0
% 2.25/0.96  --prop_impl_unit                        []
% 2.25/0.96  --share_sel_clauses                     true
% 2.25/0.96  --reset_solvers                         false
% 2.25/0.96  --bc_imp_inh                            [conj_cone]
% 2.25/0.96  --conj_cone_tolerance                   3.
% 2.25/0.96  --extra_neg_conj                        none
% 2.25/0.96  --large_theory_mode                     true
% 2.25/0.96  --prolific_symb_bound                   200
% 2.25/0.96  --lt_threshold                          2000
% 2.25/0.96  --clause_weak_htbl                      true
% 2.25/0.96  --gc_record_bc_elim                     false
% 2.25/0.96  
% 2.25/0.96  ------ Preprocessing Options
% 2.25/0.96  
% 2.25/0.96  --preprocessing_flag                    true
% 2.25/0.96  --time_out_prep_mult                    0.1
% 2.25/0.96  --splitting_mode                        input
% 2.25/0.96  --splitting_grd                         true
% 2.25/0.96  --splitting_cvd                         false
% 2.25/0.96  --splitting_cvd_svl                     false
% 2.25/0.96  --splitting_nvd                         32
% 2.25/0.96  --sub_typing                            true
% 2.25/0.96  --prep_gs_sim                           true
% 2.25/0.96  --prep_unflatten                        true
% 2.25/0.96  --prep_res_sim                          true
% 2.25/0.96  --prep_upred                            true
% 2.25/0.96  --prep_sem_filter                       exhaustive
% 2.25/0.96  --prep_sem_filter_out                   false
% 2.25/0.96  --pred_elim                             true
% 2.25/0.96  --res_sim_input                         true
% 2.25/0.96  --eq_ax_congr_red                       true
% 2.25/0.96  --pure_diseq_elim                       true
% 2.25/0.96  --brand_transform                       false
% 2.25/0.96  --non_eq_to_eq                          false
% 2.25/0.96  --prep_def_merge                        true
% 2.25/0.96  --prep_def_merge_prop_impl              false
% 2.25/0.96  --prep_def_merge_mbd                    true
% 2.25/0.96  --prep_def_merge_tr_red                 false
% 2.25/0.96  --prep_def_merge_tr_cl                  false
% 2.25/0.96  --smt_preprocessing                     true
% 2.25/0.96  --smt_ac_axioms                         fast
% 2.25/0.96  --preprocessed_out                      false
% 2.25/0.96  --preprocessed_stats                    false
% 2.25/0.96  
% 2.25/0.96  ------ Abstraction refinement Options
% 2.25/0.96  
% 2.25/0.96  --abstr_ref                             []
% 2.25/0.96  --abstr_ref_prep                        false
% 2.25/0.96  --abstr_ref_until_sat                   false
% 2.25/0.96  --abstr_ref_sig_restrict                funpre
% 2.25/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.25/0.96  --abstr_ref_under                       []
% 2.25/0.96  
% 2.25/0.96  ------ SAT Options
% 2.25/0.96  
% 2.25/0.96  --sat_mode                              false
% 2.25/0.96  --sat_fm_restart_options                ""
% 2.25/0.96  --sat_gr_def                            false
% 2.25/0.96  --sat_epr_types                         true
% 2.25/0.96  --sat_non_cyclic_types                  false
% 2.25/0.96  --sat_finite_models                     false
% 2.25/0.96  --sat_fm_lemmas                         false
% 2.25/0.96  --sat_fm_prep                           false
% 2.25/0.97  --sat_fm_uc_incr                        true
% 2.25/0.97  --sat_out_model                         small
% 2.25/0.97  --sat_out_clauses                       false
% 2.25/0.97  
% 2.25/0.97  ------ QBF Options
% 2.25/0.97  
% 2.25/0.97  --qbf_mode                              false
% 2.25/0.97  --qbf_elim_univ                         false
% 2.25/0.97  --qbf_dom_inst                          none
% 2.25/0.97  --qbf_dom_pre_inst                      false
% 2.25/0.97  --qbf_sk_in                             false
% 2.25/0.97  --qbf_pred_elim                         true
% 2.25/0.97  --qbf_split                             512
% 2.25/0.97  
% 2.25/0.97  ------ BMC1 Options
% 2.25/0.97  
% 2.25/0.97  --bmc1_incremental                      false
% 2.25/0.97  --bmc1_axioms                           reachable_all
% 2.25/0.97  --bmc1_min_bound                        0
% 2.25/0.97  --bmc1_max_bound                        -1
% 2.25/0.97  --bmc1_max_bound_default                -1
% 2.25/0.97  --bmc1_symbol_reachability              true
% 2.25/0.97  --bmc1_property_lemmas                  false
% 2.25/0.97  --bmc1_k_induction                      false
% 2.25/0.97  --bmc1_non_equiv_states                 false
% 2.25/0.97  --bmc1_deadlock                         false
% 2.25/0.97  --bmc1_ucm                              false
% 2.25/0.97  --bmc1_add_unsat_core                   none
% 2.25/0.97  --bmc1_unsat_core_children              false
% 2.25/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.25/0.97  --bmc1_out_stat                         full
% 2.25/0.97  --bmc1_ground_init                      false
% 2.25/0.97  --bmc1_pre_inst_next_state              false
% 2.25/0.97  --bmc1_pre_inst_state                   false
% 2.25/0.97  --bmc1_pre_inst_reach_state             false
% 2.25/0.97  --bmc1_out_unsat_core                   false
% 2.25/0.97  --bmc1_aig_witness_out                  false
% 2.25/0.97  --bmc1_verbose                          false
% 2.25/0.97  --bmc1_dump_clauses_tptp                false
% 2.25/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.25/0.97  --bmc1_dump_file                        -
% 2.25/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.25/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.25/0.97  --bmc1_ucm_extend_mode                  1
% 2.25/0.97  --bmc1_ucm_init_mode                    2
% 2.25/0.97  --bmc1_ucm_cone_mode                    none
% 2.25/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.25/0.97  --bmc1_ucm_relax_model                  4
% 2.25/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.25/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.25/0.97  --bmc1_ucm_layered_model                none
% 2.25/0.97  --bmc1_ucm_max_lemma_size               10
% 2.25/0.97  
% 2.25/0.97  ------ AIG Options
% 2.25/0.97  
% 2.25/0.97  --aig_mode                              false
% 2.25/0.97  
% 2.25/0.97  ------ Instantiation Options
% 2.25/0.97  
% 2.25/0.97  --instantiation_flag                    true
% 2.25/0.97  --inst_sos_flag                         false
% 2.25/0.97  --inst_sos_phase                        true
% 2.25/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.25/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.25/0.97  --inst_lit_sel_side                     num_symb
% 2.25/0.97  --inst_solver_per_active                1400
% 2.25/0.97  --inst_solver_calls_frac                1.
% 2.25/0.97  --inst_passive_queue_type               priority_queues
% 2.25/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.25/0.97  --inst_passive_queues_freq              [25;2]
% 2.25/0.97  --inst_dismatching                      true
% 2.25/0.97  --inst_eager_unprocessed_to_passive     true
% 2.25/0.97  --inst_prop_sim_given                   true
% 2.25/0.97  --inst_prop_sim_new                     false
% 2.25/0.97  --inst_subs_new                         false
% 2.25/0.97  --inst_eq_res_simp                      false
% 2.25/0.97  --inst_subs_given                       false
% 2.25/0.97  --inst_orphan_elimination               true
% 2.25/0.97  --inst_learning_loop_flag               true
% 2.25/0.97  --inst_learning_start                   3000
% 2.25/0.97  --inst_learning_factor                  2
% 2.25/0.97  --inst_start_prop_sim_after_learn       3
% 2.25/0.97  --inst_sel_renew                        solver
% 2.25/0.97  --inst_lit_activity_flag                true
% 2.25/0.97  --inst_restr_to_given                   false
% 2.25/0.97  --inst_activity_threshold               500
% 2.25/0.97  --inst_out_proof                        true
% 2.25/0.97  
% 2.25/0.97  ------ Resolution Options
% 2.25/0.97  
% 2.25/0.97  --resolution_flag                       true
% 2.25/0.97  --res_lit_sel                           adaptive
% 2.25/0.97  --res_lit_sel_side                      none
% 2.25/0.97  --res_ordering                          kbo
% 2.25/0.97  --res_to_prop_solver                    active
% 2.25/0.97  --res_prop_simpl_new                    false
% 2.25/0.97  --res_prop_simpl_given                  true
% 2.25/0.97  --res_passive_queue_type                priority_queues
% 2.25/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.25/0.97  --res_passive_queues_freq               [15;5]
% 2.25/0.97  --res_forward_subs                      full
% 2.25/0.97  --res_backward_subs                     full
% 2.25/0.97  --res_forward_subs_resolution           true
% 2.25/0.97  --res_backward_subs_resolution          true
% 2.25/0.97  --res_orphan_elimination                true
% 2.25/0.97  --res_time_limit                        2.
% 2.25/0.97  --res_out_proof                         true
% 2.25/0.97  
% 2.25/0.97  ------ Superposition Options
% 2.25/0.97  
% 2.25/0.97  --superposition_flag                    true
% 2.25/0.97  --sup_passive_queue_type                priority_queues
% 2.25/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.25/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.25/0.97  --demod_completeness_check              fast
% 2.25/0.97  --demod_use_ground                      true
% 2.25/0.97  --sup_to_prop_solver                    passive
% 2.25/0.97  --sup_prop_simpl_new                    true
% 2.25/0.97  --sup_prop_simpl_given                  true
% 2.25/0.97  --sup_fun_splitting                     false
% 2.25/0.97  --sup_smt_interval                      50000
% 2.25/0.97  
% 2.25/0.97  ------ Superposition Simplification Setup
% 2.25/0.97  
% 2.25/0.97  --sup_indices_passive                   []
% 2.25/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.25/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.97  --sup_full_bw                           [BwDemod]
% 2.25/0.97  --sup_immed_triv                        [TrivRules]
% 2.25/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.25/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.97  --sup_immed_bw_main                     []
% 2.25/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.25/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.97  
% 2.25/0.97  ------ Combination Options
% 2.25/0.97  
% 2.25/0.97  --comb_res_mult                         3
% 2.25/0.97  --comb_sup_mult                         2
% 2.25/0.97  --comb_inst_mult                        10
% 2.25/0.97  
% 2.25/0.97  ------ Debug Options
% 2.25/0.97  
% 2.25/0.97  --dbg_backtrace                         false
% 2.25/0.97  --dbg_dump_prop_clauses                 false
% 2.25/0.97  --dbg_dump_prop_clauses_file            -
% 2.25/0.97  --dbg_out_stat                          false
% 2.25/0.97  ------ Parsing...
% 2.25/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.25/0.97  
% 2.25/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.25/0.97  
% 2.25/0.97  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.25/0.97  
% 2.25/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.25/0.97  ------ Proving...
% 2.25/0.97  ------ Problem Properties 
% 2.25/0.97  
% 2.25/0.97  
% 2.25/0.97  clauses                                 21
% 2.25/0.97  conjectures                             2
% 2.25/0.97  EPR                                     6
% 2.25/0.97  Horn                                    15
% 2.25/0.97  unary                                   8
% 2.25/0.97  binary                                  10
% 2.25/0.97  lits                                    43
% 2.25/0.97  lits eq                                 13
% 2.25/0.97  fd_pure                                 0
% 2.25/0.97  fd_pseudo                               0
% 2.25/0.97  fd_cond                                 2
% 2.25/0.97  fd_pseudo_cond                          0
% 2.25/0.97  AC symbols                              0
% 2.25/0.97  
% 2.25/0.97  ------ Schedule dynamic 5 is on 
% 2.25/0.97  
% 2.25/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.25/0.97  
% 2.25/0.97  
% 2.25/0.97  ------ 
% 2.25/0.97  Current options:
% 2.25/0.97  ------ 
% 2.25/0.97  
% 2.25/0.97  ------ Input Options
% 2.25/0.97  
% 2.25/0.97  --out_options                           all
% 2.25/0.97  --tptp_safe_out                         true
% 2.25/0.97  --problem_path                          ""
% 2.25/0.97  --include_path                          ""
% 2.25/0.97  --clausifier                            res/vclausify_rel
% 2.25/0.97  --clausifier_options                    --mode clausify
% 2.25/0.97  --stdin                                 false
% 2.25/0.97  --stats_out                             all
% 2.25/0.97  
% 2.25/0.97  ------ General Options
% 2.25/0.97  
% 2.25/0.97  --fof                                   false
% 2.25/0.97  --time_out_real                         305.
% 2.25/0.97  --time_out_virtual                      -1.
% 2.25/0.97  --symbol_type_check                     false
% 2.25/0.97  --clausify_out                          false
% 2.25/0.97  --sig_cnt_out                           false
% 2.25/0.97  --trig_cnt_out                          false
% 2.25/0.97  --trig_cnt_out_tolerance                1.
% 2.25/0.97  --trig_cnt_out_sk_spl                   false
% 2.25/0.97  --abstr_cl_out                          false
% 2.25/0.97  
% 2.25/0.97  ------ Global Options
% 2.25/0.97  
% 2.25/0.97  --schedule                              default
% 2.25/0.97  --add_important_lit                     false
% 2.25/0.97  --prop_solver_per_cl                    1000
% 2.25/0.97  --min_unsat_core                        false
% 2.25/0.97  --soft_assumptions                      false
% 2.25/0.97  --soft_lemma_size                       3
% 2.25/0.97  --prop_impl_unit_size                   0
% 2.25/0.97  --prop_impl_unit                        []
% 2.25/0.97  --share_sel_clauses                     true
% 2.25/0.97  --reset_solvers                         false
% 2.25/0.97  --bc_imp_inh                            [conj_cone]
% 2.25/0.97  --conj_cone_tolerance                   3.
% 2.25/0.97  --extra_neg_conj                        none
% 2.25/0.97  --large_theory_mode                     true
% 2.25/0.97  --prolific_symb_bound                   200
% 2.25/0.97  --lt_threshold                          2000
% 2.25/0.97  --clause_weak_htbl                      true
% 2.25/0.97  --gc_record_bc_elim                     false
% 2.25/0.97  
% 2.25/0.97  ------ Preprocessing Options
% 2.25/0.97  
% 2.25/0.97  --preprocessing_flag                    true
% 2.25/0.97  --time_out_prep_mult                    0.1
% 2.25/0.97  --splitting_mode                        input
% 2.25/0.97  --splitting_grd                         true
% 2.25/0.97  --splitting_cvd                         false
% 2.25/0.97  --splitting_cvd_svl                     false
% 2.25/0.97  --splitting_nvd                         32
% 2.25/0.97  --sub_typing                            true
% 2.25/0.97  --prep_gs_sim                           true
% 2.25/0.97  --prep_unflatten                        true
% 2.25/0.97  --prep_res_sim                          true
% 2.25/0.97  --prep_upred                            true
% 2.25/0.97  --prep_sem_filter                       exhaustive
% 2.25/0.97  --prep_sem_filter_out                   false
% 2.25/0.97  --pred_elim                             true
% 2.25/0.97  --res_sim_input                         true
% 2.25/0.97  --eq_ax_congr_red                       true
% 2.25/0.97  --pure_diseq_elim                       true
% 2.25/0.97  --brand_transform                       false
% 2.25/0.97  --non_eq_to_eq                          false
% 2.25/0.97  --prep_def_merge                        true
% 2.25/0.97  --prep_def_merge_prop_impl              false
% 2.25/0.97  --prep_def_merge_mbd                    true
% 2.25/0.97  --prep_def_merge_tr_red                 false
% 2.25/0.97  --prep_def_merge_tr_cl                  false
% 2.25/0.97  --smt_preprocessing                     true
% 2.25/0.97  --smt_ac_axioms                         fast
% 2.25/0.97  --preprocessed_out                      false
% 2.25/0.97  --preprocessed_stats                    false
% 2.25/0.97  
% 2.25/0.97  ------ Abstraction refinement Options
% 2.25/0.97  
% 2.25/0.97  --abstr_ref                             []
% 2.25/0.97  --abstr_ref_prep                        false
% 2.25/0.97  --abstr_ref_until_sat                   false
% 2.25/0.97  --abstr_ref_sig_restrict                funpre
% 2.25/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.25/0.97  --abstr_ref_under                       []
% 2.25/0.97  
% 2.25/0.97  ------ SAT Options
% 2.25/0.97  
% 2.25/0.97  --sat_mode                              false
% 2.25/0.97  --sat_fm_restart_options                ""
% 2.25/0.97  --sat_gr_def                            false
% 2.25/0.97  --sat_epr_types                         true
% 2.25/0.97  --sat_non_cyclic_types                  false
% 2.25/0.97  --sat_finite_models                     false
% 2.25/0.97  --sat_fm_lemmas                         false
% 2.25/0.97  --sat_fm_prep                           false
% 2.25/0.97  --sat_fm_uc_incr                        true
% 2.25/0.97  --sat_out_model                         small
% 2.25/0.97  --sat_out_clauses                       false
% 2.25/0.97  
% 2.25/0.97  ------ QBF Options
% 2.25/0.97  
% 2.25/0.97  --qbf_mode                              false
% 2.25/0.97  --qbf_elim_univ                         false
% 2.25/0.97  --qbf_dom_inst                          none
% 2.25/0.97  --qbf_dom_pre_inst                      false
% 2.25/0.97  --qbf_sk_in                             false
% 2.25/0.97  --qbf_pred_elim                         true
% 2.25/0.97  --qbf_split                             512
% 2.25/0.97  
% 2.25/0.97  ------ BMC1 Options
% 2.25/0.97  
% 2.25/0.97  --bmc1_incremental                      false
% 2.25/0.97  --bmc1_axioms                           reachable_all
% 2.25/0.97  --bmc1_min_bound                        0
% 2.25/0.97  --bmc1_max_bound                        -1
% 2.25/0.97  --bmc1_max_bound_default                -1
% 2.25/0.97  --bmc1_symbol_reachability              true
% 2.25/0.97  --bmc1_property_lemmas                  false
% 2.25/0.97  --bmc1_k_induction                      false
% 2.25/0.97  --bmc1_non_equiv_states                 false
% 2.25/0.97  --bmc1_deadlock                         false
% 2.25/0.97  --bmc1_ucm                              false
% 2.25/0.97  --bmc1_add_unsat_core                   none
% 2.25/0.97  --bmc1_unsat_core_children              false
% 2.25/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.25/0.97  --bmc1_out_stat                         full
% 2.25/0.97  --bmc1_ground_init                      false
% 2.25/0.97  --bmc1_pre_inst_next_state              false
% 2.25/0.97  --bmc1_pre_inst_state                   false
% 2.25/0.97  --bmc1_pre_inst_reach_state             false
% 2.25/0.97  --bmc1_out_unsat_core                   false
% 2.25/0.97  --bmc1_aig_witness_out                  false
% 2.25/0.97  --bmc1_verbose                          false
% 2.25/0.97  --bmc1_dump_clauses_tptp                false
% 2.25/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.25/0.97  --bmc1_dump_file                        -
% 2.25/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.25/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.25/0.97  --bmc1_ucm_extend_mode                  1
% 2.25/0.97  --bmc1_ucm_init_mode                    2
% 2.25/0.97  --bmc1_ucm_cone_mode                    none
% 2.25/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.25/0.97  --bmc1_ucm_relax_model                  4
% 2.25/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.25/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.25/0.97  --bmc1_ucm_layered_model                none
% 2.25/0.97  --bmc1_ucm_max_lemma_size               10
% 2.25/0.97  
% 2.25/0.97  ------ AIG Options
% 2.25/0.97  
% 2.25/0.97  --aig_mode                              false
% 2.25/0.97  
% 2.25/0.97  ------ Instantiation Options
% 2.25/0.97  
% 2.25/0.97  --instantiation_flag                    true
% 2.25/0.97  --inst_sos_flag                         false
% 2.25/0.97  --inst_sos_phase                        true
% 2.25/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.25/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.25/0.97  --inst_lit_sel_side                     none
% 2.25/0.97  --inst_solver_per_active                1400
% 2.25/0.97  --inst_solver_calls_frac                1.
% 2.25/0.97  --inst_passive_queue_type               priority_queues
% 2.25/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.25/0.97  --inst_passive_queues_freq              [25;2]
% 2.25/0.97  --inst_dismatching                      true
% 2.25/0.97  --inst_eager_unprocessed_to_passive     true
% 2.25/0.97  --inst_prop_sim_given                   true
% 2.25/0.97  --inst_prop_sim_new                     false
% 2.25/0.97  --inst_subs_new                         false
% 2.25/0.97  --inst_eq_res_simp                      false
% 2.25/0.97  --inst_subs_given                       false
% 2.25/0.97  --inst_orphan_elimination               true
% 2.25/0.97  --inst_learning_loop_flag               true
% 2.25/0.97  --inst_learning_start                   3000
% 2.25/0.97  --inst_learning_factor                  2
% 2.25/0.97  --inst_start_prop_sim_after_learn       3
% 2.25/0.97  --inst_sel_renew                        solver
% 2.25/0.97  --inst_lit_activity_flag                true
% 2.25/0.97  --inst_restr_to_given                   false
% 2.25/0.97  --inst_activity_threshold               500
% 2.25/0.97  --inst_out_proof                        true
% 2.25/0.97  
% 2.25/0.97  ------ Resolution Options
% 2.25/0.97  
% 2.25/0.97  --resolution_flag                       false
% 2.25/0.97  --res_lit_sel                           adaptive
% 2.25/0.97  --res_lit_sel_side                      none
% 2.25/0.97  --res_ordering                          kbo
% 2.25/0.97  --res_to_prop_solver                    active
% 2.25/0.97  --res_prop_simpl_new                    false
% 2.25/0.97  --res_prop_simpl_given                  true
% 2.25/0.97  --res_passive_queue_type                priority_queues
% 2.25/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.25/0.97  --res_passive_queues_freq               [15;5]
% 2.25/0.97  --res_forward_subs                      full
% 2.25/0.97  --res_backward_subs                     full
% 2.25/0.97  --res_forward_subs_resolution           true
% 2.25/0.97  --res_backward_subs_resolution          true
% 2.25/0.97  --res_orphan_elimination                true
% 2.25/0.97  --res_time_limit                        2.
% 2.25/0.97  --res_out_proof                         true
% 2.25/0.97  
% 2.25/0.97  ------ Superposition Options
% 2.25/0.97  
% 2.25/0.97  --superposition_flag                    true
% 2.25/0.97  --sup_passive_queue_type                priority_queues
% 2.25/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.25/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.25/0.97  --demod_completeness_check              fast
% 2.25/0.97  --demod_use_ground                      true
% 2.25/0.97  --sup_to_prop_solver                    passive
% 2.25/0.97  --sup_prop_simpl_new                    true
% 2.25/0.97  --sup_prop_simpl_given                  true
% 2.25/0.97  --sup_fun_splitting                     false
% 2.25/0.97  --sup_smt_interval                      50000
% 2.25/0.97  
% 2.25/0.97  ------ Superposition Simplification Setup
% 2.25/0.97  
% 2.25/0.97  --sup_indices_passive                   []
% 2.25/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.25/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.97  --sup_full_bw                           [BwDemod]
% 2.25/0.97  --sup_immed_triv                        [TrivRules]
% 2.25/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.25/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.97  --sup_immed_bw_main                     []
% 2.25/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.25/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.97  
% 2.25/0.97  ------ Combination Options
% 2.25/0.97  
% 2.25/0.97  --comb_res_mult                         3
% 2.25/0.97  --comb_sup_mult                         2
% 2.25/0.97  --comb_inst_mult                        10
% 2.25/0.97  
% 2.25/0.97  ------ Debug Options
% 2.25/0.97  
% 2.25/0.97  --dbg_backtrace                         false
% 2.25/0.97  --dbg_dump_prop_clauses                 false
% 2.25/0.97  --dbg_dump_prop_clauses_file            -
% 2.25/0.97  --dbg_out_stat                          false
% 2.25/0.97  
% 2.25/0.97  
% 2.25/0.97  
% 2.25/0.97  
% 2.25/0.97  ------ Proving...
% 2.25/0.97  
% 2.25/0.97  
% 2.25/0.97  % SZS status Theorem for theBenchmark.p
% 2.25/0.97  
% 2.25/0.97   Resolution empty clause
% 2.25/0.97  
% 2.25/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.25/0.97  
% 2.25/0.97  fof(f4,axiom,(
% 2.25/0.97    v1_xboole_0(k1_xboole_0)),
% 2.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.97  
% 2.25/0.97  fof(f49,plain,(
% 2.25/0.97    v1_xboole_0(k1_xboole_0)),
% 2.25/0.97    inference(cnf_transformation,[],[f4])).
% 2.25/0.97  
% 2.25/0.97  fof(f9,axiom,(
% 2.25/0.97    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.97  
% 2.25/0.97  fof(f20,plain,(
% 2.25/0.97    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.25/0.97    inference(ennf_transformation,[],[f9])).
% 2.25/0.97  
% 2.25/0.97  fof(f55,plain,(
% 2.25/0.97    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.25/0.97    inference(cnf_transformation,[],[f20])).
% 2.25/0.97  
% 2.25/0.97  fof(f3,axiom,(
% 2.25/0.97    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.97  
% 2.25/0.97  fof(f36,plain,(
% 2.25/0.97    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.25/0.97    inference(nnf_transformation,[],[f3])).
% 2.25/0.97  
% 2.25/0.97  fof(f47,plain,(
% 2.25/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.25/0.97    inference(cnf_transformation,[],[f36])).
% 2.25/0.97  
% 2.25/0.97  fof(f16,conjecture,(
% 2.25/0.97    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.97  
% 2.25/0.97  fof(f17,negated_conjecture,(
% 2.25/0.97    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.25/0.97    inference(negated_conjecture,[],[f16])).
% 2.25/0.97  
% 2.25/0.97  fof(f30,plain,(
% 2.25/0.97    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 2.25/0.97    inference(ennf_transformation,[],[f17])).
% 2.25/0.97  
% 2.25/0.97  fof(f31,plain,(
% 2.25/0.97    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 2.25/0.97    inference(flattening,[],[f30])).
% 2.25/0.97  
% 2.25/0.97  fof(f42,plain,(
% 2.25/0.97    ( ! [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK4))) )),
% 2.25/0.97    introduced(choice_axiom,[])).
% 2.25/0.97  
% 2.25/0.97  fof(f41,plain,(
% 2.25/0.97    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 2.25/0.97    introduced(choice_axiom,[])).
% 2.25/0.97  
% 2.25/0.97  fof(f43,plain,(
% 2.25/0.97    (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 2.25/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f42,f41])).
% 2.25/0.97  
% 2.25/0.97  fof(f69,plain,(
% 2.25/0.97    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))),
% 2.25/0.97    inference(cnf_transformation,[],[f43])).
% 2.25/0.97  
% 2.25/0.97  fof(f13,axiom,(
% 2.25/0.97    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 2.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.97  
% 2.25/0.97  fof(f60,plain,(
% 2.25/0.97    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 2.25/0.97    inference(cnf_transformation,[],[f13])).
% 2.25/0.97  
% 2.25/0.97  fof(f75,plain,(
% 2.25/0.97    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))),
% 2.25/0.97    inference(definition_unfolding,[],[f69,f60])).
% 2.25/0.97  
% 2.25/0.97  fof(f67,plain,(
% 2.25/0.97    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 2.25/0.97    inference(cnf_transformation,[],[f43])).
% 2.25/0.97  
% 2.25/0.97  fof(f77,plain,(
% 2.25/0.97    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 2.25/0.97    inference(definition_unfolding,[],[f67,f60])).
% 2.25/0.97  
% 2.25/0.97  fof(f68,plain,(
% 2.25/0.97    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 2.25/0.97    inference(cnf_transformation,[],[f43])).
% 2.25/0.97  
% 2.25/0.97  fof(f76,plain,(
% 2.25/0.97    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 2.25/0.97    inference(definition_unfolding,[],[f68,f60])).
% 2.25/0.97  
% 2.25/0.97  fof(f15,axiom,(
% 2.25/0.97    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 2.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.97  
% 2.25/0.97  fof(f28,plain,(
% 2.25/0.97    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.25/0.97    inference(ennf_transformation,[],[f15])).
% 2.25/0.97  
% 2.25/0.97  fof(f29,plain,(
% 2.25/0.97    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.25/0.97    inference(flattening,[],[f28])).
% 2.25/0.97  
% 2.25/0.97  fof(f62,plain,(
% 2.25/0.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.25/0.97    inference(cnf_transformation,[],[f29])).
% 2.25/0.97  
% 2.25/0.97  fof(f74,plain,(
% 2.25/0.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.25/0.97    inference(definition_unfolding,[],[f62,f60,f60,f60,f60])).
% 2.25/0.97  
% 2.25/0.97  fof(f66,plain,(
% 2.25/0.97    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))),
% 2.25/0.97    inference(cnf_transformation,[],[f43])).
% 2.25/0.97  
% 2.25/0.97  fof(f78,plain,(
% 2.25/0.97    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))),
% 2.25/0.97    inference(definition_unfolding,[],[f66,f60])).
% 2.25/0.97  
% 2.25/0.97  fof(f65,plain,(
% 2.25/0.97    ~v1_xboole_0(sK4)),
% 2.25/0.97    inference(cnf_transformation,[],[f43])).
% 2.25/0.97  
% 2.25/0.97  fof(f63,plain,(
% 2.25/0.97    ~v2_struct_0(sK3)),
% 2.25/0.97    inference(cnf_transformation,[],[f43])).
% 2.25/0.97  
% 2.25/0.97  fof(f64,plain,(
% 2.25/0.97    l1_struct_0(sK3)),
% 2.25/0.97    inference(cnf_transformation,[],[f43])).
% 2.25/0.97  
% 2.25/0.97  fof(f12,axiom,(
% 2.25/0.97    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.97  
% 2.25/0.97  fof(f24,plain,(
% 2.25/0.97    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.25/0.97    inference(ennf_transformation,[],[f12])).
% 2.25/0.97  
% 2.25/0.97  fof(f25,plain,(
% 2.25/0.97    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.25/0.97    inference(flattening,[],[f24])).
% 2.25/0.97  
% 2.25/0.97  fof(f59,plain,(
% 2.25/0.97    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.25/0.97    inference(cnf_transformation,[],[f25])).
% 2.25/0.97  
% 2.25/0.97  fof(f1,axiom,(
% 2.25/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.97  
% 2.25/0.97  fof(f44,plain,(
% 2.25/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.25/0.97    inference(cnf_transformation,[],[f1])).
% 2.25/0.97  
% 2.25/0.97  fof(f10,axiom,(
% 2.25/0.97    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.97  
% 2.25/0.97  fof(f21,plain,(
% 2.25/0.97    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.25/0.97    inference(ennf_transformation,[],[f10])).
% 2.25/0.97  
% 2.25/0.97  fof(f56,plain,(
% 2.25/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.25/0.97    inference(cnf_transformation,[],[f21])).
% 2.25/0.97  
% 2.25/0.97  fof(f6,axiom,(
% 2.25/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.97  
% 2.25/0.97  fof(f52,plain,(
% 2.25/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.25/0.97    inference(cnf_transformation,[],[f6])).
% 2.25/0.97  
% 2.25/0.97  fof(f72,plain,(
% 2.25/0.97    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.25/0.97    inference(definition_unfolding,[],[f56,f52])).
% 2.25/0.97  
% 2.25/0.97  fof(f14,axiom,(
% 2.25/0.97    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 2.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.97  
% 2.25/0.97  fof(f26,plain,(
% 2.25/0.97    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.25/0.97    inference(ennf_transformation,[],[f14])).
% 2.25/0.97  
% 2.25/0.97  fof(f27,plain,(
% 2.25/0.97    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.25/0.97    inference(flattening,[],[f26])).
% 2.25/0.97  
% 2.25/0.97  fof(f61,plain,(
% 2.25/0.97    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.25/0.97    inference(cnf_transformation,[],[f27])).
% 2.25/0.97  
% 2.25/0.97  fof(f73,plain,(
% 2.25/0.97    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.25/0.97    inference(definition_unfolding,[],[f61,f60,f60,f60,f60])).
% 2.25/0.97  
% 2.25/0.97  fof(f70,plain,(
% 2.25/0.97    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4),
% 2.25/0.97    inference(cnf_transformation,[],[f43])).
% 2.25/0.97  
% 2.25/0.97  fof(f8,axiom,(
% 2.25/0.97    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.97  
% 2.25/0.97  fof(f54,plain,(
% 2.25/0.97    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.25/0.97    inference(cnf_transformation,[],[f8])).
% 2.25/0.97  
% 2.25/0.97  fof(f7,axiom,(
% 2.25/0.97    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.25/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.97  
% 2.25/0.97  fof(f53,plain,(
% 2.25/0.97    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.25/0.97    inference(cnf_transformation,[],[f7])).
% 2.25/0.97  
% 2.25/0.97  fof(f71,plain,(
% 2.25/0.97    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.25/0.97    inference(definition_unfolding,[],[f53,f52])).
% 2.25/0.97  
% 2.25/0.97  cnf(c_5,plain,
% 2.25/0.97      ( v1_xboole_0(k1_xboole_0) ),
% 2.25/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_1425,plain,
% 2.25/0.97      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.25/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_10,plain,
% 2.25/0.97      ( r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 2.25/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_1421,plain,
% 2.25/0.97      ( r1_xboole_0(k1_tarski(X0),X1) = iProver_top
% 2.25/0.97      | r2_hidden(X0,X1) = iProver_top ),
% 2.25/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_4,plain,
% 2.25/0.97      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.25/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_1426,plain,
% 2.25/0.97      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 2.25/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_2237,plain,
% 2.25/0.97      ( k3_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
% 2.25/0.97      | r2_hidden(X0,X1) = iProver_top ),
% 2.25/0.97      inference(superposition,[status(thm)],[c_1421,c_1426]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_18,negated_conjecture,
% 2.25/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
% 2.25/0.97      inference(cnf_transformation,[],[f75]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_20,negated_conjecture,
% 2.25/0.97      ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.25/0.97      inference(cnf_transformation,[],[f77]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_19,negated_conjecture,
% 2.25/0.97      ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 2.25/0.97      inference(cnf_transformation,[],[f76]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_16,plain,
% 2.25/0.97      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.25/0.97      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.25/0.97      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.25/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.25/0.97      | ~ r2_hidden(X2,X0)
% 2.25/0.97      | ~ v1_xboole_0(X2)
% 2.25/0.97      | v1_xboole_0(X1)
% 2.25/0.97      | v1_xboole_0(X0) ),
% 2.25/0.97      inference(cnf_transformation,[],[f74]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_21,negated_conjecture,
% 2.25/0.97      ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
% 2.25/0.97      inference(cnf_transformation,[],[f78]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_317,plain,
% 2.25/0.97      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.25/0.97      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.25/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.25/0.97      | ~ r2_hidden(X2,X0)
% 2.25/0.97      | ~ v1_xboole_0(X2)
% 2.25/0.97      | v1_xboole_0(X0)
% 2.25/0.97      | v1_xboole_0(X1)
% 2.25/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.25/0.97      | sK4 != X0 ),
% 2.25/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_318,plain,
% 2.25/0.97      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.25/0.97      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.25/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.25/0.97      | ~ r2_hidden(X1,sK4)
% 2.25/0.97      | ~ v1_xboole_0(X1)
% 2.25/0.97      | v1_xboole_0(X0)
% 2.25/0.97      | v1_xboole_0(sK4)
% 2.25/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.25/0.97      inference(unflattening,[status(thm)],[c_317]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_22,negated_conjecture,
% 2.25/0.97      ( ~ v1_xboole_0(sK4) ),
% 2.25/0.97      inference(cnf_transformation,[],[f65]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_320,plain,
% 2.25/0.97      ( v1_xboole_0(X0)
% 2.25/0.97      | ~ v1_xboole_0(X1)
% 2.25/0.97      | ~ r2_hidden(X1,sK4)
% 2.25/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.25/0.97      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.25/0.97      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.25/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.25/0.97      inference(global_propositional_subsumption,[status(thm)],[c_318,c_22]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_321,plain,
% 2.25/0.97      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.25/0.97      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.25/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.25/0.97      | ~ r2_hidden(X1,sK4)
% 2.25/0.97      | ~ v1_xboole_0(X1)
% 2.25/0.97      | v1_xboole_0(X0)
% 2.25/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.25/0.97      inference(renaming,[status(thm)],[c_320]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_400,plain,
% 2.25/0.97      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 2.25/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.25/0.97      | ~ r2_hidden(X1,sK4)
% 2.25/0.97      | ~ v1_xboole_0(X1)
% 2.25/0.97      | v1_xboole_0(X0)
% 2.25/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.25/0.97      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.25/0.97      | sK4 != sK4 ),
% 2.25/0.97      inference(resolution_lifted,[status(thm)],[c_19,c_321]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_445,plain,
% 2.25/0.97      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.25/0.97      | ~ r2_hidden(X1,sK4)
% 2.25/0.97      | ~ v1_xboole_0(X1)
% 2.25/0.97      | v1_xboole_0(X0)
% 2.25/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.25/0.97      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.25/0.97      | sK4 != sK4 ),
% 2.25/0.97      inference(resolution_lifted,[status(thm)],[c_20,c_400]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_486,plain,
% 2.25/0.97      ( ~ r2_hidden(X0,sK4)
% 2.25/0.97      | ~ v1_xboole_0(X0)
% 2.25/0.97      | v1_xboole_0(X1)
% 2.25/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.25/0.97      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 2.25/0.97      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.25/0.97      | sK4 != sK4 ),
% 2.25/0.97      inference(resolution_lifted,[status(thm)],[c_18,c_445]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_685,plain,
% 2.25/0.97      ( ~ r2_hidden(X0,sK4)
% 2.25/0.97      | ~ v1_xboole_0(X0)
% 2.25/0.97      | v1_xboole_0(X1)
% 2.25/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.25/0.97      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 2.25/0.97      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
% 2.25/0.97      inference(equality_resolution_simp,[status(thm)],[c_486]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_958,plain,
% 2.25/0.97      ( ~ r2_hidden(X0,sK4) | ~ v1_xboole_0(X0) | ~ sP1_iProver_split ),
% 2.25/0.97      inference(splitting,
% 2.25/0.97                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.25/0.97                [c_685]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_1415,plain,
% 2.25/0.97      ( r2_hidden(X0,sK4) != iProver_top
% 2.25/0.97      | v1_xboole_0(X0) != iProver_top
% 2.25/0.97      | sP1_iProver_split != iProver_top ),
% 2.25/0.97      inference(predicate_to_equality,[status(thm)],[c_958]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_3258,plain,
% 2.25/0.97      ( k3_xboole_0(k1_tarski(X0),sK4) = k1_xboole_0
% 2.25/0.97      | v1_xboole_0(X0) != iProver_top
% 2.25/0.97      | sP1_iProver_split != iProver_top ),
% 2.25/0.97      inference(superposition,[status(thm)],[c_2237,c_1415]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_24,negated_conjecture,
% 2.25/0.97      ( ~ v2_struct_0(sK3) ),
% 2.25/0.97      inference(cnf_transformation,[],[f63]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_25,plain,
% 2.25/0.97      ( v2_struct_0(sK3) != iProver_top ),
% 2.25/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_23,negated_conjecture,
% 2.25/0.97      ( l1_struct_0(sK3) ),
% 2.25/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_26,plain,
% 2.25/0.97      ( l1_struct_0(sK3) = iProver_top ),
% 2.25/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_14,plain,
% 2.25/0.97      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.25/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_36,plain,
% 2.25/0.97      ( v2_struct_0(X0) = iProver_top
% 2.25/0.97      | l1_struct_0(X0) != iProver_top
% 2.25/0.97      | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
% 2.25/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_38,plain,
% 2.25/0.97      ( v2_struct_0(sK3) = iProver_top
% 2.25/0.97      | l1_struct_0(sK3) != iProver_top
% 2.25/0.97      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 2.25/0.97      inference(instantiation,[status(thm)],[c_36]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_959,plain,
% 2.25/0.97      ( sP1_iProver_split | sP0_iProver_split ),
% 2.25/0.97      inference(splitting,
% 2.25/0.97                [splitting(split),new_symbols(definition,[])],
% 2.25/0.97                [c_685]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_992,plain,
% 2.25/0.97      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 2.25/0.97      inference(predicate_to_equality,[status(thm)],[c_959]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_974,plain,
% 2.25/0.97      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 2.25/0.97      theory(equality) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_1607,plain,
% 2.25/0.97      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) = u1_struct_0(X0)
% 2.25/0.97      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != X0 ),
% 2.25/0.97      inference(instantiation,[status(thm)],[c_974]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_1720,plain,
% 2.25/0.97      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) = u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.25/0.97      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3))) ),
% 2.25/0.97      inference(instantiation,[status(thm)],[c_1607]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_961,plain,( X0 = X0 ),theory(equality) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_1721,plain,
% 2.25/0.97      ( k3_lattice3(k1_lattice3(k2_struct_0(sK3))) = k3_lattice3(k1_lattice3(k2_struct_0(sK3))) ),
% 2.25/0.97      inference(instantiation,[status(thm)],[c_961]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_957,plain,
% 2.25/0.97      ( v1_xboole_0(X0)
% 2.25/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.25/0.97      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.25/0.97      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 2.25/0.97      | ~ sP0_iProver_split ),
% 2.25/0.97      inference(splitting,
% 2.25/0.97                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.25/0.97                [c_685]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_1416,plain,
% 2.25/0.97      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.25/0.97      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 2.25/0.97      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 2.25/0.97      | v1_xboole_0(X0) = iProver_top
% 2.25/0.97      | sP0_iProver_split != iProver_top ),
% 2.25/0.97      inference(predicate_to_equality,[status(thm)],[c_957]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_1809,plain,
% 2.25/0.97      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.25/0.97      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 2.25/0.97      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top
% 2.25/0.97      | sP0_iProver_split != iProver_top ),
% 2.25/0.97      inference(equality_resolution,[status(thm)],[c_1416]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_3291,plain,
% 2.25/0.97      ( v1_xboole_0(X0) != iProver_top
% 2.25/0.97      | k3_xboole_0(k1_tarski(X0),sK4) = k1_xboole_0 ),
% 2.25/0.97      inference(global_propositional_subsumption,
% 2.25/0.97                [status(thm)],
% 2.25/0.97                [c_3258,c_25,c_26,c_38,c_992,c_1720,c_1721,c_1809]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_3292,plain,
% 2.25/0.97      ( k3_xboole_0(k1_tarski(X0),sK4) = k1_xboole_0
% 2.25/0.97      | v1_xboole_0(X0) != iProver_top ),
% 2.25/0.97      inference(renaming,[status(thm)],[c_3291]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_3299,plain,
% 2.25/0.97      ( k3_xboole_0(k1_tarski(k1_xboole_0),sK4) = k1_xboole_0 ),
% 2.25/0.97      inference(superposition,[status(thm)],[c_1425,c_3292]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_0,plain,
% 2.25/0.97      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.25/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_3497,plain,
% 2.25/0.97      ( k3_xboole_0(sK4,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
% 2.25/0.97      inference(superposition,[status(thm)],[c_3299,c_0]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_11,plain,
% 2.25/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.25/0.97      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 2.25/0.97      inference(cnf_transformation,[],[f72]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_477,plain,
% 2.25/0.97      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 2.25/0.97      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X2)
% 2.25/0.97      | sK4 != X0 ),
% 2.25/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_478,plain,
% 2.25/0.97      ( k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) = k7_subset_1(X1,sK4,X0)
% 2.25/0.97      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X1) ),
% 2.25/0.97      inference(unflattening,[status(thm)],[c_477]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_1575,plain,
% 2.25/0.97      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,X0) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
% 2.25/0.97      inference(equality_resolution,[status(thm)],[c_478]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_15,plain,
% 2.25/0.97      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.25/0.97      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.25/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.25/0.97      | v2_struct_0(X1)
% 2.25/0.97      | ~ l1_struct_0(X1)
% 2.25/0.97      | v1_xboole_0(X0)
% 2.25/0.97      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
% 2.25/0.97      inference(cnf_transformation,[],[f73]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_365,plain,
% 2.25/0.97      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.25/0.97      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.25/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.25/0.97      | v2_struct_0(X1)
% 2.25/0.97      | v1_xboole_0(X0)
% 2.25/0.97      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
% 2.25/0.97      | sK3 != X1 ),
% 2.25/0.97      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_366,plain,
% 2.25/0.97      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.25/0.97      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.25/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.25/0.97      | v2_struct_0(sK3)
% 2.25/0.97      | v1_xboole_0(X0)
% 2.25/0.97      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 2.25/0.97      inference(unflattening,[status(thm)],[c_365]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_370,plain,
% 2.25/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.25/0.97      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.25/0.97      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.25/0.97      | v1_xboole_0(X0)
% 2.25/0.97      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 2.25/0.97      inference(global_propositional_subsumption,[status(thm)],[c_366,c_24]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_371,plain,
% 2.25/0.97      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.25/0.97      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.25/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.25/0.97      | v1_xboole_0(X0)
% 2.25/0.97      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 2.25/0.97      inference(renaming,[status(thm)],[c_370]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_427,plain,
% 2.25/0.97      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.25/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.25/0.97      | v1_xboole_0(X0)
% 2.25/0.97      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
% 2.25/0.97      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 2.25/0.97      | sK4 != X0 ),
% 2.25/0.97      inference(resolution_lifted,[status(thm)],[c_19,c_371]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_428,plain,
% 2.25/0.97      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 2.25/0.97      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 2.25/0.97      | v1_xboole_0(sK4)
% 2.25/0.97      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.25/0.97      inference(unflattening,[status(thm)],[c_427]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_430,plain,
% 2.25/0.97      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 2.25/0.97      inference(global_propositional_subsumption,
% 2.25/0.97                [status(thm)],
% 2.25/0.97                [c_428,c_22,c_20,c_18]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_1594,plain,
% 2.25/0.97      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) ),
% 2.25/0.97      inference(demodulation,[status(thm)],[c_1575,c_430]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_17,negated_conjecture,
% 2.25/0.97      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
% 2.25/0.97      inference(cnf_transformation,[],[f70]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_1602,plain,
% 2.25/0.97      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) != sK4 ),
% 2.25/0.97      inference(demodulation,[status(thm)],[c_1594,c_17]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_3515,plain,
% 2.25/0.97      ( k5_xboole_0(sK4,k1_xboole_0) != sK4 ),
% 2.25/0.97      inference(demodulation,[status(thm)],[c_3497,c_1602]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_9,plain,
% 2.25/0.97      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.25/0.97      inference(cnf_transformation,[],[f54]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_1422,plain,
% 2.25/0.97      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 2.25/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_1956,plain,
% 2.25/0.97      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.25/0.97      inference(superposition,[status(thm)],[c_1422,c_1426]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_8,plain,
% 2.25/0.97      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 2.25/0.97      inference(cnf_transformation,[],[f71]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_2010,plain,
% 2.25/0.97      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.25/0.97      inference(demodulation,[status(thm)],[c_1956,c_8]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_3521,plain,
% 2.25/0.97      ( sK4 != sK4 ),
% 2.25/0.97      inference(demodulation,[status(thm)],[c_3515,c_2010]) ).
% 2.25/0.97  
% 2.25/0.97  cnf(c_3522,plain,
% 2.25/0.97      ( $false ),
% 2.25/0.97      inference(equality_resolution_simp,[status(thm)],[c_3521]) ).
% 2.25/0.97  
% 2.25/0.97  
% 2.25/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.25/0.97  
% 2.25/0.97  ------                               Statistics
% 2.25/0.97  
% 2.25/0.97  ------ General
% 2.25/0.97  
% 2.25/0.97  abstr_ref_over_cycles:                  0
% 2.25/0.97  abstr_ref_under_cycles:                 0
% 2.25/0.97  gc_basic_clause_elim:                   0
% 2.25/0.97  forced_gc_time:                         0
% 2.25/0.97  parsing_time:                           0.009
% 2.25/0.97  unif_index_cands_time:                  0.
% 2.25/0.97  unif_index_add_time:                    0.
% 2.25/0.97  orderings_time:                         0.
% 2.25/0.97  out_proof_time:                         0.011
% 2.25/0.97  total_time:                             0.157
% 2.25/0.97  num_of_symbols:                         59
% 2.25/0.97  num_of_terms:                           3019
% 2.25/0.97  
% 2.25/0.97  ------ Preprocessing
% 2.25/0.97  
% 2.25/0.97  num_of_splits:                          2
% 2.25/0.97  num_of_split_atoms:                     2
% 2.25/0.97  num_of_reused_defs:                     0
% 2.25/0.97  num_eq_ax_congr_red:                    15
% 2.25/0.97  num_of_sem_filtered_clauses:            1
% 2.25/0.97  num_of_subtypes:                        0
% 2.25/0.97  monotx_restored_types:                  0
% 2.25/0.97  sat_num_of_epr_types:                   0
% 2.25/0.97  sat_num_of_non_cyclic_types:            0
% 2.25/0.97  sat_guarded_non_collapsed_types:        0
% 2.25/0.97  num_pure_diseq_elim:                    0
% 2.25/0.97  simp_replaced_by:                       0
% 2.25/0.97  res_preprocessed:                       119
% 2.25/0.97  prep_upred:                             0
% 2.25/0.97  prep_unflattend:                        21
% 2.25/0.97  smt_new_axioms:                         0
% 2.25/0.97  pred_elim_cands:                        3
% 2.25/0.97  pred_elim:                              6
% 2.25/0.97  pred_elim_cl:                           6
% 2.25/0.97  pred_elim_cycles:                       8
% 2.25/0.97  merged_defs:                            8
% 2.25/0.97  merged_defs_ncl:                        0
% 2.25/0.97  bin_hyper_res:                          8
% 2.25/0.97  prep_cycles:                            4
% 2.25/0.97  pred_elim_time:                         0.023
% 2.25/0.97  splitting_time:                         0.
% 2.25/0.97  sem_filter_time:                        0.
% 2.25/0.97  monotx_time:                            0.001
% 2.25/0.97  subtype_inf_time:                       0.
% 2.25/0.97  
% 2.25/0.97  ------ Problem properties
% 2.25/0.97  
% 2.25/0.97  clauses:                                21
% 2.25/0.97  conjectures:                            2
% 2.25/0.97  epr:                                    6
% 2.25/0.97  horn:                                   15
% 2.25/0.97  ground:                                 6
% 2.25/0.97  unary:                                  8
% 2.25/0.97  binary:                                 10
% 2.25/0.97  lits:                                   43
% 2.25/0.97  lits_eq:                                13
% 2.25/0.97  fd_pure:                                0
% 2.25/0.97  fd_pseudo:                              0
% 2.25/0.97  fd_cond:                                2
% 2.25/0.97  fd_pseudo_cond:                         0
% 2.25/0.97  ac_symbols:                             0
% 2.25/0.97  
% 2.25/0.97  ------ Propositional Solver
% 2.25/0.97  
% 2.25/0.97  prop_solver_calls:                      28
% 2.25/0.97  prop_fast_solver_calls:                 750
% 2.25/0.97  smt_solver_calls:                       0
% 2.25/0.97  smt_fast_solver_calls:                  0
% 2.25/0.97  prop_num_of_clauses:                    1080
% 2.25/0.97  prop_preprocess_simplified:             4089
% 2.25/0.97  prop_fo_subsumed:                       14
% 2.25/0.97  prop_solver_time:                       0.
% 2.25/0.97  smt_solver_time:                        0.
% 2.25/0.97  smt_fast_solver_time:                   0.
% 2.25/0.97  prop_fast_solver_time:                  0.
% 2.25/0.97  prop_unsat_core_time:                   0.
% 2.25/0.97  
% 2.25/0.97  ------ QBF
% 2.25/0.97  
% 2.25/0.97  qbf_q_res:                              0
% 2.25/0.97  qbf_num_tautologies:                    0
% 2.25/0.97  qbf_prep_cycles:                        0
% 2.25/0.97  
% 2.25/0.97  ------ BMC1
% 2.25/0.97  
% 2.25/0.97  bmc1_current_bound:                     -1
% 2.25/0.97  bmc1_last_solved_bound:                 -1
% 2.25/0.97  bmc1_unsat_core_size:                   -1
% 2.25/0.97  bmc1_unsat_core_parents_size:           -1
% 2.25/0.97  bmc1_merge_next_fun:                    0
% 2.25/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.25/0.97  
% 2.25/0.97  ------ Instantiation
% 2.25/0.97  
% 2.25/0.97  inst_num_of_clauses:                    378
% 2.25/0.97  inst_num_in_passive:                    104
% 2.25/0.97  inst_num_in_active:                     208
% 2.25/0.97  inst_num_in_unprocessed:                66
% 2.25/0.97  inst_num_of_loops:                      240
% 2.25/0.97  inst_num_of_learning_restarts:          0
% 2.25/0.97  inst_num_moves_active_passive:          28
% 2.25/0.97  inst_lit_activity:                      0
% 2.25/0.97  inst_lit_activity_moves:                0
% 2.25/0.97  inst_num_tautologies:                   0
% 2.25/0.97  inst_num_prop_implied:                  0
% 2.25/0.97  inst_num_existing_simplified:           0
% 2.25/0.97  inst_num_eq_res_simplified:             0
% 2.25/0.97  inst_num_child_elim:                    0
% 2.25/0.97  inst_num_of_dismatching_blockings:      86
% 2.25/0.97  inst_num_of_non_proper_insts:           333
% 2.25/0.97  inst_num_of_duplicates:                 0
% 2.25/0.97  inst_inst_num_from_inst_to_res:         0
% 2.25/0.97  inst_dismatching_checking_time:         0.
% 2.25/0.97  
% 2.25/0.97  ------ Resolution
% 2.25/0.97  
% 2.25/0.97  res_num_of_clauses:                     0
% 2.25/0.97  res_num_in_passive:                     0
% 2.25/0.97  res_num_in_active:                      0
% 2.25/0.97  res_num_of_loops:                       123
% 2.25/0.97  res_forward_subset_subsumed:            63
% 2.25/0.97  res_backward_subset_subsumed:           4
% 2.25/0.97  res_forward_subsumed:                   0
% 2.25/0.97  res_backward_subsumed:                  0
% 2.25/0.97  res_forward_subsumption_resolution:     0
% 2.25/0.97  res_backward_subsumption_resolution:    0
% 2.25/0.97  res_clause_to_clause_subsumption:       186
% 2.25/0.97  res_orphan_elimination:                 0
% 2.25/0.97  res_tautology_del:                      63
% 2.25/0.97  res_num_eq_res_simplified:              1
% 2.25/0.97  res_num_sel_changes:                    0
% 2.25/0.97  res_moves_from_active_to_pass:          0
% 2.25/0.97  
% 2.25/0.97  ------ Superposition
% 2.25/0.97  
% 2.25/0.97  sup_time_total:                         0.
% 2.25/0.97  sup_time_generating:                    0.
% 2.25/0.97  sup_time_sim_full:                      0.
% 2.25/0.97  sup_time_sim_immed:                     0.
% 2.25/0.97  
% 2.25/0.97  sup_num_of_clauses:                     55
% 2.25/0.97  sup_num_in_active:                      41
% 2.25/0.97  sup_num_in_passive:                     14
% 2.25/0.97  sup_num_of_loops:                       47
% 2.25/0.97  sup_fw_superposition:                   78
% 2.25/0.97  sup_bw_superposition:                   35
% 2.25/0.97  sup_immediate_simplified:               15
% 2.25/0.97  sup_given_eliminated:                   0
% 2.25/0.97  comparisons_done:                       0
% 2.25/0.97  comparisons_avoided:                    0
% 2.25/0.97  
% 2.25/0.97  ------ Simplifications
% 2.25/0.97  
% 2.25/0.97  
% 2.25/0.97  sim_fw_subset_subsumed:                 12
% 2.25/0.97  sim_bw_subset_subsumed:                 2
% 2.25/0.97  sim_fw_subsumed:                        2
% 2.25/0.97  sim_bw_subsumed:                        0
% 2.25/0.97  sim_fw_subsumption_res:                 0
% 2.25/0.97  sim_bw_subsumption_res:                 0
% 2.25/0.97  sim_tautology_del:                      5
% 2.25/0.97  sim_eq_tautology_del:                   1
% 2.25/0.97  sim_eq_res_simp:                        1
% 2.25/0.97  sim_fw_demodulated:                     2
% 2.25/0.97  sim_bw_demodulated:                     6
% 2.25/0.97  sim_light_normalised:                   0
% 2.25/0.97  sim_joinable_taut:                      0
% 2.25/0.97  sim_joinable_simp:                      0
% 2.25/0.97  sim_ac_normalised:                      0
% 2.25/0.97  sim_smt_subsumption:                    0
% 2.25/0.97  
%------------------------------------------------------------------------------
