%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:11 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 656 expanded)
%              Number of clauses        :   84 ( 162 expanded)
%              Number of leaves         :   24 ( 185 expanded)
%              Depth                    :   24
%              Number of atoms          :  504 (3381 expanded)
%              Number of equality atoms :  142 ( 630 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( r1_xboole_0(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( r1_xboole_0(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f39])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f37])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f51,f50])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f34,f42,f41])).

fof(f68,plain,(
    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f76,plain,(
    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f68,f60])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f63,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f67,f60])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
    inference(definition_unfolding,[],[f69,f60])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f50])).

fof(f70,plain,(
    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f43])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(cnf_transformation,[],[f32])).

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

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1431,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_12,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1427,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1433,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1901,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1427,c_1433])).

cnf(c_2477,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1431,c_1901])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2576,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_2477,c_6])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1435,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1429,plain,
    ( X0 = X1
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1430,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(k1_tarski(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1725,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1429,c_1430])).

cnf(c_2178,plain,
    ( sK0(X0,k1_tarski(X1)) = X1
    | r1_xboole_0(X0,k1_tarski(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1435,c_1725])).

cnf(c_3142,plain,
    ( k3_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0
    | sK0(X0,k1_tarski(X1)) = X1 ),
    inference(superposition,[status(thm)],[c_2178,c_1901])).

cnf(c_19,negated_conjecture,
    ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_15,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_317,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_318,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | ~ l1_struct_0(sK3)
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_322,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_318,c_23])).

cnf(c_323,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
    inference(renaming,[status(thm)],[c_322])).

cnf(c_385,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v1_xboole_0(X0)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_323])).

cnf(c_386,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
    | v1_xboole_0(sK4)
    | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_20,negated_conjecture,
    ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_388,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_22,c_20,c_18])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_435,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X2)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_436,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) = k7_subset_1(X1,sK4,X0)
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_1666,plain,
    ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,X0) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
    inference(equality_resolution,[status(thm)],[c_436])).

cnf(c_2631,plain,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_388,c_1666])).

cnf(c_17,negated_conjecture,
    ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3550,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) != sK4 ),
    inference(superposition,[status(thm)],[c_2631,c_17])).

cnf(c_8483,plain,
    ( k5_xboole_0(sK4,k1_xboole_0) != sK4
    | sK0(sK4,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3142,c_3550])).

cnf(c_8489,plain,
    ( sK0(sK4,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2576,c_8483])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1434,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8636,plain,
    ( r2_hidden(k1_xboole_0,sK4) = iProver_top
    | r1_xboole_0(sK4,k1_tarski(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8489,c_1434])).

cnf(c_25,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_26,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_36,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_38,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_40,plain,
    ( ~ l1_struct_0(sK3)
    | u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_74,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_16,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_21,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_269,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_270,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_272,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_270,c_22])).

cnf(c_273,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_272])).

cnf(c_358,plain,
    ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_273])).

cnf(c_403,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ r2_hidden(X1,sK4)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_358])).

cnf(c_444,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_403])).

cnf(c_756,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
    inference(equality_resolution_simp,[status(thm)],[c_444])).

cnf(c_1084,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_756])).

cnf(c_1118,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1084])).

cnf(c_1083,plain,
    ( ~ r2_hidden(X0,sK4)
    | ~ v1_xboole_0(X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_756])).

cnf(c_1483,plain,
    ( ~ r2_hidden(k1_xboole_0,sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_1083])).

cnf(c_1484,plain,
    ( r2_hidden(k1_xboole_0,sK4) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1483])).

cnf(c_1082,plain,
    ( v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_756])).

cnf(c_1097,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1527,plain,
    ( v1_xboole_0(X0)
    | ~ sP0_iProver_split
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
    | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1082,c_1097])).

cnf(c_1086,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1587,plain,
    ( v1_xboole_0(k2_struct_0(sK3))
    | ~ sP0_iProver_split
    | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3))) ),
    inference(resolution,[status(thm)],[c_1527,c_1086])).

cnf(c_1588,plain,
    ( v1_xboole_0(k2_struct_0(sK3))
    | ~ sP0_iProver_split ),
    inference(equality_resolution_simp,[status(thm)],[c_1587])).

cnf(c_1589,plain,
    ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1588])).

cnf(c_1088,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1661,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_1088])).

cnf(c_1755,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(k2_struct_0(sK3))
    | u1_struct_0(sK3) != k2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1661])).

cnf(c_1756,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1755])).

cnf(c_8648,plain,
    ( r1_xboole_0(sK4,k1_tarski(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8636,c_25,c_23,c_26,c_38,c_40,c_74,c_1118,c_1484,c_1589,c_1756])).

cnf(c_8653,plain,
    ( k3_xboole_0(sK4,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8648,c_1901])).

cnf(c_10472,plain,
    ( k5_xboole_0(sK4,k1_xboole_0) != sK4 ),
    inference(superposition,[status(thm)],[c_8653,c_3550])).

cnf(c_10473,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2576,c_10472])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:08:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.72/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.00  
% 3.72/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.72/1.00  
% 3.72/1.00  ------  iProver source info
% 3.72/1.00  
% 3.72/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.72/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.72/1.00  git: non_committed_changes: false
% 3.72/1.00  git: last_make_outside_of_git: false
% 3.72/1.00  
% 3.72/1.00  ------ 
% 3.72/1.00  ------ Parsing...
% 3.72/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.72/1.00  
% 3.72/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.72/1.00  
% 3.72/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.72/1.00  
% 3.72/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.72/1.00  ------ Proving...
% 3.72/1.00  ------ Problem Properties 
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  clauses                                 21
% 3.72/1.00  conjectures                             2
% 3.72/1.00  EPR                                     6
% 3.72/1.00  Horn                                    14
% 3.72/1.00  unary                                   8
% 3.72/1.00  binary                                  10
% 3.72/1.00  lits                                    39
% 3.72/1.00  lits eq                                 12
% 3.72/1.00  fd_pure                                 0
% 3.72/1.00  fd_pseudo                               0
% 3.72/1.00  fd_cond                                 2
% 3.72/1.00  fd_pseudo_cond                          1
% 3.72/1.00  AC symbols                              0
% 3.72/1.00  
% 3.72/1.00  ------ Input Options Time Limit: Unbounded
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  ------ 
% 3.72/1.00  Current options:
% 3.72/1.00  ------ 
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  ------ Proving...
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  % SZS status Theorem for theBenchmark.p
% 3.72/1.00  
% 3.72/1.00   Resolution empty clause
% 3.72/1.00  
% 3.72/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.72/1.00  
% 3.72/1.00  fof(f6,axiom,(
% 3.72/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f52,plain,(
% 3.72/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f6])).
% 3.72/1.00  
% 3.72/1.00  fof(f10,axiom,(
% 3.72/1.00    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f25,plain,(
% 3.72/1.00    ! [X0] : (? [X1] : (r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.72/1.00    inference(ennf_transformation,[],[f10])).
% 3.72/1.00  
% 3.72/1.00  fof(f39,plain,(
% 3.72/1.00    ! [X0] : (? [X1] : (r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) => (r1_xboole_0(sK2(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 3.72/1.00    introduced(choice_axiom,[])).
% 3.72/1.00  
% 3.72/1.00  fof(f40,plain,(
% 3.72/1.00    ! [X0] : ((r1_xboole_0(sK2(X0),X0) & r2_hidden(sK2(X0),X0)) | k1_xboole_0 = X0)),
% 3.72/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f39])).
% 3.72/1.00  
% 3.72/1.00  fof(f56,plain,(
% 3.72/1.00    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.72/1.00    inference(cnf_transformation,[],[f40])).
% 3.72/1.00  
% 3.72/1.00  fof(f3,axiom,(
% 3.72/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f19,plain,(
% 3.72/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.72/1.00    inference(rectify,[],[f3])).
% 3.72/1.00  
% 3.72/1.00  fof(f21,plain,(
% 3.72/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.72/1.00    inference(ennf_transformation,[],[f19])).
% 3.72/1.00  
% 3.72/1.00  fof(f37,plain,(
% 3.72/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.72/1.00    introduced(choice_axiom,[])).
% 3.72/1.00  
% 3.72/1.00  fof(f38,plain,(
% 3.72/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.72/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f37])).
% 3.72/1.00  
% 3.72/1.00  fof(f49,plain,(
% 3.72/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.72/1.00    inference(cnf_transformation,[],[f38])).
% 3.72/1.00  
% 3.72/1.00  fof(f5,axiom,(
% 3.72/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f51,plain,(
% 3.72/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.72/1.00    inference(cnf_transformation,[],[f5])).
% 3.72/1.00  
% 3.72/1.00  fof(f4,axiom,(
% 3.72/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f50,plain,(
% 3.72/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.72/1.00    inference(cnf_transformation,[],[f4])).
% 3.72/1.00  
% 3.72/1.00  fof(f71,plain,(
% 3.72/1.00    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 3.72/1.00    inference(definition_unfolding,[],[f51,f50])).
% 3.72/1.00  
% 3.72/1.00  fof(f2,axiom,(
% 3.72/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f18,plain,(
% 3.72/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.72/1.00    inference(rectify,[],[f2])).
% 3.72/1.00  
% 3.72/1.00  fof(f20,plain,(
% 3.72/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.72/1.00    inference(ennf_transformation,[],[f18])).
% 3.72/1.00  
% 3.72/1.00  fof(f35,plain,(
% 3.72/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.72/1.00    introduced(choice_axiom,[])).
% 3.72/1.00  
% 3.72/1.00  fof(f36,plain,(
% 3.72/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.72/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f35])).
% 3.72/1.00  
% 3.72/1.00  fof(f46,plain,(
% 3.72/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f36])).
% 3.72/1.00  
% 3.72/1.00  fof(f8,axiom,(
% 3.72/1.00    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f23,plain,(
% 3.72/1.00    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 3.72/1.00    inference(ennf_transformation,[],[f8])).
% 3.72/1.00  
% 3.72/1.00  fof(f54,plain,(
% 3.72/1.00    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 3.72/1.00    inference(cnf_transformation,[],[f23])).
% 3.72/1.00  
% 3.72/1.00  fof(f7,axiom,(
% 3.72/1.00    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f22,plain,(
% 3.72/1.00    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 3.72/1.00    inference(ennf_transformation,[],[f7])).
% 3.72/1.00  
% 3.72/1.00  fof(f53,plain,(
% 3.72/1.00    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f22])).
% 3.72/1.00  
% 3.72/1.00  fof(f16,conjecture,(
% 3.72/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f17,negated_conjecture,(
% 3.72/1.00    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 3.72/1.00    inference(negated_conjecture,[],[f16])).
% 3.72/1.00  
% 3.72/1.00  fof(f33,plain,(
% 3.72/1.00    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 3.72/1.00    inference(ennf_transformation,[],[f17])).
% 3.72/1.00  
% 3.72/1.00  fof(f34,plain,(
% 3.72/1.00    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 3.72/1.00    inference(flattening,[],[f33])).
% 3.72/1.00  
% 3.72/1.00  fof(f42,plain,(
% 3.72/1.00    ( ! [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK4))) )),
% 3.72/1.00    introduced(choice_axiom,[])).
% 3.72/1.00  
% 3.72/1.00  fof(f41,plain,(
% 3.72/1.00    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))),
% 3.72/1.00    introduced(choice_axiom,[])).
% 3.72/1.00  
% 3.72/1.00  fof(f43,plain,(
% 3.72/1.00    (k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))) & v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3))) & v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))) & ~v1_xboole_0(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)),
% 3.72/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f34,f42,f41])).
% 3.72/1.00  
% 3.72/1.00  fof(f68,plain,(
% 3.72/1.00    v13_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 3.72/1.00    inference(cnf_transformation,[],[f43])).
% 3.72/1.00  
% 3.72/1.00  fof(f13,axiom,(
% 3.72/1.00    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f60,plain,(
% 3.72/1.00    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 3.72/1.00    inference(cnf_transformation,[],[f13])).
% 3.72/1.00  
% 3.72/1.00  fof(f76,plain,(
% 3.72/1.00    v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 3.72/1.00    inference(definition_unfolding,[],[f68,f60])).
% 3.72/1.00  
% 3.72/1.00  fof(f14,axiom,(
% 3.72/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f29,plain,(
% 3.72/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.72/1.00    inference(ennf_transformation,[],[f14])).
% 3.72/1.00  
% 3.72/1.00  fof(f30,plain,(
% 3.72/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.72/1.00    inference(flattening,[],[f29])).
% 3.72/1.00  
% 3.72/1.00  fof(f61,plain,(
% 3.72/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f30])).
% 3.72/1.00  
% 3.72/1.00  fof(f73,plain,(
% 3.72/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.72/1.00    inference(definition_unfolding,[],[f61,f60,f60,f60,f60])).
% 3.72/1.00  
% 3.72/1.00  fof(f63,plain,(
% 3.72/1.00    ~v2_struct_0(sK3)),
% 3.72/1.00    inference(cnf_transformation,[],[f43])).
% 3.72/1.00  
% 3.72/1.00  fof(f64,plain,(
% 3.72/1.00    l1_struct_0(sK3)),
% 3.72/1.00    inference(cnf_transformation,[],[f43])).
% 3.72/1.00  
% 3.72/1.00  fof(f65,plain,(
% 3.72/1.00    ~v1_xboole_0(sK4)),
% 3.72/1.00    inference(cnf_transformation,[],[f43])).
% 3.72/1.00  
% 3.72/1.00  fof(f67,plain,(
% 3.72/1.00    v2_waybel_0(sK4,k3_yellow_1(k2_struct_0(sK3)))),
% 3.72/1.00    inference(cnf_transformation,[],[f43])).
% 3.72/1.00  
% 3.72/1.00  fof(f77,plain,(
% 3.72/1.00    v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))),
% 3.72/1.00    inference(definition_unfolding,[],[f67,f60])).
% 3.72/1.00  
% 3.72/1.00  fof(f69,plain,(
% 3.72/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK3)))))),
% 3.72/1.00    inference(cnf_transformation,[],[f43])).
% 3.72/1.00  
% 3.72/1.00  fof(f75,plain,(
% 3.72/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))),
% 3.72/1.00    inference(definition_unfolding,[],[f69,f60])).
% 3.72/1.00  
% 3.72/1.00  fof(f9,axiom,(
% 3.72/1.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f24,plain,(
% 3.72/1.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.72/1.00    inference(ennf_transformation,[],[f9])).
% 3.72/1.00  
% 3.72/1.00  fof(f55,plain,(
% 3.72/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.72/1.00    inference(cnf_transformation,[],[f24])).
% 3.72/1.00  
% 3.72/1.00  fof(f72,plain,(
% 3.72/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.72/1.00    inference(definition_unfolding,[],[f55,f50])).
% 3.72/1.00  
% 3.72/1.00  fof(f70,plain,(
% 3.72/1.00    k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4),
% 3.72/1.00    inference(cnf_transformation,[],[f43])).
% 3.72/1.00  
% 3.72/1.00  fof(f45,plain,(
% 3.72/1.00    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f36])).
% 3.72/1.00  
% 3.72/1.00  fof(f12,axiom,(
% 3.72/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f27,plain,(
% 3.72/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.72/1.00    inference(ennf_transformation,[],[f12])).
% 3.72/1.00  
% 3.72/1.00  fof(f28,plain,(
% 3.72/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.72/1.00    inference(flattening,[],[f27])).
% 3.72/1.00  
% 3.72/1.00  fof(f59,plain,(
% 3.72/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f28])).
% 3.72/1.00  
% 3.72/1.00  fof(f11,axiom,(
% 3.72/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f26,plain,(
% 3.72/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.72/1.00    inference(ennf_transformation,[],[f11])).
% 3.72/1.00  
% 3.72/1.00  fof(f58,plain,(
% 3.72/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f26])).
% 3.72/1.00  
% 3.72/1.00  fof(f1,axiom,(
% 3.72/1.00    v1_xboole_0(k1_xboole_0)),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f44,plain,(
% 3.72/1.00    v1_xboole_0(k1_xboole_0)),
% 3.72/1.00    inference(cnf_transformation,[],[f1])).
% 3.72/1.00  
% 3.72/1.00  fof(f15,axiom,(
% 3.72/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 3.72/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.72/1.00  
% 3.72/1.00  fof(f31,plain,(
% 3.72/1.00    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.72/1.00    inference(ennf_transformation,[],[f15])).
% 3.72/1.00  
% 3.72/1.00  fof(f32,plain,(
% 3.72/1.00    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.72/1.00    inference(flattening,[],[f31])).
% 3.72/1.00  
% 3.72/1.00  fof(f62,plain,(
% 3.72/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.72/1.00    inference(cnf_transformation,[],[f32])).
% 3.72/1.00  
% 3.72/1.00  fof(f74,plain,(
% 3.72/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.72/1.00    inference(definition_unfolding,[],[f62,f60,f60,f60,f60])).
% 3.72/1.00  
% 3.72/1.00  fof(f66,plain,(
% 3.72/1.00    v1_subset_1(sK4,u1_struct_0(k3_yellow_1(k2_struct_0(sK3))))),
% 3.72/1.00    inference(cnf_transformation,[],[f43])).
% 3.72/1.00  
% 3.72/1.00  fof(f78,plain,(
% 3.72/1.00    v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))),
% 3.72/1.00    inference(definition_unfolding,[],[f66,f60])).
% 3.72/1.00  
% 3.72/1.00  cnf(c_7,plain,
% 3.72/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.72/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1431,plain,
% 3.72/1.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_12,plain,
% 3.72/1.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.72/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1427,plain,
% 3.72/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_4,plain,
% 3.72/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 3.72/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1433,plain,
% 3.72/1.00      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 3.72/1.00      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1901,plain,
% 3.72/1.00      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_1427,c_1433]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2477,plain,
% 3.72/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_1431,c_1901]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_6,plain,
% 3.72/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.72/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2576,plain,
% 3.72/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_2477,c_6]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2,plain,
% 3.72/1.00      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.72/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1435,plain,
% 3.72/1.00      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.72/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_9,plain,
% 3.72/1.00      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X1 = X0 ),
% 3.72/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1429,plain,
% 3.72/1.00      ( X0 = X1 | r1_xboole_0(k1_tarski(X1),k1_tarski(X0)) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_8,plain,
% 3.72/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k1_tarski(X0),X1) ),
% 3.72/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1430,plain,
% 3.72/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.72/1.00      | r1_xboole_0(k1_tarski(X0),X1) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1725,plain,
% 3.72/1.00      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_1429,c_1430]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2178,plain,
% 3.72/1.00      ( sK0(X0,k1_tarski(X1)) = X1
% 3.72/1.00      | r1_xboole_0(X0,k1_tarski(X1)) = iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_1435,c_1725]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_3142,plain,
% 3.72/1.00      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_xboole_0
% 3.72/1.00      | sK0(X0,k1_tarski(X1)) = X1 ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_2178,c_1901]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_19,negated_conjecture,
% 3.72/1.00      ( v13_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 3.72/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_15,plain,
% 3.72/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 3.72/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 3.72/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 3.72/1.00      | v2_struct_0(X1)
% 3.72/1.00      | ~ l1_struct_0(X1)
% 3.72/1.00      | v1_xboole_0(X0)
% 3.72/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) ),
% 3.72/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_24,negated_conjecture,
% 3.72/1.00      ( ~ v2_struct_0(sK3) ),
% 3.72/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_317,plain,
% 3.72/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 3.72/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 3.72/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 3.72/1.00      | ~ l1_struct_0(X1)
% 3.72/1.00      | v1_xboole_0(X0)
% 3.72/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0))
% 3.72/1.00      | sK3 != X1 ),
% 3.72/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_318,plain,
% 3.72/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.72/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.72/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 3.72/1.00      | ~ l1_struct_0(sK3)
% 3.72/1.00      | v1_xboole_0(X0)
% 3.72/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 3.72/1.00      inference(unflattening,[status(thm)],[c_317]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_23,negated_conjecture,
% 3.72/1.00      ( l1_struct_0(sK3) ),
% 3.72/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_322,plain,
% 3.72/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 3.72/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.72/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.72/1.00      | v1_xboole_0(X0)
% 3.72/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 3.72/1.00      inference(global_propositional_subsumption,[status(thm)],[c_318,c_23]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_323,plain,
% 3.72/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.72/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.72/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 3.72/1.00      | v1_xboole_0(X0)
% 3.72/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0)) ),
% 3.72/1.00      inference(renaming,[status(thm)],[c_322]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_385,plain,
% 3.72/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.72/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 3.72/1.00      | v1_xboole_0(X0)
% 3.72/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),X0,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),X0))
% 3.72/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3)))
% 3.72/1.00      | sK4 != X0 ),
% 3.72/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_323]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_386,plain,
% 3.72/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3))))
% 3.72/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))))
% 3.72/1.00      | v1_xboole_0(sK4)
% 3.72/1.00      | k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 3.72/1.00      inference(unflattening,[status(thm)],[c_385]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_22,negated_conjecture,
% 3.72/1.00      ( ~ v1_xboole_0(sK4) ),
% 3.72/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_20,negated_conjecture,
% 3.72/1.00      ( v2_waybel_0(sK4,k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) ),
% 3.72/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_18,negated_conjecture,
% 3.72/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))))) ),
% 3.72/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_388,plain,
% 3.72/1.00      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,k1_tarski(k1_xboole_0)) = k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) ),
% 3.72/1.00      inference(global_propositional_subsumption,
% 3.72/1.00                [status(thm)],
% 3.72/1.00                [c_386,c_22,c_20,c_18]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_10,plain,
% 3.72/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.72/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 3.72/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_435,plain,
% 3.72/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 3.72/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X2)
% 3.72/1.00      | sK4 != X0 ),
% 3.72/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_436,plain,
% 3.72/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) = k7_subset_1(X1,sK4,X0)
% 3.72/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(X1) ),
% 3.72/1.00      inference(unflattening,[status(thm)],[c_435]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1666,plain,
% 3.72/1.00      ( k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))),sK4,X0) = k5_xboole_0(sK4,k3_xboole_0(sK4,X0)) ),
% 3.72/1.00      inference(equality_resolution,[status(thm)],[c_436]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_2631,plain,
% 3.72/1.00      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) = k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_388,c_1666]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_17,negated_conjecture,
% 3.72/1.00      ( k2_yellow19(sK3,k3_yellow19(sK3,k2_struct_0(sK3),sK4)) != sK4 ),
% 3.72/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_3550,plain,
% 3.72/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k1_tarski(k1_xboole_0))) != sK4 ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_2631,c_17]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_8483,plain,
% 3.72/1.00      ( k5_xboole_0(sK4,k1_xboole_0) != sK4
% 3.72/1.00      | sK0(sK4,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_3142,c_3550]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_8489,plain,
% 3.72/1.00      ( sK0(sK4,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_2576,c_8483]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_3,plain,
% 3.72/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.72/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1434,plain,
% 3.72/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.72/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_8636,plain,
% 3.72/1.00      ( r2_hidden(k1_xboole_0,sK4) = iProver_top
% 3.72/1.00      | r1_xboole_0(sK4,k1_tarski(k1_xboole_0)) = iProver_top ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_8489,c_1434]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_25,plain,
% 3.72/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_26,plain,
% 3.72/1.00      ( l1_struct_0(sK3) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_14,plain,
% 3.72/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.72/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_36,plain,
% 3.72/1.00      ( v2_struct_0(X0) = iProver_top
% 3.72/1.00      | l1_struct_0(X0) != iProver_top
% 3.72/1.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_38,plain,
% 3.72/1.00      ( v2_struct_0(sK3) = iProver_top
% 3.72/1.00      | l1_struct_0(sK3) != iProver_top
% 3.72/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_36]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_13,plain,
% 3.72/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.72/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_40,plain,
% 3.72/1.00      ( ~ l1_struct_0(sK3) | u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_0,plain,
% 3.72/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.72/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_74,plain,
% 3.72/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_16,plain,
% 3.72/1.00      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 3.72/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.72/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.72/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.72/1.00      | ~ r2_hidden(X2,X0)
% 3.72/1.00      | ~ v1_xboole_0(X2)
% 3.72/1.00      | v1_xboole_0(X0)
% 3.72/1.00      | v1_xboole_0(X1) ),
% 3.72/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_21,negated_conjecture,
% 3.72/1.00      ( v1_subset_1(sK4,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) ),
% 3.72/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_269,plain,
% 3.72/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.72/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 3.72/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 3.72/1.00      | ~ r2_hidden(X2,X0)
% 3.72/1.00      | ~ v1_xboole_0(X2)
% 3.72/1.00      | v1_xboole_0(X1)
% 3.72/1.00      | v1_xboole_0(X0)
% 3.72/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 3.72/1.00      | sK4 != X0 ),
% 3.72/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_270,plain,
% 3.72/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 3.72/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 3.72/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.72/1.00      | ~ r2_hidden(X1,sK4)
% 3.72/1.00      | ~ v1_xboole_0(X1)
% 3.72/1.00      | v1_xboole_0(X0)
% 3.72/1.00      | v1_xboole_0(sK4)
% 3.72/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 3.72/1.00      inference(unflattening,[status(thm)],[c_269]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_272,plain,
% 3.72/1.00      ( v1_xboole_0(X0)
% 3.72/1.00      | ~ v1_xboole_0(X1)
% 3.72/1.00      | ~ r2_hidden(X1,sK4)
% 3.72/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.72/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 3.72/1.00      | ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 3.72/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 3.72/1.00      inference(global_propositional_subsumption,[status(thm)],[c_270,c_22]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_273,plain,
% 3.72/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 3.72/1.00      | ~ v13_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 3.72/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.72/1.00      | ~ r2_hidden(X1,sK4)
% 3.72/1.00      | ~ v1_xboole_0(X1)
% 3.72/1.00      | v1_xboole_0(X0)
% 3.72/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 3.72/1.00      inference(renaming,[status(thm)],[c_272]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_358,plain,
% 3.72/1.00      ( ~ v2_waybel_0(sK4,k3_lattice3(k1_lattice3(X0)))
% 3.72/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.72/1.00      | ~ r2_hidden(X1,sK4)
% 3.72/1.00      | ~ v1_xboole_0(X1)
% 3.72/1.00      | v1_xboole_0(X0)
% 3.72/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 3.72/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 3.72/1.00      | sK4 != sK4 ),
% 3.72/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_273]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_403,plain,
% 3.72/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 3.72/1.00      | ~ r2_hidden(X1,sK4)
% 3.72/1.00      | ~ v1_xboole_0(X1)
% 3.72/1.00      | v1_xboole_0(X0)
% 3.72/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 3.72/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 3.72/1.00      | sK4 != sK4 ),
% 3.72/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_358]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_444,plain,
% 3.72/1.00      ( ~ r2_hidden(X0,sK4)
% 3.72/1.00      | ~ v1_xboole_0(X0)
% 3.72/1.00      | v1_xboole_0(X1)
% 3.72/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 3.72/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 3.72/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 3.72/1.00      | sK4 != sK4 ),
% 3.72/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_403]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_756,plain,
% 3.72/1.00      ( ~ r2_hidden(X0,sK4)
% 3.72/1.00      | ~ v1_xboole_0(X0)
% 3.72/1.00      | v1_xboole_0(X1)
% 3.72/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X1))
% 3.72/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 3.72/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))) ),
% 3.72/1.00      inference(equality_resolution_simp,[status(thm)],[c_444]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1084,plain,
% 3.72/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 3.72/1.00      inference(splitting,
% 3.72/1.00                [splitting(split),new_symbols(definition,[])],
% 3.72/1.00                [c_756]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1118,plain,
% 3.72/1.00      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_1084]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1083,plain,
% 3.72/1.00      ( ~ r2_hidden(X0,sK4) | ~ v1_xboole_0(X0) | ~ sP1_iProver_split ),
% 3.72/1.00      inference(splitting,
% 3.72/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.72/1.00                [c_756]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1483,plain,
% 3.72/1.00      ( ~ r2_hidden(k1_xboole_0,sK4)
% 3.72/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.72/1.00      | ~ sP1_iProver_split ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_1083]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1484,plain,
% 3.72/1.00      ( r2_hidden(k1_xboole_0,sK4) != iProver_top
% 3.72/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top
% 3.72/1.00      | sP1_iProver_split != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_1483]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1082,plain,
% 3.72/1.00      ( v1_xboole_0(X0)
% 3.72/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 3.72/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 3.72/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 3.72/1.00      | ~ sP0_iProver_split ),
% 3.72/1.00      inference(splitting,
% 3.72/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.72/1.00                [c_756]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1097,plain,
% 3.72/1.00      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.72/1.00      theory(equality) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1527,plain,
% 3.72/1.00      ( v1_xboole_0(X0)
% 3.72/1.00      | ~ sP0_iProver_split
% 3.72/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(X0))
% 3.72/1.00      | k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK3))))) != k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ),
% 3.72/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1082,c_1097]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1086,plain,( X0 = X0 ),theory(equality) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1587,plain,
% 3.72/1.00      ( v1_xboole_0(k2_struct_0(sK3))
% 3.72/1.00      | ~ sP0_iProver_split
% 3.72/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK3))) != k3_lattice3(k1_lattice3(k2_struct_0(sK3))) ),
% 3.72/1.00      inference(resolution,[status(thm)],[c_1527,c_1086]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1588,plain,
% 3.72/1.00      ( v1_xboole_0(k2_struct_0(sK3)) | ~ sP0_iProver_split ),
% 3.72/1.00      inference(equality_resolution_simp,[status(thm)],[c_1587]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1589,plain,
% 3.72/1.00      ( v1_xboole_0(k2_struct_0(sK3)) = iProver_top
% 3.72/1.00      | sP0_iProver_split != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_1588]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1088,plain,
% 3.72/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.72/1.00      theory(equality) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1661,plain,
% 3.72/1.00      ( ~ v1_xboole_0(X0)
% 3.72/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 3.72/1.00      | u1_struct_0(sK3) != X0 ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_1088]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1755,plain,
% 3.72/1.00      ( v1_xboole_0(u1_struct_0(sK3))
% 3.72/1.00      | ~ v1_xboole_0(k2_struct_0(sK3))
% 3.72/1.00      | u1_struct_0(sK3) != k2_struct_0(sK3) ),
% 3.72/1.00      inference(instantiation,[status(thm)],[c_1661]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_1756,plain,
% 3.72/1.00      ( u1_struct_0(sK3) != k2_struct_0(sK3)
% 3.72/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 3.72/1.00      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.72/1.00      inference(predicate_to_equality,[status(thm)],[c_1755]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_8648,plain,
% 3.72/1.00      ( r1_xboole_0(sK4,k1_tarski(k1_xboole_0)) = iProver_top ),
% 3.72/1.00      inference(global_propositional_subsumption,
% 3.72/1.00                [status(thm)],
% 3.72/1.00                [c_8636,c_25,c_23,c_26,c_38,c_40,c_74,c_1118,c_1484,c_1589,
% 3.72/1.00                 c_1756]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_8653,plain,
% 3.72/1.00      ( k3_xboole_0(sK4,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_8648,c_1901]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_10472,plain,
% 3.72/1.00      ( k5_xboole_0(sK4,k1_xboole_0) != sK4 ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_8653,c_3550]) ).
% 3.72/1.00  
% 3.72/1.00  cnf(c_10473,plain,
% 3.72/1.00      ( $false ),
% 3.72/1.00      inference(superposition,[status(thm)],[c_2576,c_10472]) ).
% 3.72/1.00  
% 3.72/1.00  
% 3.72/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.72/1.00  
% 3.72/1.00  ------                               Statistics
% 3.72/1.00  
% 3.72/1.00  ------ Selected
% 3.72/1.00  
% 3.72/1.00  total_time:                             0.321
% 3.72/1.00  
%------------------------------------------------------------------------------
