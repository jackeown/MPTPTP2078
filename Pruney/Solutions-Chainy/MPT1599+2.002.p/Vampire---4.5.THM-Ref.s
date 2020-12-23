%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:29 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  195 (1938 expanded)
%              Number of leaves         :   23 ( 687 expanded)
%              Depth                    :   32
%              Number of atoms          :  720 (6970 expanded)
%              Number of equality atoms :   87 ( 590 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f755,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f168,f578,f581,f618,f754])).

fof(f754,plain,
    ( spl4_3
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f753])).

fof(f753,plain,
    ( $false
    | spl4_3
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f752,f47])).

fof(f47,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v2_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v2_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
      & v2_lattice3(k2_yellow_1(sK0))
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

fof(f752,plain,
    ( v1_xboole_0(sK0)
    | spl4_3
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f751,f284])).

fof(f284,plain,(
    m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(subsumption_resolution,[],[f283,f77])).

fof(f77,plain,(
    m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f52,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f50,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f283,plain,
    ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(superposition,[],[f133,f265])).

fof(f265,plain,(
    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) ),
    inference(resolution,[],[f112,f78])).

fof(f78,plain,(
    m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f112,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X5) ) ),
    inference(subsumption_resolution,[],[f111,f80])).

fof(f80,plain,(
    ! [X0] : v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f56,f52])).

fof(f56,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f111,plain,(
    ! [X5] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f110,f79])).

fof(f79,plain,(
    v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f48,plain,(
    v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f110,plain,(
    ! [X5] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f98,f84])).

fof(f84,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f58,f52])).

fof(f58,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f98,plain,(
    ! [X5] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(resolution,[],[f77,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_lattice3)).

fof(f133,plain,(
    ! [X1] :
      ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) ),
    inference(subsumption_resolution,[],[f126,f84])).

fof(f126,plain,(
    ! [X1] :
      ( m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(resolution,[],[f78,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f751,plain,
    ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | v1_xboole_0(sK0)
    | spl4_3
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f750,f78])).

fof(f750,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | v1_xboole_0(sK0)
    | spl4_3
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f748,f163])).

fof(f163,plain,
    ( ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl4_3
  <=> r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f748,plain,
    ( r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | v1_xboole_0(sK0)
    | ~ spl4_19 ),
    inference(resolution,[],[f706,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f61,f52,f52,f52])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f706,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f705,f82])).

fof(f82,plain,(
    ! [X0] : v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f54,f52])).

fof(f54,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f705,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f704,f80])).

fof(f704,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f703,f79])).

fof(f703,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f702,f84])).

fof(f702,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f701,f284])).

fof(f701,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f692,f78])).

fof(f692,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_19 ),
    inference(trivial_inequality_removal,[],[f691])).

fof(f691,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)
    | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_19 ),
    inference(superposition,[],[f65,f639])).

fof(f639,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f302,f638])).

fof(f638,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2))
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f289,f637])).

fof(f637,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f631,f265])).

fof(f631,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1),sK1)
    | ~ spl4_19 ),
    inference(resolution,[],[f596,f77])).

fof(f596,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1),sK1) )
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f347,f595])).

fof(f595,plain,
    ( sK1 = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f277,f594])).

fof(f594,plain,
    ( sK1 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f593,f82])).

fof(f593,plain,
    ( sK1 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f592,f80])).

fof(f592,plain,
    ( sK1 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f591,f79])).

fof(f591,plain,
    ( sK1 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f590,f84])).

fof(f590,plain,
    ( sK1 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f584,f78])).

fof(f584,plain,
    ( sK1 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_19 ),
    inference(duplicate_literal_removal,[],[f583])).

fof(f583,plain,
    ( sK1 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_19 ),
    inference(resolution,[],[f575,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | k12_lattice3(X0,X1,X2) = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k12_lattice3(X0,X1,X2) = X1
                  | ~ r3_orders_2(X0,X1,X2) )
                & ( r3_orders_2(X0,X1,X2)
                  | k12_lattice3(X0,X1,X2) != X1 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).

fof(f575,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f573])).

fof(f573,plain,
    ( spl4_19
  <=> r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f277,plain,(
    k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) ),
    inference(resolution,[],[f136,f78])).

fof(f136,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1) ) ),
    inference(subsumption_resolution,[],[f135,f80])).

fof(f135,plain,(
    ! [X2] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f134,f79])).

fof(f134,plain,(
    ! [X2] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f127,f84])).

fof(f127,plain,(
    ! [X2] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(resolution,[],[f78,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

% (22056)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f347,plain,(
    ! [X1] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1))
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) ),
    inference(resolution,[],[f140,f78])).

fof(f140,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK1))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) ),
    inference(subsumption_resolution,[],[f139,f80])).

fof(f139,plain,(
    ! [X4,X3] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK1))
      | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f138,f79])).

fof(f138,plain,(
    ! [X4,X3] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK1))
      | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f137,f84])).

fof(f137,plain,(
    ! [X4,X3] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK1))
      | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f128,f81])).

fof(f81,plain,(
    ! [X0] : v4_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f55,f52])).

fof(f55,plain,(
    ! [X0] : v4_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f128,plain,(
    ! [X4,X3] :
      ( ~ v4_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK1))
      | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(resolution,[],[f78,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3))
                  | ~ v4_orders_2(X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3))
                  | ~ v4_orders_2(X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( v4_orders_2(X0)
                   => k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_lattice3)).

fof(f289,plain,(
    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) ),
    inference(resolution,[],[f284,f143])).

fof(f143,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X5) ) ),
    inference(subsumption_resolution,[],[f142,f80])).

fof(f142,plain,(
    ! [X5] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f141,f79])).

fof(f141,plain,(
    ! [X5] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f129,f84])).

fof(f129,plain,(
    ! [X5] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(resolution,[],[f78,f67])).

fof(f302,plain,(
    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
    inference(forward_demodulation,[],[f290,f289])).

fof(f290,plain,(
    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
    inference(resolution,[],[f284,f136])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) != X1
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f618,plain,
    ( ~ spl4_2
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f617])).

fof(f617,plain,
    ( $false
    | ~ spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f616,f47])).

fof(f616,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f615,f284])).

fof(f615,plain,
    ( ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | v1_xboole_0(sK0)
    | ~ spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f614,f77])).

fof(f614,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | v1_xboole_0(sK0)
    | ~ spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f612,f167])).

fof(f167,plain,
    ( ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl4_4
  <=> r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f612,plain,
    ( r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | v1_xboole_0(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f538,f89])).

% (22070)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f538,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f537,f82])).

fof(f537,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f536,f80])).

fof(f536,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f535,f79])).

fof(f535,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f534,f84])).

fof(f534,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f533,f284])).

fof(f533,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f524,f77])).

fof(f524,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f523])).

fof(f523,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)
    | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(superposition,[],[f65,f414])).

fof(f414,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f303,f411])).

fof(f411,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f291,f405])).

fof(f405,plain,
    ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f333,f78])).

fof(f333,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
        | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),sK2) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f328,f262])).

fof(f262,plain,
    ( sK2 = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f258,f158])).

fof(f158,plain,
    ( sK2 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f157,f82])).

fof(f157,plain,
    ( sK2 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f156,f80])).

fof(f156,plain,
    ( sK2 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f155,f79])).

fof(f155,plain,
    ( sK2 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f154,f84])).

fof(f154,plain,
    ( sK2 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f150,f77])).

fof(f150,plain,
    ( sK2 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,
    ( sK2 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f123,f66])).

fof(f123,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_2
  <=> r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f258,plain,(
    k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) ),
    inference(resolution,[],[f105,f77])).

fof(f105,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2) ) ),
    inference(subsumption_resolution,[],[f104,f80])).

fof(f104,plain,(
    ! [X2] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f103,f79])).

fof(f103,plain,(
    ! [X2] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f96,f84])).

fof(f96,plain,(
    ! [X2] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2)
      | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(resolution,[],[f77,f73])).

fof(f328,plain,(
    ! [X0] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) ),
    inference(resolution,[],[f109,f77])).

fof(f109,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK2))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) ) ),
    inference(subsumption_resolution,[],[f108,f80])).

fof(f108,plain,(
    ! [X4,X3] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK2))
      | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f107,f79])).

fof(f107,plain,(
    ! [X4,X3] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK2))
      | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f106,f84])).

fof(f106,plain,(
    ! [X4,X3] :
      ( k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK2))
      | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f97,f81])).

fof(f97,plain,(
    ! [X4,X3] :
      ( ~ v4_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK2))
      | ~ m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))
      | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))
      | ~ v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) ) ),
    inference(resolution,[],[f77,f68])).

fof(f291,plain,(
    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) ),
    inference(resolution,[],[f284,f112])).

fof(f303,plain,(
    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) ),
    inference(forward_demodulation,[],[f292,f291])).

fof(f292,plain,(
    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) ),
    inference(resolution,[],[f284,f105])).

fof(f581,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f580])).

fof(f580,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f579,f47])).

fof(f579,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f119,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f59,f52])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f119,plain,
    ( v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_1
  <=> v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f578,plain,
    ( spl4_1
    | spl4_19 ),
    inference(avatar_split_clause,[],[f577,f573,f117])).

fof(f577,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f145,f99])).

fof(f99,plain,(
    sP3(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(resolution,[],[f77,f91])).

% (22063)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f91,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP3(X0) ) ),
    inference(cnf_transformation,[],[f91_D])).

fof(f91_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(X0))
    <=> ~ sP3(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).

fof(f145,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ sP3(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f144,f82])).

fof(f144,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ sP3(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f131,f84])).

fof(f131,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ sP3(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(resolution,[],[f78,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP3(X0) ) ),
    inference(general_splitting,[],[f72,f91_D])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f168,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f159,f165,f161])).

fof(f159,plain,
    ( ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)
    | ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) ),
    inference(resolution,[],[f76,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f75,f69])).

fof(f69,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f76,plain,(
    ~ r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(definition_unfolding,[],[f51,f52,f69])).

fof(f51,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f124,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f115,f121,f117])).

fof(f115,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f114,f99])).

fof(f114,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ sP3(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f113,f82])).

fof(f113,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ sP3(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f100,f84])).

fof(f100,plain,
    ( r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)
    | ~ l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))
    | ~ sP3(g1_orders_2(sK0,k1_yellow_1(sK0))) ),
    inference(resolution,[],[f77,f92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:45:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.44/0.56  % (22054)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.44/0.56  % (22060)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.44/0.57  % (22073)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.44/0.57  % (22081)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.57  % (22064)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.58  % (22069)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.66/0.58  % (22052)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.66/0.58  % (22052)Refutation not found, incomplete strategy% (22052)------------------------------
% 1.66/0.58  % (22052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (22052)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.58  
% 1.66/0.58  % (22052)Memory used [KB]: 1663
% 1.66/0.58  % (22052)Time elapsed: 0.147 s
% 1.66/0.58  % (22052)------------------------------
% 1.66/0.58  % (22052)------------------------------
% 1.66/0.58  % (22057)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.66/0.58  % (22077)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.66/0.58  % (22069)Refutation not found, incomplete strategy% (22069)------------------------------
% 1.66/0.58  % (22069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (22069)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.58  
% 1.66/0.58  % (22069)Memory used [KB]: 10618
% 1.66/0.58  % (22069)Time elapsed: 0.156 s
% 1.66/0.58  % (22069)------------------------------
% 1.66/0.58  % (22069)------------------------------
% 1.66/0.59  % (22061)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.66/0.59  % (22071)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.66/0.59  % (22067)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.66/0.59  % (22061)Refutation not found, incomplete strategy% (22061)------------------------------
% 1.66/0.59  % (22061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (22060)Refutation found. Thanks to Tanya!
% 1.66/0.60  % SZS status Theorem for theBenchmark
% 1.66/0.60  % (22061)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.60  
% 1.66/0.60  % (22061)Memory used [KB]: 10746
% 1.66/0.60  % (22061)Time elapsed: 0.159 s
% 1.66/0.60  % (22061)------------------------------
% 1.66/0.60  % (22061)------------------------------
% 1.66/0.60  % (22059)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.66/0.60  % (22075)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.66/0.60  % (22053)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.66/0.61  % (22065)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.66/0.61  % (22072)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.66/0.61  % (22055)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.66/0.61  % (22079)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.66/0.61  % (22062)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.66/0.61  % SZS output start Proof for theBenchmark
% 1.66/0.61  fof(f755,plain,(
% 1.66/0.61    $false),
% 1.66/0.61    inference(avatar_sat_refutation,[],[f124,f168,f578,f581,f618,f754])).
% 1.66/0.61  fof(f754,plain,(
% 1.66/0.61    spl4_3 | ~spl4_19),
% 1.66/0.61    inference(avatar_contradiction_clause,[],[f753])).
% 1.66/0.61  fof(f753,plain,(
% 1.66/0.61    $false | (spl4_3 | ~spl4_19)),
% 1.66/0.61    inference(subsumption_resolution,[],[f752,f47])).
% 1.66/0.61  fof(f47,plain,(
% 1.66/0.61    ~v1_xboole_0(sK0)),
% 1.66/0.61    inference(cnf_transformation,[],[f44])).
% 1.66/0.61  fof(f44,plain,(
% 1.66/0.61    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 1.66/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f43,f42,f41])).
% 1.66/0.61  fof(f41,plain,(
% 1.66/0.61    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 1.66/0.61    introduced(choice_axiom,[])).
% 1.66/0.61  fof(f42,plain,(
% 1.66/0.61    ? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 1.66/0.61    introduced(choice_axiom,[])).
% 1.66/0.61  fof(f43,plain,(
% 1.66/0.61    ? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 1.66/0.61    introduced(choice_axiom,[])).
% 1.66/0.61  fof(f20,plain,(
% 1.66/0.61    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 1.66/0.61    inference(flattening,[],[f19])).
% 1.66/0.61  fof(f19,plain,(
% 1.66/0.61    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 1.66/0.61    inference(ennf_transformation,[],[f18])).
% 1.66/0.61  fof(f18,negated_conjecture,(
% 1.66/0.61    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 1.66/0.61    inference(negated_conjecture,[],[f17])).
% 1.66/0.61  fof(f17,conjecture,(
% 1.66/0.61    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).
% 1.66/0.61  fof(f752,plain,(
% 1.66/0.61    v1_xboole_0(sK0) | (spl4_3 | ~spl4_19)),
% 1.66/0.61    inference(subsumption_resolution,[],[f751,f284])).
% 1.66/0.61  fof(f284,plain,(
% 1.66/0.61    m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 1.66/0.61    inference(subsumption_resolution,[],[f283,f77])).
% 1.66/0.61  fof(f77,plain,(
% 1.66/0.61    m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 1.66/0.61    inference(definition_unfolding,[],[f50,f52])).
% 1.66/0.61  fof(f52,plain,(
% 1.66/0.61    ( ! [X0] : (k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))) )),
% 1.66/0.61    inference(cnf_transformation,[],[f12])).
% 1.66/0.61  fof(f12,axiom,(
% 1.66/0.61    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).
% 1.66/0.61  fof(f50,plain,(
% 1.66/0.61    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 1.66/0.61    inference(cnf_transformation,[],[f44])).
% 1.66/0.61  fof(f283,plain,(
% 1.66/0.61    m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 1.66/0.61    inference(superposition,[],[f133,f265])).
% 1.66/0.61  fof(f265,plain,(
% 1.66/0.61    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1)),
% 1.66/0.61    inference(resolution,[],[f112,f78])).
% 1.66/0.61  fof(f78,plain,(
% 1.66/0.61    m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))),
% 1.66/0.61    inference(definition_unfolding,[],[f49,f52])).
% 1.66/0.61  fof(f49,plain,(
% 1.66/0.61    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 1.66/0.61    inference(cnf_transformation,[],[f44])).
% 1.66/0.61  fof(f112,plain,(
% 1.66/0.61    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X5)) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f111,f80])).
% 1.66/0.61  fof(f80,plain,(
% 1.66/0.61    ( ! [X0] : (v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 1.66/0.61    inference(definition_unfolding,[],[f56,f52])).
% 1.66/0.61  fof(f56,plain,(
% 1.66/0.61    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 1.66/0.61    inference(cnf_transformation,[],[f14])).
% 1.66/0.61  fof(f14,axiom,(
% 1.66/0.61    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 1.66/0.61  fof(f111,plain,(
% 1.66/0.61    ( ! [X5] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X5) | ~m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f110,f79])).
% 1.66/0.61  fof(f79,plain,(
% 1.66/0.61    v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 1.66/0.61    inference(definition_unfolding,[],[f48,f52])).
% 1.66/0.61  fof(f48,plain,(
% 1.66/0.61    v2_lattice3(k2_yellow_1(sK0))),
% 1.66/0.61    inference(cnf_transformation,[],[f44])).
% 1.66/0.61  fof(f110,plain,(
% 1.66/0.61    ( ! [X5] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X5) | ~m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f98,f84])).
% 1.66/0.61  fof(f84,plain,(
% 1.66/0.61    ( ! [X0] : (l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 1.66/0.61    inference(definition_unfolding,[],[f58,f52])).
% 1.66/0.61  fof(f58,plain,(
% 1.66/0.61    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 1.66/0.61    inference(cnf_transformation,[],[f13])).
% 1.66/0.61  fof(f13,axiom,(
% 1.66/0.61    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 1.66/0.61  fof(f98,plain,(
% 1.66/0.61    ( ! [X5] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,X5) | ~m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.61    inference(resolution,[],[f77,f67])).
% 1.66/0.61  fof(f67,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f29])).
% 1.66/0.61  fof(f29,plain,(
% 1.66/0.61    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 1.66/0.61    inference(flattening,[],[f28])).
% 1.66/0.61  fof(f28,plain,(
% 1.66/0.61    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 1.66/0.61    inference(ennf_transformation,[],[f9])).
% 1.66/0.61  fof(f9,axiom,(
% 1.66/0.61    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_lattice3)).
% 1.66/0.61  fof(f133,plain,(
% 1.66/0.61    ( ! [X1] : (m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f126,f84])).
% 1.66/0.61  fof(f126,plain,(
% 1.66/0.61    ( ! [X1] : (m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.61    inference(resolution,[],[f78,f74])).
% 1.66/0.61  fof(f74,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f38])).
% 1.66/0.61  fof(f38,plain,(
% 1.66/0.61    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.66/0.61    inference(flattening,[],[f37])).
% 1.66/0.61  fof(f37,plain,(
% 1.66/0.61    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 1.66/0.61    inference(ennf_transformation,[],[f7])).
% 1.66/0.61  fof(f7,axiom,(
% 1.66/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 1.66/0.61  fof(f751,plain,(
% 1.66/0.61    ~m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v1_xboole_0(sK0) | (spl4_3 | ~spl4_19)),
% 1.66/0.61    inference(subsumption_resolution,[],[f750,f78])).
% 1.66/0.61  fof(f750,plain,(
% 1.66/0.61    ~m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v1_xboole_0(sK0) | (spl4_3 | ~spl4_19)),
% 1.66/0.61    inference(subsumption_resolution,[],[f748,f163])).
% 1.66/0.61  fof(f163,plain,(
% 1.66/0.61    ~r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) | spl4_3),
% 1.66/0.61    inference(avatar_component_clause,[],[f161])).
% 1.66/0.61  fof(f161,plain,(
% 1.66/0.61    spl4_3 <=> r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)),
% 1.66/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.66/0.61  fof(f748,plain,(
% 1.66/0.61    r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v1_xboole_0(sK0) | ~spl4_19),
% 1.66/0.61    inference(resolution,[],[f706,f89])).
% 1.66/0.61  fof(f89,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~r3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)),X1,X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0)))) | v1_xboole_0(X0)) )),
% 1.66/0.61    inference(definition_unfolding,[],[f61,f52,f52,f52])).
% 1.66/0.61  fof(f61,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f45])).
% 1.66/0.61  fof(f45,plain,(
% 1.66/0.61    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.66/0.61    inference(nnf_transformation,[],[f22])).
% 1.66/0.61  fof(f22,plain,(
% 1.66/0.61    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.66/0.61    inference(ennf_transformation,[],[f16])).
% 1.66/0.61  fof(f16,axiom,(
% 1.66/0.61    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 1.66/0.61  fof(f706,plain,(
% 1.66/0.61    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) | ~spl4_19),
% 1.66/0.61    inference(subsumption_resolution,[],[f705,f82])).
% 1.66/0.61  fof(f82,plain,(
% 1.66/0.61    ( ! [X0] : (v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 1.66/0.61    inference(definition_unfolding,[],[f54,f52])).
% 1.66/0.61  fof(f54,plain,(
% 1.66/0.61    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 1.66/0.61    inference(cnf_transformation,[],[f14])).
% 1.66/0.61  fof(f705,plain,(
% 1.66/0.61    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_19),
% 1.66/0.61    inference(subsumption_resolution,[],[f704,f80])).
% 1.66/0.61  fof(f704,plain,(
% 1.66/0.61    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_19),
% 1.66/0.61    inference(subsumption_resolution,[],[f703,f79])).
% 1.66/0.61  fof(f703,plain,(
% 1.66/0.61    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_19),
% 1.66/0.61    inference(subsumption_resolution,[],[f702,f84])).
% 1.66/0.61  fof(f702,plain,(
% 1.66/0.61    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_19),
% 1.66/0.61    inference(subsumption_resolution,[],[f701,f284])).
% 1.66/0.61  fof(f701,plain,(
% 1.66/0.61    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) | ~m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_19),
% 1.66/0.61    inference(subsumption_resolution,[],[f692,f78])).
% 1.66/0.61  fof(f692,plain,(
% 1.66/0.61    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_19),
% 1.66/0.61    inference(trivial_inequality_removal,[],[f691])).
% 1.66/0.61  fof(f691,plain,(
% 1.66/0.61    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_19),
% 1.66/0.61    inference(superposition,[],[f65,f639])).
% 1.66/0.61  fof(f639,plain,(
% 1.66/0.61    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) | ~spl4_19),
% 1.66/0.61    inference(backward_demodulation,[],[f302,f638])).
% 1.66/0.61  fof(f638,plain,(
% 1.66/0.61    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) | ~spl4_19),
% 1.66/0.61    inference(backward_demodulation,[],[f289,f637])).
% 1.66/0.61  fof(f637,plain,(
% 1.66/0.61    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) | ~spl4_19),
% 1.66/0.61    inference(forward_demodulation,[],[f631,f265])).
% 1.66/0.61  fof(f631,plain,(
% 1.66/0.61    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK1),sK1) | ~spl4_19),
% 1.66/0.61    inference(resolution,[],[f596,f77])).
% 1.66/0.61  fof(f596,plain,(
% 1.66/0.61    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1),sK1)) ) | ~spl4_19),
% 1.66/0.61    inference(backward_demodulation,[],[f347,f595])).
% 1.66/0.61  fof(f595,plain,(
% 1.66/0.61    sK1 = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) | ~spl4_19),
% 1.66/0.61    inference(backward_demodulation,[],[f277,f594])).
% 1.66/0.61  fof(f594,plain,(
% 1.66/0.61    sK1 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) | ~spl4_19),
% 1.66/0.61    inference(subsumption_resolution,[],[f593,f82])).
% 1.66/0.61  fof(f593,plain,(
% 1.66/0.61    sK1 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_19),
% 1.66/0.61    inference(subsumption_resolution,[],[f592,f80])).
% 1.66/0.62  fof(f592,plain,(
% 1.66/0.62    sK1 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_19),
% 1.66/0.62    inference(subsumption_resolution,[],[f591,f79])).
% 1.66/0.62  fof(f591,plain,(
% 1.66/0.62    sK1 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_19),
% 1.66/0.62    inference(subsumption_resolution,[],[f590,f84])).
% 1.66/0.62  fof(f590,plain,(
% 1.66/0.62    sK1 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_19),
% 1.66/0.62    inference(subsumption_resolution,[],[f584,f78])).
% 1.66/0.62  fof(f584,plain,(
% 1.66/0.62    sK1 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_19),
% 1.66/0.62    inference(duplicate_literal_removal,[],[f583])).
% 1.66/0.62  fof(f583,plain,(
% 1.66/0.62    sK1 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_19),
% 1.66/0.62    inference(resolution,[],[f575,f66])).
% 1.66/0.62  fof(f66,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f46])).
% 1.66/0.62  fof(f46,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : (((k12_lattice3(X0,X1,X2) = X1 | ~r3_orders_2(X0,X1,X2)) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 1.66/0.62    inference(nnf_transformation,[],[f27])).
% 1.66/0.62  fof(f27,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 1.66/0.62    inference(flattening,[],[f26])).
% 1.66/0.62  fof(f26,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : ((k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 1.66/0.62    inference(ennf_transformation,[],[f11])).
% 1.66/0.62  fof(f11,axiom,(
% 1.66/0.62    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).
% 1.66/0.62  fof(f575,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) | ~spl4_19),
% 1.66/0.62    inference(avatar_component_clause,[],[f573])).
% 1.66/0.62  fof(f573,plain,(
% 1.66/0.62    spl4_19 <=> r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.66/0.62  fof(f277,plain,(
% 1.66/0.62    k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)),
% 1.66/0.62    inference(resolution,[],[f136,f78])).
% 1.66/0.62  fof(f136,plain,(
% 1.66/0.62    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1)) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f135,f80])).
% 1.66/0.62  fof(f135,plain,(
% 1.66/0.62    ( ! [X2] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f134,f79])).
% 1.66/0.62  fof(f134,plain,(
% 1.66/0.62    ( ! [X2] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f127,f84])).
% 1.66/0.62  fof(f127,plain,(
% 1.66/0.62    ( ! [X2] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK1) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(resolution,[],[f78,f73])).
% 1.66/0.62  fof(f73,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f36])).
% 1.66/0.62  fof(f36,plain,(
% 1.66/0.62    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 1.66/0.62    inference(flattening,[],[f35])).
% 1.66/0.62  % (22056)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.66/0.62  fof(f35,plain,(
% 1.66/0.62    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 1.66/0.62    inference(ennf_transformation,[],[f8])).
% 1.66/0.62  fof(f8,axiom,(
% 1.66/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 1.66/0.62  fof(f347,plain,(
% 1.66/0.62    ( ! [X1] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,sK1),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1)) | ~m1_subset_1(X1,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))) )),
% 1.66/0.62    inference(resolution,[],[f140,f78])).
% 1.66/0.62  fof(f140,plain,(
% 1.66/0.62    ( ! [X4,X3] : (~m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK1)) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f139,f80])).
% 1.66/0.62  fof(f139,plain,(
% 1.66/0.62    ( ! [X4,X3] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK1)) | ~m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f138,f79])).
% 1.66/0.62  fof(f138,plain,(
% 1.66/0.62    ( ! [X4,X3] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK1)) | ~m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f137,f84])).
% 1.66/0.62  fof(f137,plain,(
% 1.66/0.62    ( ! [X4,X3] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK1)) | ~m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f128,f81])).
% 1.66/0.62  fof(f81,plain,(
% 1.66/0.62    ( ! [X0] : (v4_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) )),
% 1.66/0.62    inference(definition_unfolding,[],[f55,f52])).
% 1.66/0.62  fof(f55,plain,(
% 1.66/0.62    ( ! [X0] : (v4_orders_2(k2_yellow_1(X0))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f14])).
% 1.66/0.62  fof(f128,plain,(
% 1.66/0.62    ( ! [X4,X3] : (~v4_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK1)) | ~m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(resolution,[],[f78,f68])).
% 1.66/0.62  fof(f68,plain,(
% 1.66/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,u1_struct_0(X0)) | ~v4_orders_2(X0) | k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f31])).
% 1.66/0.62  fof(f31,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~v4_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 1.66/0.62    inference(flattening,[],[f30])).
% 1.66/0.62  fof(f30,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)) | ~v4_orders_2(X0)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 1.66/0.62    inference(ennf_transformation,[],[f10])).
% 1.66/0.62  fof(f10,axiom,(
% 1.66/0.62    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (v4_orders_2(X0) => k11_lattice3(X0,k11_lattice3(X0,X1,X2),X3) = k11_lattice3(X0,X1,k11_lattice3(X0,X2,X3)))))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_lattice3)).
% 1.66/0.62  fof(f289,plain,(
% 1.66/0.62    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2))),
% 1.66/0.62    inference(resolution,[],[f284,f143])).
% 1.66/0.62  fof(f143,plain,(
% 1.66/0.62    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X5)) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f142,f80])).
% 1.66/0.62  fof(f142,plain,(
% 1.66/0.62    ( ! [X5] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X5) | ~m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f141,f79])).
% 1.66/0.62  fof(f141,plain,(
% 1.66/0.62    ( ! [X5] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X5) | ~m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f129,f84])).
% 1.66/0.62  fof(f129,plain,(
% 1.66/0.62    ( ! [X5] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X5,sK1) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,X5) | ~m1_subset_1(X5,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(resolution,[],[f78,f67])).
% 1.66/0.62  fof(f302,plain,(
% 1.66/0.62    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)),
% 1.66/0.62    inference(forward_demodulation,[],[f290,f289])).
% 1.66/0.62  fof(f290,plain,(
% 1.66/0.62    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)),
% 1.66/0.62    inference(resolution,[],[f284,f136])).
% 1.66/0.62  fof(f65,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) != X1 | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f46])).
% 1.66/0.62  fof(f618,plain,(
% 1.66/0.62    ~spl4_2 | spl4_4),
% 1.66/0.62    inference(avatar_contradiction_clause,[],[f617])).
% 1.66/0.62  fof(f617,plain,(
% 1.66/0.62    $false | (~spl4_2 | spl4_4)),
% 1.66/0.62    inference(subsumption_resolution,[],[f616,f47])).
% 1.66/0.62  fof(f616,plain,(
% 1.66/0.62    v1_xboole_0(sK0) | (~spl4_2 | spl4_4)),
% 1.66/0.62    inference(subsumption_resolution,[],[f615,f284])).
% 1.66/0.62  fof(f615,plain,(
% 1.66/0.62    ~m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v1_xboole_0(sK0) | (~spl4_2 | spl4_4)),
% 1.66/0.62    inference(subsumption_resolution,[],[f614,f77])).
% 1.66/0.62  fof(f614,plain,(
% 1.66/0.62    ~m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v1_xboole_0(sK0) | (~spl4_2 | spl4_4)),
% 1.66/0.62    inference(subsumption_resolution,[],[f612,f167])).
% 1.66/0.62  fof(f167,plain,(
% 1.66/0.62    ~r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) | spl4_4),
% 1.66/0.62    inference(avatar_component_clause,[],[f165])).
% 1.66/0.62  fof(f165,plain,(
% 1.66/0.62    spl4_4 <=> r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.66/0.62  fof(f612,plain,(
% 1.66/0.62    r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | v1_xboole_0(sK0) | ~spl4_2),
% 1.66/0.62    inference(resolution,[],[f538,f89])).
% 1.66/0.62  % (22070)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.66/0.62  fof(f538,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) | ~spl4_2),
% 1.66/0.62    inference(subsumption_resolution,[],[f537,f82])).
% 1.66/0.62  fof(f537,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_2),
% 1.66/0.62    inference(subsumption_resolution,[],[f536,f80])).
% 1.66/0.62  fof(f536,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_2),
% 1.66/0.62    inference(subsumption_resolution,[],[f535,f79])).
% 1.66/0.62  fof(f535,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_2),
% 1.66/0.62    inference(subsumption_resolution,[],[f534,f84])).
% 1.66/0.62  fof(f534,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_2),
% 1.66/0.62    inference(subsumption_resolution,[],[f533,f284])).
% 1.66/0.62  fof(f533,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) | ~m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_2),
% 1.66/0.62    inference(subsumption_resolution,[],[f524,f77])).
% 1.66/0.62  fof(f524,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_2),
% 1.66/0.62    inference(trivial_inequality_removal,[],[f523])).
% 1.66/0.62  fof(f523,plain,(
% 1.66/0.62    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) != k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) | r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_2),
% 1.66/0.62    inference(superposition,[],[f65,f414])).
% 1.66/0.62  fof(f414,plain,(
% 1.66/0.62    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) | ~spl4_2),
% 1.66/0.62    inference(backward_demodulation,[],[f303,f411])).
% 1.66/0.62  fof(f411,plain,(
% 1.66/0.62    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) | ~spl4_2),
% 1.66/0.62    inference(backward_demodulation,[],[f291,f405])).
% 1.66/0.62  fof(f405,plain,(
% 1.66/0.62    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) | ~spl4_2),
% 1.66/0.62    inference(resolution,[],[f333,f78])).
% 1.66/0.62  fof(f333,plain,(
% 1.66/0.62    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),sK2)) ) | ~spl4_2),
% 1.66/0.62    inference(forward_demodulation,[],[f328,f262])).
% 1.66/0.62  fof(f262,plain,(
% 1.66/0.62    sK2 = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) | ~spl4_2),
% 1.66/0.62    inference(forward_demodulation,[],[f258,f158])).
% 1.66/0.62  fof(f158,plain,(
% 1.66/0.62    sK2 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) | ~spl4_2),
% 1.66/0.62    inference(subsumption_resolution,[],[f157,f82])).
% 1.66/0.62  fof(f157,plain,(
% 1.66/0.62    sK2 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_2),
% 1.66/0.62    inference(subsumption_resolution,[],[f156,f80])).
% 1.66/0.62  fof(f156,plain,(
% 1.66/0.62    sK2 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_2),
% 1.66/0.62    inference(subsumption_resolution,[],[f155,f79])).
% 1.66/0.62  fof(f155,plain,(
% 1.66/0.62    sK2 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_2),
% 1.66/0.62    inference(subsumption_resolution,[],[f154,f84])).
% 1.66/0.62  fof(f154,plain,(
% 1.66/0.62    sK2 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_2),
% 1.66/0.62    inference(subsumption_resolution,[],[f150,f77])).
% 1.66/0.62  fof(f150,plain,(
% 1.66/0.62    sK2 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) | ~m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_2),
% 1.66/0.62    inference(duplicate_literal_removal,[],[f149])).
% 1.66/0.62  fof(f149,plain,(
% 1.66/0.62    sK2 = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) | ~m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(sK2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_2),
% 1.66/0.62    inference(resolution,[],[f123,f66])).
% 1.66/0.62  fof(f123,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) | ~spl4_2),
% 1.66/0.62    inference(avatar_component_clause,[],[f121])).
% 1.66/0.62  fof(f121,plain,(
% 1.66/0.62    spl4_2 <=> r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.66/0.62  fof(f258,plain,(
% 1.66/0.62    k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)),
% 1.66/0.62    inference(resolution,[],[f105,f77])).
% 1.66/0.62  fof(f105,plain,(
% 1.66/0.62    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2)) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f104,f80])).
% 1.66/0.62  fof(f104,plain,(
% 1.66/0.62    ( ! [X2] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f103,f79])).
% 1.66/0.62  fof(f103,plain,(
% 1.66/0.62    ( ! [X2] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f96,f84])).
% 1.66/0.62  fof(f96,plain,(
% 1.66/0.62    ( ! [X2] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X2,sK2) | ~m1_subset_1(X2,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(resolution,[],[f77,f73])).
% 1.66/0.62  fof(f328,plain,(
% 1.66/0.62    ( ! [X0] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X0,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2)) | ~m1_subset_1(X0,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))) )),
% 1.66/0.62    inference(resolution,[],[f109,f77])).
% 1.66/0.62  fof(f109,plain,(
% 1.66/0.62    ( ! [X4,X3] : (~m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK2)) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))))) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f108,f80])).
% 1.66/0.62  fof(f108,plain,(
% 1.66/0.62    ( ! [X4,X3] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK2)) | ~m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f107,f79])).
% 1.66/0.62  fof(f107,plain,(
% 1.66/0.62    ( ! [X4,X3] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK2)) | ~m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f106,f84])).
% 1.66/0.62  fof(f106,plain,(
% 1.66/0.62    ( ! [X4,X3] : (k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK2)) | ~m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f97,f81])).
% 1.66/0.62  fof(f97,plain,(
% 1.66/0.62    ( ! [X4,X3] : (~v4_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,X4),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X3,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),X4,sK2)) | ~m1_subset_1(X4,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~m1_subset_1(X3,u1_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v2_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v5_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)))) )),
% 1.66/0.62    inference(resolution,[],[f77,f68])).
% 1.66/0.62  fof(f291,plain,(
% 1.66/0.62    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2))),
% 1.66/0.62    inference(resolution,[],[f284,f112])).
% 1.66/0.62  fof(f303,plain,(
% 1.66/0.62    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2)) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)),
% 1.66/0.62    inference(forward_demodulation,[],[f292,f291])).
% 1.66/0.62  fof(f292,plain,(
% 1.66/0.62    k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) = k12_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2)),
% 1.66/0.62    inference(resolution,[],[f284,f105])).
% 1.66/0.62  fof(f581,plain,(
% 1.66/0.62    ~spl4_1),
% 1.66/0.62    inference(avatar_contradiction_clause,[],[f580])).
% 1.66/0.62  fof(f580,plain,(
% 1.66/0.62    $false | ~spl4_1),
% 1.66/0.62    inference(subsumption_resolution,[],[f579,f47])).
% 1.66/0.62  fof(f579,plain,(
% 1.66/0.62    v1_xboole_0(sK0) | ~spl4_1),
% 1.66/0.62    inference(resolution,[],[f119,f87])).
% 1.66/0.62  fof(f87,plain,(
% 1.66/0.62    ( ! [X0] : (~v2_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 1.66/0.62    inference(definition_unfolding,[],[f59,f52])).
% 1.66/0.62  fof(f59,plain,(
% 1.66/0.62    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f21])).
% 1.66/0.62  fof(f21,plain,(
% 1.66/0.62    ! [X0] : ((v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0))),
% 1.66/0.62    inference(ennf_transformation,[],[f15])).
% 1.66/0.62  fof(f15,axiom,(
% 1.66/0.62    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).
% 1.66/0.62  fof(f119,plain,(
% 1.66/0.62    v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~spl4_1),
% 1.66/0.62    inference(avatar_component_clause,[],[f117])).
% 1.66/0.62  fof(f117,plain,(
% 1.66/0.62    spl4_1 <=> v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.66/0.62  fof(f578,plain,(
% 1.66/0.62    spl4_1 | spl4_19),
% 1.66/0.62    inference(avatar_split_clause,[],[f577,f573,f117])).
% 1.66/0.62  fof(f577,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 1.66/0.62    inference(subsumption_resolution,[],[f145,f99])).
% 1.66/0.62  fof(f99,plain,(
% 1.66/0.62    sP3(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 1.66/0.62    inference(resolution,[],[f77,f91])).
% 1.66/0.62  % (22063)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.66/0.62  fof(f91,plain,(
% 1.66/0.62    ( ! [X2,X0] : (~m1_subset_1(X2,u1_struct_0(X0)) | sP3(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f91_D])).
% 1.66/0.62  fof(f91_D,plain,(
% 1.66/0.62    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,u1_struct_0(X0)) ) <=> ~sP3(X0)) )),
% 1.66/0.62    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).
% 1.66/0.62  fof(f145,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~sP3(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 1.66/0.62    inference(subsumption_resolution,[],[f144,f82])).
% 1.66/0.62  fof(f144,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~sP3(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 1.66/0.62    inference(subsumption_resolution,[],[f131,f84])).
% 1.66/0.62  fof(f131,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK1) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~sP3(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 1.66/0.62    inference(resolution,[],[f78,f92])).
% 1.66/0.62  fof(f92,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~sP3(X0)) )),
% 1.66/0.62    inference(general_splitting,[],[f72,f91_D])).
% 1.66/0.62  fof(f72,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f34])).
% 1.66/0.62  fof(f34,plain,(
% 1.66/0.62    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.66/0.62    inference(flattening,[],[f33])).
% 1.66/0.62  fof(f33,plain,(
% 1.66/0.62    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.66/0.62    inference(ennf_transformation,[],[f6])).
% 1.66/0.62  fof(f6,axiom,(
% 1.66/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).
% 1.66/0.62  fof(f168,plain,(
% 1.66/0.62    ~spl4_3 | ~spl4_4),
% 1.66/0.62    inference(avatar_split_clause,[],[f159,f165,f161])).
% 1.66/0.62  fof(f159,plain,(
% 1.66/0.62    ~r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK2) | ~r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),sK1)),
% 1.66/0.62    inference(resolution,[],[f76,f90])).
% 1.66/0.62  fof(f90,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.66/0.62    inference(definition_unfolding,[],[f75,f69])).
% 1.66/0.62  fof(f69,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f2])).
% 1.66/0.62  fof(f2,axiom,(
% 1.66/0.62    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.66/0.62  fof(f75,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f40])).
% 1.66/0.62  fof(f40,plain,(
% 1.66/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.66/0.62    inference(flattening,[],[f39])).
% 1.66/0.62  fof(f39,plain,(
% 1.66/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.66/0.62    inference(ennf_transformation,[],[f1])).
% 1.66/0.62  fof(f1,axiom,(
% 1.66/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.66/0.62  fof(f76,plain,(
% 1.66/0.62    ~r1_tarski(k11_lattice3(g1_orders_2(sK0,k1_yellow_1(sK0)),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))),
% 1.66/0.62    inference(definition_unfolding,[],[f51,f52,f69])).
% 1.66/0.62  fof(f51,plain,(
% 1.66/0.62    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 1.66/0.62    inference(cnf_transformation,[],[f44])).
% 1.66/0.62  fof(f124,plain,(
% 1.66/0.62    spl4_1 | spl4_2),
% 1.66/0.62    inference(avatar_split_clause,[],[f115,f121,f117])).
% 1.66/0.62  fof(f115,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 1.66/0.62    inference(subsumption_resolution,[],[f114,f99])).
% 1.66/0.62  fof(f114,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~sP3(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 1.66/0.62    inference(subsumption_resolution,[],[f113,f82])).
% 1.66/0.62  fof(f113,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~sP3(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 1.66/0.62    inference(subsumption_resolution,[],[f100,f84])).
% 1.66/0.62  fof(f100,plain,(
% 1.66/0.62    r3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0)),sK2,sK2) | ~l1_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~v3_orders_2(g1_orders_2(sK0,k1_yellow_1(sK0))) | v2_struct_0(g1_orders_2(sK0,k1_yellow_1(sK0))) | ~sP3(g1_orders_2(sK0,k1_yellow_1(sK0)))),
% 1.66/0.62    inference(resolution,[],[f77,f92])).
% 1.66/0.62  % SZS output end Proof for theBenchmark
% 1.66/0.62  % (22060)------------------------------
% 1.66/0.62  % (22060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.62  % (22060)Termination reason: Refutation
% 1.66/0.62  
% 1.66/0.62  % (22060)Memory used [KB]: 11129
% 1.66/0.62  % (22060)Time elapsed: 0.160 s
% 1.66/0.62  % (22060)------------------------------
% 1.66/0.62  % (22060)------------------------------
% 1.66/0.62  % (22051)Success in time 0.253 s
%------------------------------------------------------------------------------
