%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 227 expanded)
%              Number of leaves         :   11 (  62 expanded)
%              Depth                    :   22
%              Number of atoms          :  227 (1106 expanded)
%              Number of equality atoms :   36 (  68 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f233,plain,(
    $false ),
    inference(subsumption_resolution,[],[f232,f34])).

fof(f34,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattice3)).

fof(f232,plain,(
    ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(resolution,[],[f163,f35])).

fof(f35,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f163,plain,(
    ~ l2_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f161,f46])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f161,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ l2_lattices(k1_lattice3(sK0)) ),
    inference(superposition,[],[f144,f87])).

fof(f87,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ l2_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f86,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f86,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | r1_tarski(sK1,sK2)
    | ~ l2_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f85,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | ~ r1_lattices(k1_lattice3(sK0),sK1,sK2) )
    & ( r1_tarski(sK1,sK2)
      | r1_lattices(k1_lattice3(sK0),sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_lattices(k1_lattice3(X0),X1,X2) )
            & ( r1_tarski(X1,X2)
              | r1_lattices(k1_lattice3(X0),X1,X2) )
            & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
        & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,X2)
            | ~ r1_lattices(k1_lattice3(sK0),sK1,X2) )
          & ( r1_tarski(sK1,X2)
            | r1_lattices(k1_lattice3(sK0),sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(k1_lattice3(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,X2)
          | ~ r1_lattices(k1_lattice3(sK0),sK1,X2) )
        & ( r1_tarski(sK1,X2)
          | r1_lattices(k1_lattice3(sK0),sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(k1_lattice3(sK0))) )
   => ( ( ~ r1_tarski(sK1,sK2)
        | ~ r1_lattices(k1_lattice3(sK0),sK1,sK2) )
      & ( r1_tarski(sK1,sK2)
        | r1_lattices(k1_lattice3(sK0),sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_lattices(k1_lattice3(X0),X1,X2) )
          & ( r1_tarski(X1,X2)
            | r1_lattices(k1_lattice3(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_lattices(k1_lattice3(X0),X1,X2) )
          & ( r1_tarski(X1,X2)
            | r1_lattices(k1_lattice3(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_lattices(k1_lattice3(X0),X1,X2)
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
           => ( r1_lattices(k1_lattice3(X0),X1,X2)
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
         => ( r1_lattices(k1_lattice3(X0),X1,X2)
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_lattice3)).

fof(f85,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | r1_tarski(sK1,sK2)
    | ~ l2_lattices(k1_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f80,f30])).

fof(f30,plain,(
    m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | r1_tarski(sK1,sK2)
    | ~ l2_lattices(k1_lattice3(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    inference(superposition,[],[f74,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(k1_lattice3(X0),X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_lattices(k1_lattice3(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k1_lattices(k1_lattice3(X0),X1,X2) = k2_xboole_0(X1,X2) )
          | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
         => ( k2_lattices(k1_lattice3(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k1_lattices(k1_lattice3(X0),X1,X2) = k2_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_lattice3)).

fof(f74,plain,
    ( sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2)
    | r1_tarski(sK1,sK2)
    | ~ l2_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f73,f33])).

fof(f33,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_lattices(k1_lattice3(X0))
      & ~ v2_struct_0(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_lattice3)).

fof(f73,plain,
    ( r1_tarski(sK1,sK2)
    | sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ l2_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f72,f29])).

fof(f72,plain,
    ( r1_tarski(sK1,sK2)
    | sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ l2_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f71,f30])).

fof(f71,plain,
    ( r1_tarski(sK1,sK2)
    | sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ l2_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(resolution,[],[f31,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

fof(f31,plain,
    ( r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f144,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(sK1,X0),sK2) ),
    inference(resolution,[],[f131,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f131,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f130,f34])).

fof(f130,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ l3_lattices(k1_lattice3(sK0)) ),
    inference(resolution,[],[f100,f35])).

fof(f100,plain,
    ( ~ l2_lattices(k1_lattice3(sK0))
    | ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f99,f87])).

fof(f99,plain,
    ( sK2 != k2_xboole_0(sK1,sK2)
    | ~ r1_tarski(sK1,sK2)
    | ~ l2_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f98,f29])).

fof(f98,plain,
    ( sK2 != k2_xboole_0(sK1,sK2)
    | ~ r1_tarski(sK1,sK2)
    | ~ l2_lattices(k1_lattice3(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    inference(subsumption_resolution,[],[f93,f30])).

fof(f93,plain,
    ( sK2 != k2_xboole_0(sK1,sK2)
    | ~ r1_tarski(sK1,sK2)
    | ~ l2_lattices(k1_lattice3(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) ),
    inference(superposition,[],[f79,f39])).

fof(f79,plain,
    ( sK2 != k1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ r1_tarski(sK1,sK2)
    | ~ l2_lattices(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f78,f33])).

fof(f78,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK2 != k1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ l2_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f77,f29])).

fof(f77,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK2 != k1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ l2_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(subsumption_resolution,[],[f76,f30])).

fof(f76,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK2 != k1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))
    | ~ l2_lattices(k1_lattice3(sK0))
    | v2_struct_0(k1_lattice3(sK0)) ),
    inference(resolution,[],[f32,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f32,plain,
    ( ~ r1_lattices(k1_lattice3(sK0),sK1,sK2)
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (27294)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.47  % (27294)Refutation not found, incomplete strategy% (27294)------------------------------
% 0.21/0.47  % (27294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (27301)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.47  % (27294)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (27294)Memory used [KB]: 10490
% 0.21/0.47  % (27294)Time elapsed: 0.051 s
% 0.21/0.47  % (27294)------------------------------
% 0.21/0.47  % (27294)------------------------------
% 0.21/0.48  % (27301)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f232,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0] : (l3_lattices(k1_lattice3(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : l3_lattices(k1_lattice3(X0))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (l3_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattice3)).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ~l3_lattices(k1_lattice3(sK0))),
% 0.21/0.48    inference(resolution,[],[f163,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ~l2_lattices(k1_lattice3(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f161,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    ~r1_tarski(sK2,sK2) | ~l2_lattices(k1_lattice3(sK0))),
% 0.21/0.48    inference(superposition,[],[f144,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    sK2 = k2_xboole_0(sK1,sK2) | ~l2_lattices(k1_lattice3(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f86,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    sK2 = k2_xboole_0(sK1,sK2) | r1_tarski(sK1,sK2) | ~l2_lattices(k1_lattice3(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ((~r1_tarski(sK1,sK2) | ~r1_lattices(k1_lattice3(sK0),sK1,sK2)) & (r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))) & m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f24,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_lattices(k1_lattice3(X0),X1,X2)) & (r1_tarski(X1,X2) | r1_lattices(k1_lattice3(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))) => (? [X2] : ((~r1_tarski(sK1,X2) | ~r1_lattices(k1_lattice3(sK0),sK1,X2)) & (r1_tarski(sK1,X2) | r1_lattices(k1_lattice3(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k1_lattice3(sK0)))) & m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X2] : ((~r1_tarski(sK1,X2) | ~r1_lattices(k1_lattice3(sK0),sK1,X2)) & (r1_tarski(sK1,X2) | r1_lattices(k1_lattice3(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k1_lattice3(sK0)))) => ((~r1_tarski(sK1,sK2) | ~r1_lattices(k1_lattice3(sK0),sK1,sK2)) & (r1_tarski(sK1,sK2) | r1_lattices(k1_lattice3(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_lattices(k1_lattice3(X0),X1,X2)) & (r1_tarski(X1,X2) | r1_lattices(k1_lattice3(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r1_lattices(k1_lattice3(X0),X1,X2)) & (r1_tarski(X1,X2) | r1_lattices(k1_lattice3(X0),X1,X2))) & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))))),
% 0.21/0.48    inference(nnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((r1_lattices(k1_lattice3(X0),X1,X2) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) => (r1_lattices(k1_lattice3(X0),X1,X2) <=> r1_tarski(X1,X2))))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) => (r1_lattices(k1_lattice3(X0),X1,X2) <=> r1_tarski(X1,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_lattice3)).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    sK2 = k2_xboole_0(sK1,sK2) | r1_tarski(sK1,sK2) | ~l2_lattices(k1_lattice3(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f80,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    sK2 = k2_xboole_0(sK1,sK2) | r1_tarski(sK1,sK2) | ~l2_lattices(k1_lattice3(sK0)) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))),
% 0.21/0.48    inference(superposition,[],[f74,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_lattices(k1_lattice3(X0),X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((k2_lattices(k1_lattice3(X0),X1,X2) = k3_xboole_0(X1,X2) & k1_lattices(k1_lattice3(X0),X1,X2) = k2_xboole_0(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) => (k2_lattices(k1_lattice3(X0),X1,X2) = k3_xboole_0(X1,X2) & k1_lattices(k1_lattice3(X0),X1,X2) = k2_xboole_0(X1,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_lattice3)).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2) | r1_tarski(sK1,sK2) | ~l2_lattices(k1_lattice3(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f73,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_struct_0(k1_lattice3(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : ~v2_struct_0(k1_lattice3(X0))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (v3_lattices(k1_lattice3(X0)) & ~v2_struct_0(k1_lattice3(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_lattice3)).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2) | sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2) | ~l2_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f72,f29])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2) | sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~l2_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f71,f30])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2) | sK2 = k1_lattices(k1_lattice3(sK0),sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~l2_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0))),
% 0.21/0.48    inference(resolution,[],[f31,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    r1_lattices(k1_lattice3(sK0),sK1,sK2) | r1_tarski(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK1,X0),sK2)) )),
% 0.21/0.48    inference(resolution,[],[f131,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ~r1_tarski(sK1,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f130,f34])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ~r1_tarski(sK1,sK2) | ~l3_lattices(k1_lattice3(sK0))),
% 0.21/0.48    inference(resolution,[],[f100,f35])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ~l2_lattices(k1_lattice3(sK0)) | ~r1_tarski(sK1,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f99,f87])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    sK2 != k2_xboole_0(sK1,sK2) | ~r1_tarski(sK1,sK2) | ~l2_lattices(k1_lattice3(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f98,f29])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    sK2 != k2_xboole_0(sK1,sK2) | ~r1_tarski(sK1,sK2) | ~l2_lattices(k1_lattice3(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f93,f30])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    sK2 != k2_xboole_0(sK1,sK2) | ~r1_tarski(sK1,sK2) | ~l2_lattices(k1_lattice3(sK0)) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0)))),
% 0.21/0.48    inference(superposition,[],[f79,f39])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    sK2 != k1_lattices(k1_lattice3(sK0),sK1,sK2) | ~r1_tarski(sK1,sK2) | ~l2_lattices(k1_lattice3(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f78,f33])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ~r1_tarski(sK1,sK2) | sK2 != k1_lattices(k1_lattice3(sK0),sK1,sK2) | ~l2_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f77,f29])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ~r1_tarski(sK1,sK2) | sK2 != k1_lattices(k1_lattice3(sK0),sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~l2_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f76,f30])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ~r1_tarski(sK1,sK2) | sK2 != k1_lattices(k1_lattice3(sK0),sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k1_lattice3(sK0))) | ~l2_lattices(k1_lattice3(sK0)) | v2_struct_0(k1_lattice3(sK0))),
% 0.21/0.48    inference(resolution,[],[f32,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ~r1_lattices(k1_lattice3(sK0),sK1,sK2) | ~r1_tarski(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (27301)------------------------------
% 0.21/0.48  % (27301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27301)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (27301)Memory used [KB]: 1663
% 0.21/0.48  % (27301)Time elapsed: 0.064 s
% 0.21/0.48  % (27301)------------------------------
% 0.21/0.48  % (27301)------------------------------
% 0.21/0.48  % (27282)Success in time 0.125 s
%------------------------------------------------------------------------------
