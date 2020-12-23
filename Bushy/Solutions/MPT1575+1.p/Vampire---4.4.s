%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t53_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:45 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 130 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   21
%              Number of atoms          :  375 ( 788 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f437,plain,(
    $false ),
    inference(subsumption_resolution,[],[f436,f74])).

fof(f74,plain,(
    ~ v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ~ v3_lattice3(sK0)
    & ! [X1] :
        ( r1_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f54])).

fof(f54,plain,
    ( ? [X0] :
        ( ~ v3_lattice3(X0)
        & ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ~ v3_lattice3(sK0)
      & ! [X1] :
          ( r1_yellow_0(sK0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ~ v3_lattice3(X0)
      & ! [X1] :
          ( r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ~ v3_lattice3(X0)
      & ! [X1] :
          ( r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_yellow_0(X0,X1) )
         => v3_lattice3(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_yellow_0(X0,X1) )
       => v3_lattice3(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',t53_yellow_0)).

fof(f436,plain,(
    v3_lattice3(sK0) ),
    inference(subsumption_resolution,[],[f434,f72])).

fof(f72,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f434,plain,
    ( ~ l1_orders_2(sK0)
    | v3_lattice3(sK0) ),
    inference(resolution,[],[f428,f162])).

fof(f162,plain,(
    ! [X0] : r1_yellow_0(sK0,X0) ),
    inference(subsumption_resolution,[],[f161,f71])).

fof(f71,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f161,plain,(
    ! [X0] :
      ( r1_yellow_0(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f157,f72])).

fof(f157,plain,(
    ! [X0] :
      ( r1_yellow_0(sK0,X0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f147,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
      | r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r2_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
            | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r2_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
            | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,X1)
           => r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r1_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
           => r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',t50_yellow_0)).

fof(f147,plain,(
    ! [X0] : r1_yellow_0(sK0,k3_xboole_0(X0,u1_struct_0(sK0))) ),
    inference(superposition,[],[f121,f95])).

fof(f95,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',commutativity_k3_xboole_0)).

fof(f121,plain,(
    ! [X0] : r1_yellow_0(sK0,k3_xboole_0(u1_struct_0(sK0),X0)) ),
    inference(resolution,[],[f120,f94])).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',t17_xboole_1)).

fof(f120,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | r1_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f100,f73])).

fof(f73,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_yellow_0(sK0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',t3_subset)).

fof(f428,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(X0,sK1(X0))
      | ~ l1_orders_2(X0)
      | v3_lattice3(X0) ) ),
    inference(subsumption_resolution,[],[f427,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',dt_k1_yellow_0)).

fof(f427,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(X0,sK1(X0))
      | ~ l1_orders_2(X0)
      | v3_lattice3(X0)
      | ~ m1_subset_1(k1_yellow_0(X0,sK1(X0)),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f426,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f107,f96])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                & r2_lattice3(X0,X1,sK4(X0,X1,X2))
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f64,f65])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',d9_yellow_0)).

fof(f426,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(X0,sK1(X0))
      | ~ l1_orders_2(X0)
      | v3_lattice3(X0)
      | ~ r2_lattice3(X0,sK1(X0),k1_yellow_0(X0,sK1(X0)))
      | ~ m1_subset_1(k1_yellow_0(X0,sK1(X0)),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f425])).

fof(f425,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(X0,sK1(X0))
      | ~ l1_orders_2(X0)
      | v3_lattice3(X0)
      | ~ r2_lattice3(X0,sK1(X0),k1_yellow_0(X0,sK1(X0)))
      | v3_lattice3(X0)
      | ~ r2_lattice3(X0,sK1(X0),k1_yellow_0(X0,sK1(X0)))
      | ~ m1_subset_1(k1_yellow_0(X0,sK1(X0)),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f319,f81])).

fof(f81,plain,(
    ! [X2,X0] :
      ( r2_lattice3(X0,sK1(X0),sK2(X0,X2))
      | v3_lattice3(X0)
      | ~ r2_lattice3(X0,sK1(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ! [X2] :
              ( ( ~ r1_orders_2(X0,X2,sK2(X0,X2))
                & r2_lattice3(X0,sK1(X0),sK2(X0,X2))
                & m1_subset_1(sK2(X0,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,sK1(X0),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X6] :
                  ( r1_orders_2(X0,sK3(X0,X4),X6)
                  | ~ r2_lattice3(X0,X4,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r2_lattice3(X0,X4,sK3(X0,X4))
              & m1_subset_1(sK3(X0,X4),u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f57,f60,f59,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,X1,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,X1,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,sK1(X0),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_lattice3(X0,sK1(X0),X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X1,X2,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK2(X0,X2))
        & r2_lattice3(X0,X1,sK2(X0,X2))
        & m1_subset_1(sK2(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_orders_2(X0,X5,X6)
              | ~ r2_lattice3(X0,X4,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r2_lattice3(X0,X4,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_orders_2(X0,sK3(X0,X4),X6)
            | ~ r2_lattice3(X0,X4,X6)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r2_lattice3(X0,X4,sK3(X0,X4))
        & m1_subset_1(sK3(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
            ? [X5] :
              ( ! [X6] :
                  ( r1_orders_2(X0,X5,X6)
                  | ~ r2_lattice3(X0,X4,X6)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r2_lattice3(X0,X4,X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X1] :
            ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v3_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                 => r1_orders_2(X0,X2,X3) ) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t53_yellow_0.p',d12_lattice3)).

fof(f319,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(X0,X1,sK2(X0,k1_yellow_0(X0,X1)))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v3_lattice3(X0)
      | ~ r2_lattice3(X0,sK1(X0),k1_yellow_0(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f318,f96])).

fof(f318,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,sK2(X0,k1_yellow_0(X0,X1)))
      | ~ l1_orders_2(X0)
      | v3_lattice3(X0)
      | ~ r2_lattice3(X0,sK1(X0),k1_yellow_0(X0,X1))
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f317,f80])).

fof(f80,plain,(
    ! [X2,X0] :
      ( m1_subset_1(sK2(X0,X2),u1_struct_0(X0))
      | v3_lattice3(X0)
      | ~ r2_lattice3(X0,sK1(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f317,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2(X0,k1_yellow_0(X0,X1)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,sK2(X0,k1_yellow_0(X0,X1)))
      | ~ l1_orders_2(X0)
      | v3_lattice3(X0)
      | ~ r2_lattice3(X0,sK1(X0),k1_yellow_0(X0,X1))
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2(X0,k1_yellow_0(X0,X1)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,sK2(X0,k1_yellow_0(X0,X1)))
      | ~ l1_orders_2(X0)
      | v3_lattice3(X0)
      | ~ r2_lattice3(X0,sK1(X0),k1_yellow_0(X0,X1))
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f195,f82])).

fof(f82,plain,(
    ! [X2,X0] :
      ( ~ r1_orders_2(X0,X2,sK2(X0,X2))
      | v3_lattice3(X0)
      | ~ r2_lattice3(X0,sK1(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X2)
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f106,f96])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f66])).
%------------------------------------------------------------------------------
