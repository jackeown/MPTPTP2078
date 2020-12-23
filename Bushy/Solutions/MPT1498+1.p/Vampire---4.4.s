%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattice3__t31_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:54 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   63 (1000 expanded)
%              Number of leaves         :    7 ( 264 expanded)
%              Depth                    :   27
%              Number of atoms          :  252 (6782 expanded)
%              Number of equality atoms :   16 (  96 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(subsumption_resolution,[],[f161,f154])).

fof(f154,plain,(
    ~ r4_lattice3(sK1,sK2,sK0) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,
    ( ~ r4_lattice3(sK1,sK2,sK0)
    | ~ r4_lattice3(sK1,sK2,sK0) ),
    inference(resolution,[],[f137,f118])).

fof(f118,plain,
    ( ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | ~ r4_lattice3(sK1,sK2,sK0) ),
    inference(backward_demodulation,[],[f116,f69])).

fof(f69,plain,
    ( ~ r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
    | ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( ~ r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
      | ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2) )
    & ( r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
      | r2_lattice3(k3_lattice3(sK1),sK0,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1)))
    & l3_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f55,f57,f56])).

fof(f56,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r4_lattice3(X1,k5_lattice3(X1,X2),X0)
              | ~ r2_lattice3(k3_lattice3(X1),X0,X2) )
            & ( r4_lattice3(X1,k5_lattice3(X1,X2),X0)
              | r2_lattice3(k3_lattice3(X1),X0,X2) )
            & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
        & l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ r4_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
            | ~ r2_lattice3(k3_lattice3(sK1),sK0,X2) )
          & ( r4_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
            | r2_lattice3(k3_lattice3(sK1),sK0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(sK1))) )
      & l3_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | ~ r2_lattice3(k3_lattice3(X1),X0,X2) )
          & ( r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | r2_lattice3(k3_lattice3(X1),X0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
     => ( ( ~ r4_lattice3(X1,k5_lattice3(X1,sK2),X0)
          | ~ r2_lattice3(k3_lattice3(X1),X0,sK2) )
        & ( r4_lattice3(X1,k5_lattice3(X1,sK2),X0)
          | r2_lattice3(k3_lattice3(X1),X0,sK2) )
        & m1_subset_1(sK2,u1_struct_0(k3_lattice3(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | ~ r2_lattice3(k3_lattice3(X1),X0,X2) )
          & ( r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | r2_lattice3(k3_lattice3(X1),X0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | ~ r2_lattice3(k3_lattice3(X1),X0,X2) )
          & ( r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | r2_lattice3(k3_lattice3(X1),X0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_lattice3(k3_lattice3(X1),X0,X2)
          <~> r4_lattice3(X1,k5_lattice3(X1,X2),X0) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_lattice3(k3_lattice3(X1),X0,X2)
          <~> r4_lattice3(X1,k5_lattice3(X1,X2),X0) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
           => ( r2_lattice3(k3_lattice3(X1),X0,X2)
            <=> r4_lattice3(X1,k5_lattice3(X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
         => ( r2_lattice3(k3_lattice3(X1),X0,X2)
          <=> r4_lattice3(X1,k5_lattice3(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t31_lattice3.p',t31_lattice3)).

fof(f116,plain,(
    k5_lattice3(sK1,sK2) = sK2 ),
    inference(subsumption_resolution,[],[f115,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f115,plain,
    ( k5_lattice3(sK1,sK2) = sK2
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f114,f65])).

fof(f65,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f114,plain,
    ( k5_lattice3(sK1,sK2) = sK2
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f108,f66])).

fof(f66,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f108,plain,
    ( k5_lattice3(sK1,sK2) = sK2
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f67,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k5_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
         => k5_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t31_lattice3.p',d4_lattice3)).

fof(f67,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) ),
    inference(cnf_transformation,[],[f58])).

fof(f137,plain,(
    ! [X0] :
      ( r2_lattice3(k3_lattice3(sK1),X0,sK2)
      | ~ r4_lattice3(sK1,sK2,X0) ) ),
    inference(forward_demodulation,[],[f136,f129])).

fof(f129,plain,(
    k4_lattice3(sK1,sK2) = sK2 ),
    inference(subsumption_resolution,[],[f128,f64])).

fof(f128,plain,
    ( k4_lattice3(sK1,sK2) = sK2
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f127,f65])).

fof(f127,plain,
    ( k4_lattice3(sK1,sK2) = sK2
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f123,f66])).

fof(f123,plain,
    ( k4_lattice3(sK1,sK2) = sK2
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f122,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t31_lattice3.p',d3_lattice3)).

fof(f122,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f121,f116])).

fof(f121,plain,(
    m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f120,f64])).

fof(f120,plain,
    ( m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f119,f65])).

fof(f119,plain,
    ( m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1))
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f109,f66])).

fof(f109,plain,
    ( m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f67,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t31_lattice3.p',dt_k5_lattice3)).

fof(f136,plain,(
    ! [X0] :
      ( r2_lattice3(k3_lattice3(sK1),X0,k4_lattice3(sK1,sK2))
      | ~ r4_lattice3(sK1,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f135,f64])).

fof(f135,plain,(
    ! [X0] :
      ( r2_lattice3(k3_lattice3(sK1),X0,k4_lattice3(sK1,sK2))
      | ~ r4_lattice3(sK1,sK2,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f134,f65])).

fof(f134,plain,(
    ! [X0] :
      ( r2_lattice3(k3_lattice3(sK1),X0,k4_lattice3(sK1,sK2))
      | ~ r4_lattice3(sK1,sK2,X0)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f125,f66])).

fof(f125,plain,(
    ! [X0] :
      ( r2_lattice3(k3_lattice3(sK1),X0,k4_lattice3(sK1,sK2))
      | ~ r4_lattice3(sK1,sK2,X0)
      | ~ l3_lattices(sK1)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f122,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r4_lattice3(X1,X2,X0)
              | ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
            & ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
              | ~ r4_lattice3(X1,X2,X0) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r4_lattice3(X1,X2,X0)
          <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t31_lattice3.p',t30_lattice3)).

fof(f161,plain,(
    r4_lattice3(sK1,sK2,sK0) ),
    inference(resolution,[],[f160,f117])).

fof(f117,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | r4_lattice3(sK1,sK2,sK0) ),
    inference(backward_demodulation,[],[f116,f68])).

fof(f68,plain,
    ( r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
    | r2_lattice3(k3_lattice3(sK1),sK0,sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f160,plain,(
    ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2) ),
    inference(forward_demodulation,[],[f159,f129])).

fof(f159,plain,(
    ~ r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f158,f64])).

fof(f158,plain,
    ( ~ r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f157,f65])).

fof(f157,plain,
    ( ~ r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f156,f66])).

fof(f156,plain,
    ( ~ r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f155,f122])).

fof(f155,plain,
    ( ~ r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f154,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,X2,X0)
      | ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
