%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1517+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:00 EST 2020

% Result     : Theorem 32.80s
% Output     : Refutation 32.80s
% Verified   : 
% Statistics : Number of formulae       :  249 (4061 expanded)
%              Number of leaves         :   21 ( 965 expanded)
%              Depth                    :   33
%              Number of atoms          : 1232 (30393 expanded)
%              Number of equality atoms :  171 (3444 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112437,plain,(
    $false ),
    inference(subsumption_resolution,[],[f112436,f70755])).

fof(f70755,plain,(
    m1_subset_1(sK2(sK0,k15_lattice3(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    inference(superposition,[],[f12160,f70503])).

fof(f70503,plain,(
    k15_lattice3(sK0,u1_struct_0(sK0)) = k3_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f70502,f177])).

fof(f177,plain,(
    ! [X6] : m1_subset_1(k15_lattice3(sK0,X6),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f157,f65])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( k6_lattices(sK0) != k15_lattice3(sK0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v14_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f53])).

fof(f53,plain,
    ( ? [X0] :
        ( ( k6_lattices(X0) != k15_lattice3(X0,u1_struct_0(X0))
          | ~ l3_lattices(X0)
          | ~ v14_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k6_lattices(sK0) != k15_lattice3(sK0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v14_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ( k6_lattices(X0) != k15_lattice3(X0,u1_struct_0(X0))
        | ~ l3_lattices(X0)
        | ~ v14_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ( k6_lattices(X0) != k15_lattice3(X0,u1_struct_0(X0))
        | ~ l3_lattices(X0)
        | ~ v14_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( k6_lattices(X0) = k15_lattice3(X0,u1_struct_0(X0))
          & l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( k6_lattices(X0) = k15_lattice3(X0,u1_struct_0(X0))
        & l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_lattice3)).

fof(f157,plain,(
    ! [X6] :
      ( m1_subset_1(k15_lattice3(sK0,X6),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f68,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f68,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f70502,plain,
    ( k15_lattice3(sK0,u1_struct_0(sK0)) = k3_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),k6_lattices(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f69959,f199])).

fof(f199,plain,(
    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f185,f65])).

fof(f185,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f148,f83])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f148,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f68,f70])).

fof(f70,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f69959,plain,
    ( k15_lattice3(sK0,u1_struct_0(sK0)) = k3_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),k6_lattices(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(superposition,[],[f40862,f364])).

fof(f364,plain,(
    ! [X15] :
      ( k3_lattices(sK0,X15,k6_lattices(sK0)) = k1_lattices(sK0,X15,k6_lattices(sK0))
      | ~ m1_subset_1(X15,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f363,f65])).

fof(f363,plain,(
    ! [X15] :
      ( k3_lattices(sK0,X15,k6_lattices(sK0)) = k1_lattices(sK0,X15,k6_lattices(sK0))
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f362,f161])).

fof(f161,plain,(
    v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f160,f65])).

fof(f160,plain,
    ( v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f149,f66])).

fof(f66,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f149,plain,
    ( v4_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f362,plain,(
    ! [X15] :
      ( k3_lattices(sK0,X15,k6_lattices(sK0)) = k1_lattices(sK0,X15,k6_lattices(sK0))
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f287,f148])).

fof(f287,plain,(
    ! [X15] :
      ( k3_lattices(sK0,X15,k6_lattices(sK0)) = k1_lattices(sK0,X15,k6_lattices(sK0))
      | ~ m1_subset_1(X15,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f199,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f40862,plain,(
    ! [X3] :
      ( k15_lattice3(sK0,u1_struct_0(sK0)) = k1_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f40861,f480])).

fof(f480,plain,(
    ! [X35,X34] :
      ( m1_subset_1(k1_lattices(sK0,k15_lattice3(sK0,X34),X35),u1_struct_0(sK0))
      | ~ m1_subset_1(X35,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f479,f65])).

fof(f479,plain,(
    ! [X35,X34] :
      ( m1_subset_1(k1_lattices(sK0,k15_lattice3(sK0,X34),X35),u1_struct_0(sK0))
      | ~ m1_subset_1(X35,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f404,f148])).

fof(f404,plain,(
    ! [X35,X34] :
      ( m1_subset_1(k1_lattices(sK0,k15_lattice3(sK0,X34),X35),u1_struct_0(sK0))
      | ~ m1_subset_1(X35,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f177,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattices)).

fof(f40861,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X3),u1_struct_0(sK0))
      | k15_lattice3(sK0,u1_struct_0(sK0)) = k1_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X3) ) ),
    inference(subsumption_resolution,[],[f40860,f65])).

fof(f40860,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X3),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k15_lattice3(sK0,u1_struct_0(sK0)) = k1_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X3) ) ),
    inference(subsumption_resolution,[],[f40859,f66])).

fof(f40859,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X3),u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | k15_lattice3(sK0,u1_struct_0(sK0)) = k1_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X3) ) ),
    inference(subsumption_resolution,[],[f40858,f67])).

fof(f67,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f40858,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X3),u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | k15_lattice3(sK0,u1_struct_0(sK0)) = k1_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X3) ) ),
    inference(subsumption_resolution,[],[f40857,f68])).

fof(f40857,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X3),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | k15_lattice3(sK0,u1_struct_0(sK0)) = k1_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X3) ) ),
    inference(subsumption_resolution,[],[f40851,f177])).

fof(f40851,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
      | ~ m1_subset_1(k1_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X3),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | k15_lattice3(sK0,u1_struct_0(sK0)) = k1_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X3) ) ),
    inference(duplicate_literal_removal,[],[f40732])).

fof(f40732,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
      | ~ m1_subset_1(k1_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X3),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | k15_lattice3(sK0,u1_struct_0(sK0)) = k1_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f3080,f4413])).

fof(f4413,plain,(
    ! [X14,X13] :
      ( ~ r3_lattices(sK0,k1_lattices(sK0,k15_lattice3(sK0,X13),X14),k15_lattice3(sK0,X13))
      | k15_lattice3(sK0,X13) = k1_lattices(sK0,k15_lattice3(sK0,X13),X14)
      | ~ m1_subset_1(X14,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f4412,f480])).

fof(f4412,plain,(
    ! [X14,X13] :
      ( k15_lattice3(sK0,X13) = k1_lattices(sK0,k15_lattice3(sK0,X13),X14)
      | ~ m1_subset_1(k1_lattices(sK0,k15_lattice3(sK0,X13),X14),u1_struct_0(sK0))
      | ~ r3_lattices(sK0,k1_lattices(sK0,k15_lattice3(sK0,X13),X14),k15_lattice3(sK0,X13))
      | ~ m1_subset_1(X14,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f4384,f177])).

fof(f4384,plain,(
    ! [X14,X13] :
      ( k15_lattice3(sK0,X13) = k1_lattices(sK0,k15_lattice3(sK0,X13),X14)
      | ~ m1_subset_1(k1_lattices(sK0,k15_lattice3(sK0,X13),X14),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X13),u1_struct_0(sK0))
      | ~ r3_lattices(sK0,k1_lattices(sK0,k15_lattice3(sK0,X13),X14),k15_lattice3(sK0,X13))
      | ~ m1_subset_1(X14,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f1501,f414])).

fof(f414,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k15_lattice3(sK0,X0),k1_lattices(sK0,k15_lattice3(sK0,X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f413,f65])).

fof(f413,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k15_lattice3(sK0,X0),k1_lattices(sK0,k15_lattice3(sK0,X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f412,f163])).

fof(f163,plain,(
    v5_lattices(sK0) ),
    inference(subsumption_resolution,[],[f162,f65])).

fof(f162,plain,
    ( v5_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f150,f66])).

fof(f150,plain,
    ( v5_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f412,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k15_lattice3(sK0,X0),k1_lattices(sK0,k15_lattice3(sK0,X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f411,f165])).

fof(f165,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f164,f65])).

fof(f164,plain,
    ( v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f151,f66])).

fof(f151,plain,
    ( v6_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f411,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k15_lattice3(sK0,X0),k1_lattices(sK0,k15_lattice3(sK0,X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f410,f167])).

fof(f167,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f166,f65])).

fof(f166,plain,
    ( v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f152,f66])).

fof(f152,plain,
    ( v8_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f410,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k15_lattice3(sK0,X0),k1_lattices(sK0,k15_lattice3(sK0,X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f409,f169])).

fof(f169,plain,(
    v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f168,f65])).

fof(f168,plain,
    ( v9_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f153,f66])).

fof(f153,plain,
    ( v9_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f409,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k15_lattice3(sK0,X0),k1_lattices(sK0,k15_lattice3(sK0,X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f384,f68])).

fof(f384,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k15_lattice3(sK0,X0),k1_lattices(sK0,k15_lattice3(sK0,X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f177,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_lattices)).

fof(f1501,plain,(
    ! [X2,X3] :
      ( ~ r1_lattices(sK0,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X3,X2) ) ),
    inference(subsumption_resolution,[],[f1500,f65])).

fof(f1500,plain,(
    ! [X2,X3] :
      ( X2 = X3
      | ~ r1_lattices(sK0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X3,X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1499,f165])).

fof(f1499,plain,(
    ! [X2,X3] :
      ( X2 = X3
      | ~ r1_lattices(sK0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X3,X2)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1498,f167])).

fof(f1498,plain,(
    ! [X2,X3] :
      ( X2 = X3
      | ~ r1_lattices(sK0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X3,X2)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1497,f169])).

fof(f1497,plain,(
    ! [X2,X3] :
      ( X2 = X3
      | ~ r1_lattices(sK0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X3,X2)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1488,f68])).

fof(f1488,plain,(
    ! [X2,X3] :
      ( X2 = X3
      | ~ r1_lattices(sK0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X3,X2)
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1487])).

fof(f1487,plain,(
    ! [X2,X3] :
      ( X2 = X3
      | ~ r1_lattices(sK0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f1485,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f1485,plain,(
    ! [X6,X7] :
      ( ~ r1_lattices(sK0,X7,X6)
      | X6 = X7
      | ~ r1_lattices(sK0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1484,f161])).

fof(f1484,plain,(
    ! [X6,X7] :
      ( X6 = X7
      | ~ r1_lattices(sK0,X7,X6)
      | ~ r1_lattices(sK0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ v4_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f111,f148])).

fof(f111,plain,(
    ! [X6,X7] :
      ( X6 = X7
      | ~ r1_lattices(sK0,X7,X6)
      | ~ r1_lattices(sK0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0) ) ),
    inference(resolution,[],[f65,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_lattices(X0,X2,X1)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

fof(f3080,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X2,k1_lattices(sK0,X0,X1),k15_lattice3(X2,u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k1_lattices(sK0,X0,X1),u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f943,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

fof(f943,plain,(
    ! [X66,X67] :
      ( r2_hidden(k1_lattices(sK0,X67,X66),u1_struct_0(sK0))
      | ~ m1_subset_1(X67,u1_struct_0(sK0))
      | ~ m1_subset_1(X66,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f848,f264])).

fof(f264,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f263,f65])).

fof(f263,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f183,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f183,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f148,f77])).

fof(f77,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l2_lattices)).

fof(f848,plain,(
    ! [X66,X67] :
      ( ~ m1_subset_1(X66,u1_struct_0(sK0))
      | ~ m1_subset_1(X67,u1_struct_0(sK0))
      | r2_hidden(k1_lattices(sK0,X67,X66),u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f822,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f822,plain,(
    ! [X24,X23] :
      ( m1_subset_1(k1_lattices(sK0,X23,X24),u1_struct_0(sK0))
      | ~ m1_subset_1(X24,u1_struct_0(sK0))
      | ~ m1_subset_1(X23,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f125,f148])).

fof(f125,plain,(
    ! [X24,X23] :
      ( m1_subset_1(k1_lattices(sK0,X23,X24),u1_struct_0(sK0))
      | ~ m1_subset_1(X24,u1_struct_0(sK0))
      | ~ m1_subset_1(X23,u1_struct_0(sK0))
      | ~ l2_lattices(sK0) ) ),
    inference(resolution,[],[f65,f99])).

fof(f12160,plain,(
    ! [X9] : m1_subset_1(sK2(sK0,k3_lattices(sK0,k15_lattice3(sK0,X9),k6_lattices(sK0))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f12159,f177])).

fof(f12159,plain,(
    ! [X9] :
      ( m1_subset_1(sK2(sK0,k3_lattices(sK0,k15_lattice3(sK0,X9),k6_lattices(sK0))),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X9),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f12073,f199])).

fof(f12073,plain,(
    ! [X9] :
      ( m1_subset_1(sK2(sK0,k3_lattices(sK0,k15_lattice3(sK0,X9),k6_lattices(sK0))),u1_struct_0(sK0))
      | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X9),u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f12040,f364])).

fof(f12040,plain,(
    ! [X28,X29] :
      ( m1_subset_1(sK2(sK0,k1_lattices(sK0,k15_lattice3(sK0,X29),X28)),u1_struct_0(sK0))
      | ~ m1_subset_1(X28,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f2129,f9354])).

fof(f9354,plain,(
    ~ v14_lattices(sK0) ),
    inference(subsumption_resolution,[],[f9353,f600])).

fof(f600,plain,
    ( r2_hidden(sK3(sK0),u1_struct_0(sK0))
    | ~ v14_lattices(sK0) ),
    inference(subsumption_resolution,[],[f517,f264])).

fof(f517,plain,
    ( ~ v14_lattices(sK0)
    | r2_hidden(sK3(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f492,f93])).

fof(f492,plain,
    ( m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v14_lattices(sK0) ),
    inference(subsumption_resolution,[],[f115,f148])).

fof(f115,plain,
    ( m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v14_lattices(sK0)
    | ~ l2_lattices(sK0) ),
    inference(resolution,[],[f65,f88])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v14_lattices(X0)
          | ! [X1] :
              ( ( ( k1_lattices(X0,sK2(X0,X1),X1) != X1
                  | k1_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( ! [X4] :
                ( ( sK3(X0) = k1_lattices(X0,X4,sK3(X0))
                  & sK3(X0) = k1_lattices(X0,sK3(X0),X4) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v14_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f60,f62,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k1_lattices(X0,X2,X1) != X1
            | k1_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k1_lattices(X0,sK2(X0,X1),X1) != X1
          | k1_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( k1_lattices(X0,X4,X3) = X3
                & k1_lattices(X0,X3,X4) = X3 )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ( sK3(X0) = k1_lattices(X0,X4,sK3(X0))
              & sK3(X0) = k1_lattices(X0,sK3(X0),X4) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v14_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( ( k1_lattices(X0,X4,X3) = X3
                    & k1_lattices(X0,X3,X4) = X3 )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v14_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v14_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( ! [X2] :
                  ( ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v14_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v14_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_lattices)).

fof(f9353,plain,
    ( ~ v14_lattices(sK0)
    | ~ r2_hidden(sK3(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f9352,f749])).

fof(f749,plain,
    ( k6_lattices(sK0) = sK3(sK0)
    | ~ v14_lattices(sK0) ),
    inference(subsumption_resolution,[],[f748,f492])).

fof(f748,plain,
    ( k6_lattices(sK0) = sK3(sK0)
    | ~ v14_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f747,f65])).

fof(f747,plain,
    ( k6_lattices(sK0) = sK3(sK0)
    | ~ v14_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f746,f148])).

fof(f746,plain,
    ( k6_lattices(sK0) = sK3(sK0)
    | ~ v14_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f745,f199])).

fof(f745,plain,
    ( k6_lattices(sK0) = sK3(sK0)
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ v14_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f730])).

fof(f730,plain,
    ( k6_lattices(sK0) = sK3(sK0)
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ v14_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ v14_lattices(sK0)
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f729,f100])).

fof(f100,plain,(
    ! [X0,X3] :
      ( k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( k1_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k6_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ( ( k1_lattices(X0,sK1(X0,X1),X1) != X1
                  | k1_lattices(X0,X1,sK1(X0,X1)) != X1 )
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f56,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k1_lattices(X0,X2,X1) != X1
            | k1_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k1_lattices(X0,sK1(X0,X1),X1) != X1
          | k1_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v14_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k6_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattices)).

fof(f729,plain,(
    ! [X10] :
      ( sK3(sK0) = k1_lattices(sK0,sK3(sK0),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ v14_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f116,f148])).

fof(f116,plain,(
    ! [X10] :
      ( sK3(sK0) = k1_lattices(sK0,sK3(sK0),X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ v14_lattices(sK0)
      | ~ l2_lattices(sK0) ) ),
    inference(resolution,[],[f65,f89])).

fof(f89,plain,(
    ! [X4,X0] :
      ( sK3(X0) = k1_lattices(X0,sK3(X0),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f9352,plain,
    ( k6_lattices(sK0) != sK3(sK0)
    | ~ v14_lattices(sK0)
    | ~ r2_hidden(sK3(sK0),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f9291])).

fof(f9291,plain,
    ( k6_lattices(sK0) != sK3(sK0)
    | ~ v14_lattices(sK0)
    | ~ v14_lattices(sK0)
    | ~ r2_hidden(sK3(sK0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f182,f4454])).

fof(f4454,plain,(
    ! [X5] :
      ( sK3(sK0) = k15_lattice3(sK0,X5)
      | ~ v14_lattices(sK0)
      | ~ r2_hidden(sK3(sK0),X5) ) ),
    inference(subsumption_resolution,[],[f4453,f492])).

fof(f4453,plain,(
    ! [X5] :
      ( sK3(sK0) = k15_lattice3(sK0,X5)
      | ~ v14_lattices(sK0)
      | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ r2_hidden(sK3(sK0),X5) ) ),
    inference(subsumption_resolution,[],[f4440,f177])).

fof(f4440,plain,(
    ! [X5] :
      ( sK3(sK0) = k15_lattice3(sK0,X5)
      | ~ v14_lattices(sK0)
      | ~ m1_subset_1(k15_lattice3(sK0,X5),u1_struct_0(sK0))
      | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ r2_hidden(sK3(sK0),X5) ) ),
    inference(resolution,[],[f4430,f608])).

fof(f608,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f607,f65])).

fof(f607,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f606,f165])).

fof(f606,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f605,f167])).

fof(f605,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f604,f169])).

fof(f604,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f603,f68])).

fof(f603,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f602,f177])).

fof(f602,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f601])).

fof(f601,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f173,f95])).

fof(f173,plain,(
    ! [X2,X3] :
      ( r3_lattices(sK0,X2,k15_lattice3(sK0,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f172,f65])).

fof(f172,plain,(
    ! [X2,X3] :
      ( r3_lattices(sK0,X2,k15_lattice3(sK0,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f171,f66])).

fof(f171,plain,(
    ! [X2,X3] :
      ( r3_lattices(sK0,X2,k15_lattice3(sK0,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f155,f67])).

fof(f155,plain,(
    ! [X2,X3] :
      ( r3_lattices(sK0,X2,k15_lattice3(sK0,X3))
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f68,f80])).

fof(f4430,plain,(
    ! [X4] :
      ( ~ r1_lattices(sK0,sK3(sK0),X4)
      | sK3(sK0) = X4
      | ~ v14_lattices(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f546,f821])).

fof(f821,plain,(
    ! [X3] :
      ( r1_lattices(sK0,X3,sK3(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v14_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f820,f492])).

fof(f820,plain,(
    ! [X3] :
      ( r1_lattices(sK0,X3,sK3(sK0))
      | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v14_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f819,f65])).

fof(f819,plain,(
    ! [X3] :
      ( r1_lattices(sK0,X3,sK3(sK0))
      | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ v14_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f818,f163])).

fof(f818,plain,(
    ! [X3] :
      ( r1_lattices(sK0,X3,sK3(sK0))
      | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ v14_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f817,f165])).

fof(f817,plain,(
    ! [X3] :
      ( r1_lattices(sK0,X3,sK3(sK0))
      | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ v14_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f816,f167])).

fof(f816,plain,(
    ! [X3] :
      ( r1_lattices(sK0,X3,sK3(sK0))
      | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ v14_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f815,f169])).

fof(f815,plain,(
    ! [X3] :
      ( r1_lattices(sK0,X3,sK3(sK0))
      | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ v14_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f801,f68])).

fof(f801,plain,(
    ! [X3] :
      ( r1_lattices(sK0,X3,sK3(sK0))
      | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ v14_lattices(sK0) ) ),
    inference(duplicate_literal_removal,[],[f794])).

fof(f794,plain,(
    ! [X3] :
      ( r1_lattices(sK0,X3,sK3(sK0))
      | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | ~ v5_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ v14_lattices(sK0) ) ),
    inference(superposition,[],[f78,f772])).

fof(f772,plain,(
    ! [X11] :
      ( sK3(sK0) = k1_lattices(sK0,X11,sK3(sK0))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ v14_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f148])).

fof(f117,plain,(
    ! [X11] :
      ( sK3(sK0) = k1_lattices(sK0,X11,sK3(sK0))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ v14_lattices(sK0)
      | ~ l2_lattices(sK0) ) ),
    inference(resolution,[],[f65,f90])).

fof(f90,plain,(
    ! [X4,X0] :
      ( sK3(X0) = k1_lattices(X0,X4,sK3(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f546,plain,(
    ! [X4] :
      ( ~ v14_lattices(sK0)
      | sK3(sK0) = X4
      | ~ r1_lattices(sK0,X4,sK3(sK0))
      | ~ r1_lattices(sK0,sK3(sK0),X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f545,f65])).

fof(f545,plain,(
    ! [X4] :
      ( ~ v14_lattices(sK0)
      | sK3(sK0) = X4
      | ~ r1_lattices(sK0,X4,sK3(sK0))
      | ~ r1_lattices(sK0,sK3(sK0),X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f544,f161])).

fof(f544,plain,(
    ! [X4] :
      ( ~ v14_lattices(sK0)
      | sK3(sK0) = X4
      | ~ r1_lattices(sK0,X4,sK3(sK0))
      | ~ r1_lattices(sK0,sK3(sK0),X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f497,f148])).

fof(f497,plain,(
    ! [X4] :
      ( ~ v14_lattices(sK0)
      | sK3(sK0) = X4
      | ~ r1_lattices(sK0,X4,sK3(sK0))
      | ~ r1_lattices(sK0,sK3(sK0),X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f492,f82])).

fof(f182,plain,
    ( k6_lattices(sK0) != k15_lattice3(sK0,u1_struct_0(sK0))
    | ~ v14_lattices(sK0) ),
    inference(subsumption_resolution,[],[f181,f65])).

fof(f181,plain,
    ( k6_lattices(sK0) != k15_lattice3(sK0,u1_struct_0(sK0))
    | ~ v14_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f180,f66])).

fof(f180,plain,
    ( k6_lattices(sK0) != k15_lattice3(sK0,u1_struct_0(sK0))
    | ~ v14_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f69,f68])).

fof(f69,plain,
    ( k6_lattices(sK0) != k15_lattice3(sK0,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v14_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f2129,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X28,u1_struct_0(sK0))
      | v14_lattices(sK0)
      | m1_subset_1(sK2(sK0,k1_lattices(sK0,k15_lattice3(sK0,X29),X28)),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f2128,f65])).

fof(f2128,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X28,u1_struct_0(sK0))
      | v14_lattices(sK0)
      | m1_subset_1(sK2(sK0,k1_lattices(sK0,k15_lattice3(sK0,X29),X28)),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2068,f148])).

fof(f2068,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X28,u1_struct_0(sK0))
      | v14_lattices(sK0)
      | m1_subset_1(sK2(sK0,k1_lattices(sK0,k15_lattice3(sK0,X29),X28)),u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f480,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v14_lattices(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f112436,plain,(
    ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f112324,f177])).

fof(f112324,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    inference(trivial_inequality_removal,[],[f112280])).

fof(f112280,plain,
    ( k15_lattice3(sK0,u1_struct_0(sK0)) != k15_lattice3(sK0,u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    inference(superposition,[],[f18066,f70469])).

fof(f70469,plain,(
    ! [X1] :
      ( k15_lattice3(sK0,u1_struct_0(sK0)) = k3_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f69973])).

fof(f69973,plain,(
    ! [X1] :
      ( k15_lattice3(sK0,u1_struct_0(sK0)) = k3_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f475,f40862])).

fof(f475,plain,(
    ! [X30,X31] :
      ( k3_lattices(sK0,k15_lattice3(sK0,X30),X31) = k1_lattices(sK0,k15_lattice3(sK0,X30),X31)
      | ~ m1_subset_1(X31,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f474,f65])).

fof(f474,plain,(
    ! [X30,X31] :
      ( k3_lattices(sK0,k15_lattice3(sK0,X30),X31) = k1_lattices(sK0,k15_lattice3(sK0,X30),X31)
      | ~ m1_subset_1(X31,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f473,f161])).

fof(f473,plain,(
    ! [X30,X31] :
      ( k3_lattices(sK0,k15_lattice3(sK0,X30),X31) = k1_lattices(sK0,k15_lattice3(sK0,X30),X31)
      | ~ m1_subset_1(X31,u1_struct_0(sK0))
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f402,f148])).

fof(f402,plain,(
    ! [X30,X31] :
      ( k3_lattices(sK0,k15_lattice3(sK0,X30),X31) = k1_lattices(sK0,k15_lattice3(sK0,X30),X31)
      | ~ m1_subset_1(X31,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f177,f98])).

fof(f18066,plain,(
    ! [X0] :
      ( k3_lattices(sK0,X0,sK2(sK0,X0)) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f18065,f9354])).

fof(f18065,plain,(
    ! [X0] :
      ( k3_lattices(sK0,X0,sK2(sK0,X0)) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v14_lattices(sK0) ) ),
    inference(duplicate_literal_removal,[],[f18040])).

fof(f18040,plain,(
    ! [X0] :
      ( k3_lattices(sK0,X0,sK2(sK0,X0)) != X0
      | k3_lattices(sK0,X0,sK2(sK0,X0)) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v14_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f18039,f698])).

fof(f698,plain,(
    ! [X26,X27] :
      ( k3_lattices(sK0,sK2(sK0,X26),X27) = k3_lattices(sK0,X27,sK2(sK0,X26))
      | ~ m1_subset_1(X26,u1_struct_0(sK0))
      | v14_lattices(sK0)
      | ~ m1_subset_1(X27,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f697,f65])).

fof(f697,plain,(
    ! [X26,X27] :
      ( v14_lattices(sK0)
      | ~ m1_subset_1(X26,u1_struct_0(sK0))
      | k3_lattices(sK0,sK2(sK0,X26),X27) = k3_lattices(sK0,X27,sK2(sK0,X26))
      | ~ m1_subset_1(X27,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f696,f161])).

fof(f696,plain,(
    ! [X26,X27] :
      ( v14_lattices(sK0)
      | ~ m1_subset_1(X26,u1_struct_0(sK0))
      | k3_lattices(sK0,sK2(sK0,X26),X27) = k3_lattices(sK0,X27,sK2(sK0,X26))
      | ~ m1_subset_1(X27,u1_struct_0(sK0))
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f635,f148])).

fof(f635,plain,(
    ! [X26,X27] :
      ( v14_lattices(sK0)
      | ~ m1_subset_1(X26,u1_struct_0(sK0))
      | k3_lattices(sK0,sK2(sK0,X26),X27) = k3_lattices(sK0,X27,sK2(sK0,X26))
      | ~ m1_subset_1(X27,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f616,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f616,plain,(
    ! [X12] :
      ( m1_subset_1(sK2(sK0,X12),u1_struct_0(sK0))
      | v14_lattices(sK0)
      | ~ m1_subset_1(X12,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f118,f148])).

fof(f118,plain,(
    ! [X12] :
      ( v14_lattices(sK0)
      | m1_subset_1(sK2(sK0,X12),u1_struct_0(sK0))
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ l2_lattices(sK0) ) ),
    inference(resolution,[],[f65,f91])).

fof(f18039,plain,(
    ! [X0] :
      ( k3_lattices(sK0,sK2(sK0,X0),X0) != X0
      | k3_lattices(sK0,X0,sK2(sK0,X0)) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f5579,f9354])).

fof(f5579,plain,(
    ! [X0] :
      ( k3_lattices(sK0,sK2(sK0,X0),X0) != X0
      | v14_lattices(sK0)
      | k3_lattices(sK0,X0,sK2(sK0,X0)) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f5578,f616])).

fof(f5578,plain,(
    ! [X0] :
      ( k3_lattices(sK0,sK2(sK0,X0),X0) != X0
      | v14_lattices(sK0)
      | k3_lattices(sK0,X0,sK2(sK0,X0)) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f5568])).

fof(f5568,plain,(
    ! [X0] :
      ( k3_lattices(sK0,sK2(sK0,X0),X0) != X0
      | v14_lattices(sK0)
      | k3_lattices(sK0,X0,sK2(sK0,X0)) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f1232,f1161])).

fof(f1161,plain,(
    ! [X21,X22] :
      ( k3_lattices(sK0,X21,X22) = k1_lattices(sK0,X21,X22)
      | ~ m1_subset_1(X22,u1_struct_0(sK0))
      | ~ m1_subset_1(X21,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1160,f161])).

fof(f1160,plain,(
    ! [X21,X22] :
      ( k3_lattices(sK0,X21,X22) = k1_lattices(sK0,X21,X22)
      | ~ m1_subset_1(X22,u1_struct_0(sK0))
      | ~ m1_subset_1(X21,u1_struct_0(sK0))
      | ~ v4_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f124,f148])).

fof(f124,plain,(
    ! [X21,X22] :
      ( k3_lattices(sK0,X21,X22) = k1_lattices(sK0,X21,X22)
      | ~ m1_subset_1(X22,u1_struct_0(sK0))
      | ~ m1_subset_1(X21,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0) ) ),
    inference(resolution,[],[f65,f98])).

fof(f1232,plain,(
    ! [X12] :
      ( k1_lattices(sK0,sK2(sK0,X12),X12) != X12
      | v14_lattices(sK0)
      | k3_lattices(sK0,X12,sK2(sK0,X12)) != X12
      | ~ m1_subset_1(X12,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1231,f616])).

fof(f1231,plain,(
    ! [X12] :
      ( k3_lattices(sK0,X12,sK2(sK0,X12)) != X12
      | v14_lattices(sK0)
      | k1_lattices(sK0,sK2(sK0,X12),X12) != X12
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(sK0,X12),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1230,f65])).

fof(f1230,plain,(
    ! [X12] :
      ( k3_lattices(sK0,X12,sK2(sK0,X12)) != X12
      | v14_lattices(sK0)
      | k1_lattices(sK0,sK2(sK0,X12),X12) != X12
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2(sK0,X12),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1186,f148])).

fof(f1186,plain,(
    ! [X12] :
      ( k3_lattices(sK0,X12,sK2(sK0,X12)) != X12
      | v14_lattices(sK0)
      | k1_lattices(sK0,sK2(sK0,X12),X12) != X12
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2(sK0,X12),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f1175])).

fof(f1175,plain,(
    ! [X12] :
      ( k3_lattices(sK0,X12,sK2(sK0,X12)) != X12
      | v14_lattices(sK0)
      | k1_lattices(sK0,sK2(sK0,X12),X12) != X12
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2(sK0,X12),u1_struct_0(sK0))
      | ~ m1_subset_1(X12,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f92,f1161])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v14_lattices(X0)
      | k1_lattices(X0,sK2(X0,X1),X1) != X1
      | k1_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

%------------------------------------------------------------------------------
