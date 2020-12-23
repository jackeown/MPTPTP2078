%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:38 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  164 (6194 expanded)
%              Number of leaves         :   25 (2749 expanded)
%              Depth                    :   19
%              Number of atoms          :  626 (43727 expanded)
%              Number of equality atoms :  145 (6948 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8176,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8175,f72])).

fof(f72,plain,(
    k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK3)) != k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK3)) != k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3))
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v11_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f46,f45,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) != k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_lattices(sK0,X1,k4_lattices(sK0,X2,X3)) != k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X1,X3))
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v11_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k3_lattices(sK0,X1,k4_lattices(sK0,X2,X3)) != k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X1,X3))
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k3_lattices(sK0,sK1,k4_lattices(sK0,X2,X3)) != k4_lattices(sK0,k3_lattices(sK0,sK1,X2),k3_lattices(sK0,sK1,X3))
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k3_lattices(sK0,sK1,k4_lattices(sK0,X2,X3)) != k4_lattices(sK0,k3_lattices(sK0,sK1,X2),k3_lattices(sK0,sK1,X3))
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,X3)) != k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,X3))
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X3] :
        ( k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,X3)) != k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,X3))
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK3)) != k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3))
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) != k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) != k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v11_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_lattices)).

fof(f8175,plain,(
    k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3)) ),
    inference(backward_demodulation,[],[f1704,f8174])).

fof(f8174,plain,(
    k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),sK1) ),
    inference(forward_demodulation,[],[f8173,f7097])).

fof(f7097,plain,(
    k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK1) ),
    inference(backward_demodulation,[],[f6991,f6982])).

fof(f6982,plain,(
    k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f65,f105,f104,f69,f329,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f329,plain,(
    m1_subset_1(k4_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f103,f71,f70,f107,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f107,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f65,f66,f68,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f68,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f66,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
    l1_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f68,f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f69,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,(
    l2_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f68,f74])).

fof(f74,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f105,plain,(
    v4_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f65,f66,f68,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f6991,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK1) = k3_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f65,f105,f104,f69,f329,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f8173,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),sK1) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK1) ),
    inference(forward_demodulation,[],[f8172,f516])).

fof(f516,plain,(
    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1) ),
    inference(backward_demodulation,[],[f507,f512])).

fof(f512,plain,(
    sK1 = k4_lattices(sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f315,f511])).

fof(f511,plain,(
    sK1 = k2_lattices(sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f402,f411])).

fof(f411,plain,(
    sK1 = k1_lattices(sK0,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f65,f107,f108,f68,f69,f109,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).

fof(f109,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f65,f66,f68,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f108,plain,(
    v8_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f65,f66,f68,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f402,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f65,f68,f69,f69,f109,f92])).

fof(f92,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),sK11(X0)))
            & m1_subset_1(sK11(X0),u1_struct_0(X0))
            & m1_subset_1(sK10(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f61,f63,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK10(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),sK11(X0)))
        & m1_subset_1(sK11(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

fof(f315,plain,(
    k2_lattices(sK0,sK1,sK1) = k4_lattices(sK0,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f65,f103,f69,f69,f107,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f507,plain,(
    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK1)) ),
    inference(backward_demodulation,[],[f375,f505])).

fof(f505,plain,(
    sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3)) ),
    inference(forward_demodulation,[],[f404,f156])).

fof(f156,plain,(
    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f65,f104,f71,f69,f105,f99])).

fof(f404,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f65,f68,f71,f69,f109,f92])).

fof(f375,plain,(
    k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK1)) ),
    inference(backward_demodulation,[],[f365,f315])).

fof(f365,plain,(
    k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK1,sK1)) ),
    inference(backward_demodulation,[],[f192,f317])).

fof(f317,plain,(
    k2_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f65,f103,f71,f69,f107,f101])).

fof(f192,plain,(
    k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK1,sK1)) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3)) ),
    inference(backward_demodulation,[],[f134,f191])).

fof(f191,plain,(
    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f160,f169])).

fof(f169,plain,(
    k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f65,f104,f69,f71,f105,f98])).

fof(f160,plain,(
    k1_lattices(sK0,sK3,sK1) = k3_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f65,f104,f69,f71,f105,f99])).

fof(f134,plain,(
    k2_lattices(sK0,sK1,k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f65,f68,f67,f69,f69,f71,f87])).

fof(f87,plain,(
    ! [X6,X4,X0,X5] :
      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ( k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),sK9(X0))) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),sK9(X0)))
            & m1_subset_1(sK9(X0),u1_struct_0(X0))
            & m1_subset_1(sK8(X0),u1_struct_0(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f55,f58,f57,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k2_lattices(X0,sK7(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),k2_lattices(X0,sK7(X0),X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k2_lattices(X0,sK7(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),k2_lattices(X0,sK7(X0),X3))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),X3))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),X3))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),sK9(X0))) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),sK9(X0)))
        & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v11_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattices)).

fof(f67,plain,(
    v11_lattices(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f8172,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),sK1) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1)) ),
    inference(forward_demodulation,[],[f6649,f1142])).

fof(f1142,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK3)) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f391,f1133])).

fof(f1133,plain,(
    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f65,f107,f103,f71,f173,f101])).

fof(f173,plain,(
    m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f104,f70,f69,f105,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattices)).

fof(f391,plain,(
    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK3)) ),
    inference(backward_demodulation,[],[f383,f312])).

fof(f312,plain,(
    k4_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f65,f103,f69,f71,f107,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f383,plain,(
    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK3,sK1)) ),
    inference(backward_demodulation,[],[f343,f313])).

fof(f313,plain,(
    k4_lattices(sK0,sK2,sK3) = k4_lattices(sK0,sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f65,f103,f70,f71,f107,f102])).

fof(f343,plain,(
    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK3,sK2),k4_lattices(sK0,sK3,sK1)) ),
    inference(backward_demodulation,[],[f341,f321])).

fof(f321,plain,(
    k2_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f65,f103,f69,f71,f107,f101])).

fof(f341,plain,(
    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) ),
    inference(backward_demodulation,[],[f202,f322])).

fof(f322,plain,(
    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f65,f103,f70,f71,f107,f101])).

fof(f202,plain,(
    k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f146,f201])).

fof(f201,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f157,f166])).

fof(f166,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f65,f104,f69,f70,f105,f98])).

fof(f157,plain,(
    k1_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f65,f104,f69,f70,f105,f99])).

fof(f146,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f65,f68,f67,f69,f70,f71,f87])).

fof(f6649,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1)) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK3)),sK1) ),
    inference(unit_resulting_resolution,[],[f65,f104,f106,f69,f326,f329,f82])).

fof(f82,plain,(
    ! [X6,X4,X0,X5] :
      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ( k1_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),sK6(X0))) != k1_lattices(X0,k1_lattices(X0,sK4(X0),sK5(X0)),sK6(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f49,f52,f51,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k1_lattices(X0,sK4(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK4(X0),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_lattices(X0,sK4(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK4(X0),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k1_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK4(X0),sK5(X0)),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k1_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK4(X0),sK5(X0)),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),sK6(X0))) != k1_lattices(X0,k1_lattices(X0,sK4(X0),sK5(X0)),sK6(X0))
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattices)).

fof(f326,plain,(
    m1_subset_1(k4_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f103,f71,f69,f107,f100])).

fof(f106,plain,(
    v5_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f65,f66,f68,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1704,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),sK1) ),
    inference(backward_demodulation,[],[f1219,f1703])).

fof(f1703,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,sK1,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) ),
    inference(backward_demodulation,[],[f1218,f1676])).

fof(f1676,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f65,f107,f103,f173,f174,f101])).

fof(f174,plain,(
    m1_subset_1(k3_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f104,f71,f69,f105,f97])).

fof(f1218,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,sK1,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) ),
    inference(forward_demodulation,[],[f1217,f156])).

fof(f1217,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,sK1,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) ),
    inference(forward_demodulation,[],[f1216,f1156])).

fof(f1156,plain,(
    sK1 = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1) ),
    inference(forward_demodulation,[],[f1127,f1153])).

fof(f1153,plain,(
    sK1 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1) ),
    inference(backward_demodulation,[],[f1139,f1152])).

fof(f1152,plain,(
    sK1 = k4_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f1131,f508])).

fof(f508,plain,(
    sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f403,f155])).

fof(f155,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f65,f104,f70,f69,f105,f99])).

fof(f403,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f65,f68,f70,f69,f109,f92])).

fof(f1131,plain,(
    k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f65,f107,f103,f69,f173,f101])).

fof(f1139,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1) = k4_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f65,f107,f103,f69,f173,f102])).

fof(f1127,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f65,f107,f103,f69,f173,f101])).

fof(f1216,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1),k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) ),
    inference(forward_demodulation,[],[f1077,f1154])).

fof(f1154,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f1129,f1141])).

fof(f1141,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f65,f107,f103,f71,f173,f102])).

fof(f1129,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3) ),
    inference(unit_resulting_resolution,[],[f65,f107,f103,f71,f173,f101])).

fof(f1077,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3)) ),
    inference(unit_resulting_resolution,[],[f65,f68,f67,f71,f69,f173,f87])).

fof(f1219,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),sK1) = k1_lattices(sK0,sK1,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))) ),
    inference(backward_demodulation,[],[f1199,f1218])).

fof(f1199,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),sK1) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3)) ),
    inference(forward_demodulation,[],[f1198,f191])).

fof(f1198,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),sK1) ),
    inference(forward_demodulation,[],[f1197,f1154])).

fof(f1197,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3),sK1) ),
    inference(forward_demodulation,[],[f1083,f1156])).

fof(f1083,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1)) ),
    inference(unit_resulting_resolution,[],[f65,f68,f67,f69,f71,f173,f87])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:42:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (9178)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.44  % (9203)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.46  % (9195)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.50  % (9193)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (9176)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (9184)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (9181)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (9177)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (9182)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (9205)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (9180)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (9187)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (9200)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (9192)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (9183)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (9198)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (9186)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (9197)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (9204)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (9185)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (9194)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (9202)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (9199)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (9189)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (9188)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (9196)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (9199)Refutation not found, incomplete strategy% (9199)------------------------------
% 0.21/0.52  % (9199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9199)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9199)Memory used [KB]: 10746
% 0.21/0.52  % (9199)Time elapsed: 0.132 s
% 0.21/0.52  % (9199)------------------------------
% 0.21/0.52  % (9199)------------------------------
% 0.21/0.53  % (9194)Refutation not found, incomplete strategy% (9194)------------------------------
% 0.21/0.53  % (9194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9194)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9194)Memory used [KB]: 10618
% 0.21/0.53  % (9194)Time elapsed: 0.099 s
% 0.21/0.53  % (9194)------------------------------
% 0.21/0.53  % (9194)------------------------------
% 0.21/0.53  % (9179)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (9201)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (9206)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (9191)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (9186)Refutation not found, incomplete strategy% (9186)------------------------------
% 0.21/0.54  % (9186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9186)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9186)Memory used [KB]: 10874
% 0.21/0.56  % (9186)Time elapsed: 0.150 s
% 0.21/0.56  % (9186)------------------------------
% 0.21/0.56  % (9186)------------------------------
% 0.21/0.56  % (9187)Refutation not found, incomplete strategy% (9187)------------------------------
% 0.21/0.56  % (9187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9187)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9187)Memory used [KB]: 11129
% 0.21/0.56  % (9187)Time elapsed: 0.167 s
% 0.21/0.56  % (9187)------------------------------
% 0.21/0.56  % (9187)------------------------------
% 1.76/0.60  % (9185)Refutation not found, incomplete strategy% (9185)------------------------------
% 1.76/0.60  % (9185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (9185)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.60  
% 1.76/0.60  % (9185)Memory used [KB]: 11513
% 1.76/0.60  % (9185)Time elapsed: 0.204 s
% 1.76/0.60  % (9185)------------------------------
% 1.76/0.60  % (9185)------------------------------
% 2.11/0.67  % (9304)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.11/0.68  % (9316)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.11/0.69  % (9307)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.82/0.73  % (9315)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.82/0.74  % (9326)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.82/0.75  % (9203)Refutation found. Thanks to Tanya!
% 2.82/0.75  % SZS status Theorem for theBenchmark
% 2.82/0.75  % SZS output start Proof for theBenchmark
% 2.82/0.75  fof(f8176,plain,(
% 2.82/0.75    $false),
% 2.82/0.75    inference(subsumption_resolution,[],[f8175,f72])).
% 2.82/0.75  fof(f72,plain,(
% 2.82/0.75    k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK3)) != k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3))),
% 2.82/0.75    inference(cnf_transformation,[],[f47])).
% 2.82/0.75  fof(f47,plain,(
% 2.82/0.75    (((k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK3)) != k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3)) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 2.82/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f46,f45,f44,f43])).
% 2.82/0.75  fof(f43,plain,(
% 2.82/0.75    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) != k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k3_lattices(sK0,X1,k4_lattices(sK0,X2,X3)) != k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 2.82/0.75    introduced(choice_axiom,[])).
% 2.82/0.75  fof(f44,plain,(
% 2.82/0.75    ? [X1] : (? [X2] : (? [X3] : (k3_lattices(sK0,X1,k4_lattices(sK0,X2,X3)) != k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (k3_lattices(sK0,sK1,k4_lattices(sK0,X2,X3)) != k4_lattices(sK0,k3_lattices(sK0,sK1,X2),k3_lattices(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 2.82/0.75    introduced(choice_axiom,[])).
% 2.82/0.75  fof(f45,plain,(
% 2.82/0.75    ? [X2] : (? [X3] : (k3_lattices(sK0,sK1,k4_lattices(sK0,X2,X3)) != k4_lattices(sK0,k3_lattices(sK0,sK1,X2),k3_lattices(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,X3)) != k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 2.82/0.75    introduced(choice_axiom,[])).
% 2.82/0.75  fof(f46,plain,(
% 2.82/0.75    ? [X3] : (k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,X3)) != k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,X3)) & m1_subset_1(X3,u1_struct_0(sK0))) => (k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK3)) != k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3)) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 2.82/0.75    introduced(choice_axiom,[])).
% 2.82/0.75  fof(f18,plain,(
% 2.82/0.75    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) != k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.82/0.75    inference(flattening,[],[f17])).
% 2.82/0.75  fof(f17,plain,(
% 2.82/0.75    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) != k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f15])).
% 2.82/0.75  fof(f15,negated_conjecture,(
% 2.82/0.75    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))))))),
% 2.82/0.75    inference(negated_conjecture,[],[f14])).
% 2.82/0.75  fof(f14,conjecture,(
% 2.82/0.75    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))))))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_lattices)).
% 2.82/0.75  fof(f8175,plain,(
% 2.82/0.75    k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3))),
% 2.82/0.75    inference(backward_demodulation,[],[f1704,f8174])).
% 2.82/0.75  fof(f8174,plain,(
% 2.82/0.75    k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),sK1)),
% 2.82/0.75    inference(forward_demodulation,[],[f8173,f7097])).
% 2.82/0.75  fof(f7097,plain,(
% 2.82/0.75    k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK1)),
% 2.82/0.75    inference(backward_demodulation,[],[f6991,f6982])).
% 2.82/0.75  fof(f6982,plain,(
% 2.82/0.75    k3_lattices(sK0,sK1,k4_lattices(sK0,sK2,sK3)) = k3_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK1)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f105,f104,f69,f329,f98])).
% 2.82/0.75  fof(f98,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f34])).
% 2.82/0.75  fof(f34,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.75    inference(flattening,[],[f33])).
% 2.82/0.75  fof(f33,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f3])).
% 2.82/0.75  fof(f3,axiom,(
% 2.82/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 2.82/0.75  fof(f329,plain,(
% 2.82/0.75    m1_subset_1(k4_lattices(sK0,sK2,sK3),u1_struct_0(sK0))),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f103,f71,f70,f107,f100])).
% 2.82/0.75  fof(f100,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f38])).
% 2.82/0.75  fof(f38,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.75    inference(flattening,[],[f37])).
% 2.82/0.75  fof(f37,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f9])).
% 2.82/0.75  fof(f9,axiom,(
% 2.82/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).
% 2.82/0.75  fof(f107,plain,(
% 2.82/0.75    v6_lattices(sK0)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f66,f68,f78])).
% 2.82/0.75  fof(f78,plain,(
% 2.82/0.75    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f21])).
% 2.82/0.75  fof(f21,plain,(
% 2.82/0.75    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.82/0.75    inference(flattening,[],[f20])).
% 2.82/0.75  fof(f20,plain,(
% 2.82/0.75    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.82/0.75    inference(ennf_transformation,[],[f16])).
% 2.82/0.75  fof(f16,plain,(
% 2.82/0.75    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.82/0.75    inference(pure_predicate_removal,[],[f2])).
% 2.82/0.75  fof(f2,axiom,(
% 2.82/0.75    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 2.82/0.75  fof(f68,plain,(
% 2.82/0.75    l3_lattices(sK0)),
% 2.82/0.75    inference(cnf_transformation,[],[f47])).
% 2.82/0.75  fof(f66,plain,(
% 2.82/0.75    v10_lattices(sK0)),
% 2.82/0.75    inference(cnf_transformation,[],[f47])).
% 2.82/0.75  fof(f70,plain,(
% 2.82/0.75    m1_subset_1(sK2,u1_struct_0(sK0))),
% 2.82/0.75    inference(cnf_transformation,[],[f47])).
% 2.82/0.75  fof(f71,plain,(
% 2.82/0.75    m1_subset_1(sK3,u1_struct_0(sK0))),
% 2.82/0.75    inference(cnf_transformation,[],[f47])).
% 2.82/0.75  fof(f103,plain,(
% 2.82/0.75    l1_lattices(sK0)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f68,f73])).
% 2.82/0.75  fof(f73,plain,(
% 2.82/0.75    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f19])).
% 2.82/0.75  fof(f19,plain,(
% 2.82/0.75    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 2.82/0.75    inference(ennf_transformation,[],[f10])).
% 2.82/0.75  fof(f10,axiom,(
% 2.82/0.75    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 2.82/0.75  fof(f69,plain,(
% 2.82/0.75    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.82/0.75    inference(cnf_transformation,[],[f47])).
% 2.82/0.75  fof(f104,plain,(
% 2.82/0.75    l2_lattices(sK0)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f68,f74])).
% 2.82/0.75  fof(f74,plain,(
% 2.82/0.75    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f19])).
% 2.82/0.75  fof(f105,plain,(
% 2.82/0.75    v4_lattices(sK0)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f66,f68,f76])).
% 2.82/0.75  fof(f76,plain,(
% 2.82/0.75    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f21])).
% 2.82/0.75  fof(f65,plain,(
% 2.82/0.75    ~v2_struct_0(sK0)),
% 2.82/0.75    inference(cnf_transformation,[],[f47])).
% 2.82/0.75  fof(f6991,plain,(
% 2.82/0.75    k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK1) = k3_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK1)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f105,f104,f69,f329,f99])).
% 2.82/0.75  fof(f99,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f36])).
% 2.82/0.75  fof(f36,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.75    inference(flattening,[],[f35])).
% 2.82/0.75  fof(f35,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f11])).
% 2.82/0.75  fof(f11,axiom,(
% 2.82/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 2.82/0.75  fof(f8173,plain,(
% 2.82/0.75    k1_lattices(sK0,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),sK1) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),sK1)),
% 2.82/0.75    inference(forward_demodulation,[],[f8172,f516])).
% 2.82/0.75  fof(f516,plain,(
% 2.82/0.75    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1)),
% 2.82/0.75    inference(backward_demodulation,[],[f507,f512])).
% 2.82/0.75  fof(f512,plain,(
% 2.82/0.75    sK1 = k4_lattices(sK0,sK1,sK1)),
% 2.82/0.75    inference(backward_demodulation,[],[f315,f511])).
% 2.82/0.75  fof(f511,plain,(
% 2.82/0.75    sK1 = k2_lattices(sK0,sK1,sK1)),
% 2.82/0.75    inference(forward_demodulation,[],[f402,f411])).
% 2.82/0.75  fof(f411,plain,(
% 2.82/0.75    sK1 = k1_lattices(sK0,sK1,sK1)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f107,f108,f68,f69,f109,f81])).
% 2.82/0.75  fof(f81,plain,(
% 2.82/0.75    ( ! [X0,X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f23])).
% 2.82/0.75  fof(f23,plain,(
% 2.82/0.75    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.75    inference(flattening,[],[f22])).
% 2.82/0.75  fof(f22,plain,(
% 2.82/0.75    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f13])).
% 2.82/0.75  fof(f13,axiom,(
% 2.82/0.75    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).
% 2.82/0.75  fof(f109,plain,(
% 2.82/0.75    v9_lattices(sK0)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f66,f68,f80])).
% 2.82/0.75  fof(f80,plain,(
% 2.82/0.75    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f21])).
% 2.82/0.75  fof(f108,plain,(
% 2.82/0.75    v8_lattices(sK0)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f66,f68,f79])).
% 2.82/0.75  fof(f79,plain,(
% 2.82/0.75    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f21])).
% 2.82/0.75  fof(f402,plain,(
% 2.82/0.75    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f68,f69,f69,f109,f92])).
% 2.82/0.75  fof(f92,plain,(
% 2.82/0.75    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f64])).
% 2.82/0.75  fof(f64,plain,(
% 2.82/0.75    ! [X0] : (((v9_lattices(X0) | ((sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),sK11(X0))) & m1_subset_1(sK11(X0),u1_struct_0(X0))) & m1_subset_1(sK10(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f61,f63,f62])).
% 2.82/0.75  fof(f62,plain,(
% 2.82/0.75    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK10(X0),u1_struct_0(X0))))),
% 2.82/0.75    introduced(choice_axiom,[])).
% 2.82/0.75  fof(f63,plain,(
% 2.82/0.75    ! [X0] : (? [X2] : (sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),sK11(X0))) & m1_subset_1(sK11(X0),u1_struct_0(X0))))),
% 2.82/0.75    introduced(choice_axiom,[])).
% 2.82/0.75  fof(f61,plain,(
% 2.82/0.75    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.75    inference(rectify,[],[f60])).
% 2.82/0.75  fof(f60,plain,(
% 2.82/0.75    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.75    inference(nnf_transformation,[],[f29])).
% 2.82/0.75  fof(f29,plain,(
% 2.82/0.75    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.75    inference(flattening,[],[f28])).
% 2.82/0.75  fof(f28,plain,(
% 2.82/0.75    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f7])).
% 2.82/0.75  fof(f7,axiom,(
% 2.82/0.75    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).
% 2.82/0.75  fof(f315,plain,(
% 2.82/0.75    k2_lattices(sK0,sK1,sK1) = k4_lattices(sK0,sK1,sK1)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f103,f69,f69,f107,f101])).
% 2.82/0.75  fof(f101,plain,(
% 2.82/0.75    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.82/0.75    inference(cnf_transformation,[],[f40])).
% 2.82/0.75  fof(f40,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.75    inference(flattening,[],[f39])).
% 2.82/0.75  fof(f39,plain,(
% 2.82/0.75    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.82/0.75    inference(ennf_transformation,[],[f12])).
% 2.82/0.75  fof(f12,axiom,(
% 2.82/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 2.82/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 2.82/0.75  fof(f507,plain,(
% 2.82/0.75    sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK1))),
% 2.82/0.75    inference(backward_demodulation,[],[f375,f505])).
% 2.82/0.75  fof(f505,plain,(
% 2.82/0.75    sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3))),
% 2.82/0.75    inference(forward_demodulation,[],[f404,f156])).
% 2.82/0.75  fof(f156,plain,(
% 2.82/0.75    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK3)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f104,f71,f69,f105,f99])).
% 2.82/0.75  fof(f404,plain,(
% 2.82/0.75    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3))),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f68,f71,f69,f109,f92])).
% 2.82/0.75  fof(f375,plain,(
% 2.82/0.75    k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),k4_lattices(sK0,sK1,sK1))),
% 2.82/0.75    inference(backward_demodulation,[],[f365,f315])).
% 2.82/0.75  fof(f365,plain,(
% 2.82/0.75    k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK1,sK1))),
% 2.82/0.75    inference(backward_demodulation,[],[f192,f317])).
% 2.82/0.75  fof(f317,plain,(
% 2.82/0.75    k2_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK1,sK3)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f103,f71,f69,f107,f101])).
% 2.82/0.75  fof(f192,plain,(
% 2.82/0.75    k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK1,sK1)) = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK3))),
% 2.82/0.75    inference(backward_demodulation,[],[f134,f191])).
% 2.82/0.75  fof(f191,plain,(
% 2.82/0.75    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK3,sK1)),
% 2.82/0.75    inference(forward_demodulation,[],[f160,f169])).
% 2.82/0.75  fof(f169,plain,(
% 2.82/0.75    k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,sK3,sK1)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f104,f69,f71,f105,f98])).
% 2.82/0.75  fof(f160,plain,(
% 2.82/0.75    k1_lattices(sK0,sK3,sK1) = k3_lattices(sK0,sK3,sK1)),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f104,f69,f71,f105,f99])).
% 2.82/0.75  fof(f134,plain,(
% 2.82/0.75    k2_lattices(sK0,sK1,k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK1,sK1))),
% 2.82/0.75    inference(unit_resulting_resolution,[],[f65,f68,f67,f69,f69,f71,f87])).
% 2.82/0.76  fof(f87,plain,(
% 2.82/0.76    ( ! [X6,X4,X0,X5] : (k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v11_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.82/0.76    inference(cnf_transformation,[],[f59])).
% 2.82/0.76  fof(f59,plain,(
% 2.82/0.76    ! [X0] : (((v11_lattices(X0) | (((k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),sK9(X0))) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),sK9(X0))) & m1_subset_1(sK9(X0),u1_struct_0(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f55,f58,f57,f56])).
% 2.82/0.76  fof(f56,plain,(
% 2.82/0.76    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k2_lattices(X0,sK7(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),k2_lattices(X0,sK7(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 2.82/0.76    introduced(choice_axiom,[])).
% 2.82/0.76  fof(f57,plain,(
% 2.82/0.76    ! [X0] : (? [X2] : (? [X3] : (k2_lattices(X0,sK7(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),k2_lattices(X0,sK7(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 2.82/0.76    introduced(choice_axiom,[])).
% 2.82/0.76  fof(f58,plain,(
% 2.82/0.76    ! [X0] : (? [X3] : (k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) => (k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),sK9(X0))) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),sK9(X0))) & m1_subset_1(sK9(X0),u1_struct_0(X0))))),
% 2.82/0.76    introduced(choice_axiom,[])).
% 2.82/0.76  fof(f55,plain,(
% 2.82/0.76    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.76    inference(rectify,[],[f54])).
% 2.82/0.76  fof(f54,plain,(
% 2.82/0.76    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.76    inference(nnf_transformation,[],[f27])).
% 2.82/0.76  fof(f27,plain,(
% 2.82/0.76    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.76    inference(flattening,[],[f26])).
% 2.82/0.76  fof(f26,plain,(
% 2.82/0.76    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.82/0.76    inference(ennf_transformation,[],[f5])).
% 2.82/0.76  fof(f5,axiom,(
% 2.82/0.76    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v11_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)))))))),
% 2.82/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattices)).
% 2.82/0.76  fof(f67,plain,(
% 2.82/0.76    v11_lattices(sK0)),
% 2.82/0.76    inference(cnf_transformation,[],[f47])).
% 2.82/0.76  fof(f8172,plain,(
% 2.82/0.76    k1_lattices(sK0,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),sK1) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1))),
% 2.82/0.76    inference(forward_demodulation,[],[f6649,f1142])).
% 2.82/0.76  fof(f1142,plain,(
% 2.82/0.76    k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK3)) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))),
% 2.82/0.76    inference(backward_demodulation,[],[f391,f1133])).
% 2.82/0.76  fof(f1133,plain,(
% 2.82/0.76    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f107,f103,f71,f173,f101])).
% 2.82/0.76  fof(f173,plain,(
% 2.82/0.76    m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f104,f70,f69,f105,f97])).
% 2.82/0.76  fof(f97,plain,(
% 2.82/0.76    ( ! [X2,X0,X1] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 2.82/0.76    inference(cnf_transformation,[],[f32])).
% 2.82/0.76  fof(f32,plain,(
% 2.82/0.76    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.76    inference(flattening,[],[f31])).
% 2.82/0.76  fof(f31,plain,(
% 2.82/0.76    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 2.82/0.76    inference(ennf_transformation,[],[f8])).
% 2.82/0.76  fof(f8,axiom,(
% 2.82/0.76    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 2.82/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattices)).
% 2.82/0.76  fof(f391,plain,(
% 2.82/0.76    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK3))),
% 2.82/0.76    inference(backward_demodulation,[],[f383,f312])).
% 2.82/0.76  fof(f312,plain,(
% 2.82/0.76    k4_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK1,sK3)),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f103,f69,f71,f107,f102])).
% 2.82/0.76  fof(f102,plain,(
% 2.82/0.76    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.82/0.76    inference(cnf_transformation,[],[f42])).
% 2.82/0.76  fof(f42,plain,(
% 2.82/0.76    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.76    inference(flattening,[],[f41])).
% 2.82/0.76  fof(f41,plain,(
% 2.82/0.76    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.82/0.76    inference(ennf_transformation,[],[f4])).
% 2.82/0.76  fof(f4,axiom,(
% 2.82/0.76    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 2.82/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 2.82/0.76  fof(f383,plain,(
% 2.82/0.76    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK3,sK1))),
% 2.82/0.76    inference(backward_demodulation,[],[f343,f313])).
% 2.82/0.76  fof(f313,plain,(
% 2.82/0.76    k4_lattices(sK0,sK2,sK3) = k4_lattices(sK0,sK3,sK2)),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f103,f70,f71,f107,f102])).
% 2.82/0.76  fof(f343,plain,(
% 2.82/0.76    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK3,sK2),k4_lattices(sK0,sK3,sK1))),
% 2.82/0.76    inference(backward_demodulation,[],[f341,f321])).
% 2.82/0.76  fof(f321,plain,(
% 2.82/0.76    k2_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK3,sK1)),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f103,f69,f71,f107,f101])).
% 2.82/0.76  fof(f341,plain,(
% 2.82/0.76    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1))),
% 2.82/0.76    inference(backward_demodulation,[],[f202,f322])).
% 2.82/0.76  fof(f322,plain,(
% 2.82/0.76    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK3,sK2)),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f103,f70,f71,f107,f101])).
% 2.82/0.76  fof(f202,plain,(
% 2.82/0.76    k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))),
% 2.82/0.76    inference(backward_demodulation,[],[f146,f201])).
% 2.82/0.76  fof(f201,plain,(
% 2.82/0.76    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK2,sK1)),
% 2.82/0.76    inference(forward_demodulation,[],[f157,f166])).
% 2.82/0.76  fof(f166,plain,(
% 2.82/0.76    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1)),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f104,f69,f70,f105,f98])).
% 2.82/0.76  fof(f157,plain,(
% 2.82/0.76    k1_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK2,sK1)),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f104,f69,f70,f105,f99])).
% 2.82/0.76  fof(f146,plain,(
% 2.82/0.76    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1))),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f68,f67,f69,f70,f71,f87])).
% 2.82/0.76  fof(f6649,plain,(
% 2.82/0.76    k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k1_lattices(sK0,k4_lattices(sK0,sK1,sK3),sK1)) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK3)),sK1)),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f104,f106,f69,f326,f329,f82])).
% 2.82/0.76  fof(f82,plain,(
% 2.82/0.76    ( ! [X6,X4,X0,X5] : (k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v5_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 2.82/0.76    inference(cnf_transformation,[],[f53])).
% 2.82/0.76  fof(f53,plain,(
% 2.82/0.76    ! [X0] : (((v5_lattices(X0) | (((k1_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),sK6(X0))) != k1_lattices(X0,k1_lattices(X0,sK4(X0),sK5(X0)),sK6(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v5_lattices(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f49,f52,f51,f50])).
% 2.82/0.76  fof(f50,plain,(
% 2.82/0.76    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k1_lattices(X0,sK4(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK4(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 2.82/0.76    introduced(choice_axiom,[])).
% 2.82/0.76  fof(f51,plain,(
% 2.82/0.76    ! [X0] : (? [X2] : (? [X3] : (k1_lattices(X0,sK4(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK4(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k1_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK4(X0),sK5(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 2.82/0.76    introduced(choice_axiom,[])).
% 2.82/0.76  fof(f52,plain,(
% 2.82/0.76    ! [X0] : (? [X3] : (k1_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK4(X0),sK5(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k1_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),sK6(X0))) != k1_lattices(X0,k1_lattices(X0,sK4(X0),sK5(X0)),sK6(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 2.82/0.76    introduced(choice_axiom,[])).
% 2.82/0.76  fof(f49,plain,(
% 2.82/0.76    ! [X0] : (((v5_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v5_lattices(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.76    inference(rectify,[],[f48])).
% 2.82/0.76  fof(f48,plain,(
% 2.82/0.76    ! [X0] : (((v5_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v5_lattices(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.76    inference(nnf_transformation,[],[f25])).
% 2.82/0.76  fof(f25,plain,(
% 2.82/0.76    ! [X0] : ((v5_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.82/0.76    inference(flattening,[],[f24])).
% 2.82/0.76  fof(f24,plain,(
% 2.82/0.76    ! [X0] : ((v5_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 2.82/0.76    inference(ennf_transformation,[],[f6])).
% 2.82/0.76  fof(f6,axiom,(
% 2.82/0.76    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => (v5_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3))))))),
% 2.82/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattices)).
% 2.82/0.76  fof(f326,plain,(
% 2.82/0.76    m1_subset_1(k4_lattices(sK0,sK1,sK3),u1_struct_0(sK0))),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f103,f71,f69,f107,f100])).
% 2.82/0.76  fof(f106,plain,(
% 2.82/0.76    v5_lattices(sK0)),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f66,f68,f77])).
% 2.82/0.76  fof(f77,plain,(
% 2.82/0.76    ( ! [X0] : (v5_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.82/0.76    inference(cnf_transformation,[],[f21])).
% 2.82/0.76  fof(f1704,plain,(
% 2.82/0.76    k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),sK1)),
% 2.82/0.76    inference(backward_demodulation,[],[f1219,f1703])).
% 2.82/0.76  fof(f1703,plain,(
% 2.82/0.76    k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,sK1,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)))),
% 2.82/0.76    inference(backward_demodulation,[],[f1218,f1676])).
% 2.82/0.76  fof(f1676,plain,(
% 2.82/0.76    k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3)) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3))),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f107,f103,f173,f174,f101])).
% 2.82/0.76  fof(f174,plain,(
% 2.82/0.76    m1_subset_1(k3_lattices(sK0,sK1,sK3),u1_struct_0(sK0))),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f104,f71,f69,f105,f97])).
% 2.82/0.76  fof(f1218,plain,(
% 2.82/0.76    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,sK1,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)))),
% 2.82/0.76    inference(forward_demodulation,[],[f1217,f156])).
% 2.82/0.76  fof(f1217,plain,(
% 2.82/0.76    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,sK1,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)))),
% 2.82/0.76    inference(forward_demodulation,[],[f1216,f1156])).
% 2.82/0.76  fof(f1156,plain,(
% 2.82/0.76    sK1 = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1)),
% 2.82/0.76    inference(forward_demodulation,[],[f1127,f1153])).
% 2.82/0.76  fof(f1153,plain,(
% 2.82/0.76    sK1 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1)),
% 2.82/0.76    inference(backward_demodulation,[],[f1139,f1152])).
% 2.82/0.76  fof(f1152,plain,(
% 2.82/0.76    sK1 = k4_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2))),
% 2.82/0.76    inference(forward_demodulation,[],[f1131,f508])).
% 2.82/0.76  fof(f508,plain,(
% 2.82/0.76    sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2))),
% 2.82/0.76    inference(forward_demodulation,[],[f403,f155])).
% 2.82/0.76  fof(f155,plain,(
% 2.82/0.76    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2)),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f104,f70,f69,f105,f99])).
% 2.82/0.76  fof(f403,plain,(
% 2.82/0.76    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f68,f70,f69,f109,f92])).
% 2.82/0.76  fof(f1131,plain,(
% 2.82/0.76    k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2))),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f107,f103,f69,f173,f101])).
% 2.82/0.76  fof(f1139,plain,(
% 2.82/0.76    k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1) = k4_lattices(sK0,sK1,k3_lattices(sK0,sK1,sK2))),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f107,f103,f69,f173,f102])).
% 2.82/0.76  fof(f1127,plain,(
% 2.82/0.76    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1)),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f107,f103,f69,f173,f101])).
% 2.82/0.76  fof(f1216,plain,(
% 2.82/0.76    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1),k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)))),
% 2.82/0.76    inference(forward_demodulation,[],[f1077,f1154])).
% 2.82/0.76  fof(f1154,plain,(
% 2.82/0.76    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))),
% 2.82/0.76    inference(forward_demodulation,[],[f1129,f1141])).
% 2.82/0.76  fof(f1141,plain,(
% 2.82/0.76    k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f107,f103,f71,f173,f102])).
% 2.82/0.76  fof(f1129,plain,(
% 2.82/0.76    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3)),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f107,f103,f71,f173,f101])).
% 2.82/0.76  fof(f1077,plain,(
% 2.82/0.76    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3))),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f68,f67,f71,f69,f173,f87])).
% 2.82/0.76  fof(f1219,plain,(
% 2.82/0.76    k1_lattices(sK0,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),sK1) = k1_lattices(sK0,sK1,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)))),
% 2.82/0.76    inference(backward_demodulation,[],[f1199,f1218])).
% 2.82/0.76  fof(f1199,plain,(
% 2.82/0.76    k1_lattices(sK0,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),sK1) = k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK1,sK3))),
% 2.82/0.76    inference(forward_demodulation,[],[f1198,f191])).
% 2.82/0.76  fof(f1198,plain,(
% 2.82/0.76    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)),sK1)),
% 2.82/0.76    inference(forward_demodulation,[],[f1197,f1154])).
% 2.82/0.76  fof(f1197,plain,(
% 2.82/0.76    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3),sK1)),
% 2.82/0.76    inference(forward_demodulation,[],[f1083,f1156])).
% 2.82/0.76  fof(f1083,plain,(
% 2.82/0.76    k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK3),k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK1))),
% 2.82/0.76    inference(unit_resulting_resolution,[],[f65,f68,f67,f69,f71,f173,f87])).
% 2.82/0.76  % SZS output end Proof for theBenchmark
% 2.82/0.76  % (9203)------------------------------
% 2.82/0.76  % (9203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.82/0.76  % (9203)Termination reason: Refutation
% 2.82/0.76  
% 2.82/0.76  % (9203)Memory used [KB]: 13432
% 2.82/0.76  % (9203)Time elapsed: 0.335 s
% 2.82/0.76  % (9203)------------------------------
% 2.82/0.76  % (9203)------------------------------
% 2.82/0.77  % (9173)Success in time 0.411 s
%------------------------------------------------------------------------------
