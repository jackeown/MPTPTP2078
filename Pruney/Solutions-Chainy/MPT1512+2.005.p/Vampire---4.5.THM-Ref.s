%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  211 (1326 expanded)
%              Number of leaves         :   28 ( 413 expanded)
%              Depth                    :   28
%              Number of atoms          : 1055 (8652 expanded)
%              Number of equality atoms :   33 ( 139 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f396,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f135,f169,f180,f245,f252,f269,f279,f288,f299,f320,f395])).

fof(f395,plain,
    ( spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f394])).

fof(f394,plain,
    ( $false
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f393,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1))
      | ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) )
    & r1_tarski(sK1,sK2)
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
              | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
            & r1_tarski(X1,X2) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,X2),k16_lattice3(sK0,X1))
            | ~ r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2,X1] :
        ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,X2),k16_lattice3(sK0,X1))
          | ~ r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2)) )
        & r1_tarski(X1,X2) )
   => ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1))
        | ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) )
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            | ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
              & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).

fof(f393,plain,
    ( v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f392,f58])).

fof(f58,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f392,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f391,f162])).

fof(f162,plain,
    ( m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl8_6
  <=> m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f391,plain,
    ( ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f389,f234])).

fof(f234,plain,
    ( ~ r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f233,f55])).

fof(f233,plain,
    ( ~ r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f232,f56])).

fof(f56,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f232,plain,
    ( ~ r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f231,f57])).

fof(f57,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f231,plain,
    ( ~ r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f230,f58])).

fof(f230,plain,
    ( ~ r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1)
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f228,f162])).

fof(f228,plain,
    ( ~ r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(resolution,[],[f223,f87])).

fof(f87,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r4_lattice3(X1,sK7(X0,X1,X2),X2)
            & sK7(X0,X1,X2) = X0
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK7(X0,X1,X2),X2)
        & sK7(X0,X1,X2) = X0
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r4_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r4_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(f223,plain,
    ( ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),a_2_2_lattice3(sK0,sK1))
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(resolution,[],[f222,f120])).

fof(f120,plain,(
    ! [X0] : r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0)) ),
    inference(superposition,[],[f119,f101])).

fof(f101,plain,(
    ! [X0] : k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0)) ),
    inference(subsumption_resolution,[],[f100,f55])).

fof(f100,plain,(
    ! [X0] :
      ( k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f99,f56])).

fof(f99,plain,(
    ! [X0] :
      ( k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f98,f58])).

fof(f98,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f61,f57])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

fof(f119,plain,(
    ! [X0] : r3_lattice3(sK0,k16_lattice3(sK0,X0),X0) ),
    inference(subsumption_resolution,[],[f118,f55])).

fof(f118,plain,(
    ! [X0] :
      ( r3_lattice3(sK0,k16_lattice3(sK0,X0),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f56])).

fof(f117,plain,(
    ! [X0] :
      ( r3_lattice3(sK0,k16_lattice3(sK0,X0),X0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f116,f58])).

fof(f116,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | r3_lattice3(sK0,k16_lattice3(sK0,X0),X0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f115,f57])).

fof(f115,plain,(
    ! [X2,X0] :
      ( ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f86,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f86,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK3(X0,X1,X2),X2)
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
        & r3_lattice3(X0,sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(f222,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK0,k15_lattice3(sK0,sK1),X0)
        | ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),X0) )
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f221,f162])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK0,k15_lattice3(sK0,sK1),X0)
        | ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),X0)
        | ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0)) )
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f218,f133])).

fof(f133,plain,
    ( m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl8_4
  <=> m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK0,k15_lattice3(sK0,sK1),X0)
        | ~ m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),X0)
        | ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0)) )
    | spl8_3 ),
    inference(resolution,[],[f215,f130])).

fof(f130,plain,
    ( ~ r3_lattice3(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl8_3
  <=> r3_lattice3(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f215,plain,(
    ! [X4,X5,X3] :
      ( r3_lattice3(sK0,X3,X4)
      | ~ r3_lattice3(sK0,X3,X5)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(sK5(sK0,X3,X4),X5)
      | ~ m1_subset_1(sK5(sK0,X3,X4),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f214,f55])).

fof(f214,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK5(sK0,X3,X4),u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X3,X5)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(sK5(sK0,X3,X4),X5)
      | r3_lattice3(sK0,X3,X4)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f210,f58])).

fof(f210,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK5(sK0,X3,X4),u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X3,X5)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(sK5(sK0,X3,X4),X5)
      | r3_lattice3(sK0,X3,X4)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f209])).

fof(f209,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK5(sK0,X3,X4),u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X3,X5)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(sK5(sK0,X3,X4),X5)
      | r3_lattice3(sK0,X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f207,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,sK5(X0,X1,X2))
      | r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK5(X0,X1,X2))
                  & r2_hidden(sK5(X0,X1,X2),X2)
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X2)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X1,X3)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(sK0,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f206,f55])).

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,X2,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f72,f58])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattices(X0,X1,X4)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f389,plain,
    ( r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(resolution,[],[f387,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
                  & r2_hidden(sK4(X0,X1,X2),X2)
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X2)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X3,X1)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

fof(f387,plain,
    ( ~ r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),sK1)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(resolution,[],[f386,f59])).

fof(f59,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f386,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),X0) )
    | spl8_3
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(resolution,[],[f380,f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f380,plain,
    ( ~ r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),sK2)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f379,f55])).

fof(f379,plain,
    ( ~ r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),sK2)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f378,f58])).

fof(f378,plain,
    ( ~ r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),sK2)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f377,f133])).

fof(f377,plain,
    ( ~ r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),sK2)
    | ~ m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f374,f130])).

fof(f374,plain,
    ( ~ r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),sK2)
    | r3_lattice3(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2))
    | ~ m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_7 ),
    inference(resolution,[],[f240,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),a_2_2_lattice3(sK0,X0))
        | ~ r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),X0) )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl8_7
  <=> ! [X0] :
        ( ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),a_2_2_lattice3(sK0,X0))
        | ~ r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f320,plain,
    ( spl8_9
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | spl8_9
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f318,f55])).

fof(f318,plain,
    ( v2_struct_0(sK0)
    | spl8_9
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f317,f58])).

fof(f317,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_9
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f316,f267])).

fof(f267,plain,
    ( m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl8_10
  <=> m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f316,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_9
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f314,f264])).

fof(f264,plain,
    ( ~ r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl8_9
  <=> r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f314,plain,
    ( r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f312,f74])).

fof(f312,plain,
    ( ~ r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl8_12 ),
    inference(resolution,[],[f311,f59])).

fof(f311,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),X0) )
    | ~ spl8_12 ),
    inference(resolution,[],[f306,f78])).

fof(f306,plain,
    ( ~ r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),sK2)
    | ~ spl8_12 ),
    inference(resolution,[],[f278,f119])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK0,k16_lattice3(sK0,sK2),X0)
        | ~ r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),X0) )
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl8_12
  <=> ! [X0] :
        ( ~ r3_lattice3(sK0,k16_lattice3(sK0,sK2),X0)
        | ~ r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f299,plain,
    ( spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f297,f55])).

fof(f297,plain,
    ( v2_struct_0(sK0)
    | spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f296,f58])).

fof(f296,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_9
    | ~ spl8_10
    | spl8_11 ),
    inference(subsumption_resolution,[],[f295,f267])).

fof(f295,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_9
    | spl8_11 ),
    inference(subsumption_resolution,[],[f293,f264])).

fof(f293,plain,
    ( r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_11 ),
    inference(resolution,[],[f275,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f275,plain,
    ( ~ m1_subset_1(sK5(sK0,k16_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | spl8_11 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl8_11
  <=> m1_subset_1(sK5(sK0,k16_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f288,plain,(
    spl8_10 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | spl8_10 ),
    inference(subsumption_resolution,[],[f286,f55])).

fof(f286,plain,
    ( v2_struct_0(sK0)
    | spl8_10 ),
    inference(subsumption_resolution,[],[f284,f58])).

fof(f284,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_10 ),
    inference(resolution,[],[f268,f77])).

fof(f268,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f266])).

fof(f279,plain,
    ( ~ spl8_11
    | ~ spl8_10
    | spl8_12
    | spl8_9 ),
    inference(avatar_split_clause,[],[f270,f262,f277,f266,f273])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK0,k16_lattice3(sK0,sK2),X0)
        | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),X0)
        | ~ m1_subset_1(sK5(sK0,k16_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) )
    | spl8_9 ),
    inference(resolution,[],[f264,f215])).

fof(f269,plain,
    ( ~ spl8_9
    | ~ spl8_10
    | spl8_2 ),
    inference(avatar_split_clause,[],[f260,f93,f266,f262])).

fof(f93,plain,
    ( spl8_2
  <=> r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f260,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1)
    | spl8_2 ),
    inference(resolution,[],[f95,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X0,k16_lattice3(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f123,f55])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f122,f56])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f121,f58])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r3_lattices(sK0,X0,k16_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f62,f57])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,k16_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
             => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).

fof(f95,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f252,plain,
    ( spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | spl8_8 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | spl8_8 ),
    inference(subsumption_resolution,[],[f250,f55])).

fof(f250,plain,
    ( v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | spl8_8 ),
    inference(subsumption_resolution,[],[f249,f58])).

fof(f249,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | spl8_8 ),
    inference(subsumption_resolution,[],[f248,f162])).

fof(f248,plain,
    ( ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | spl8_8 ),
    inference(subsumption_resolution,[],[f246,f234])).

fof(f246,plain,
    ( r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_8 ),
    inference(resolution,[],[f244,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f244,plain,
    ( ~ m1_subset_1(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),u1_struct_0(sK0))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl8_8
  <=> m1_subset_1(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f245,plain,
    ( spl8_7
    | ~ spl8_8
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f237,f161,f132,f128,f242,f239])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),a_2_2_lattice3(sK0,X0))
        | ~ r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),X0) )
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f235,f162])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),a_2_2_lattice3(sK0,X0))
        | ~ r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),X0) )
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(resolution,[],[f234,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X2))
      | ~ r2_hidden(sK4(sK0,X0,X1),X2) ) ),
    inference(subsumption_resolution,[],[f144,f55])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X2))
      | r4_lattice3(sK0,X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f143,f58])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X2))
      | r4_lattice3(sK0,X0,X1)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(sK0,X0,X1),X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X2))
      | r4_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f139,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f139,plain,(
    ! [X4,X5,X3] :
      ( r1_lattices(sK0,X3,X5)
      | ~ r2_hidden(X3,X4)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X5,a_2_2_lattice3(sK0,X4)) ) ),
    inference(resolution,[],[f137,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r4_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f113,f55])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r4_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f112,f56])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r4_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f111,f57])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r4_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f110,f58])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r4_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r4_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1))
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f108,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( sK7(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r4_lattice3(sK0,sK7(X0,sK0,X1),X1)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f107,f55])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1))
      | r4_lattice3(sK0,sK7(X0,sK0,X1),X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f106,f56])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1))
      | r4_lattice3(sK0,sK7(X0,sK0,X1),X1)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f105,f58])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | r4_lattice3(sK0,sK7(X0,sK0,X1),X1)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f83,f57])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X1)
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | r4_lattice3(X1,sK7(X0,X1,X2),X2)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_lattice3(sK0,X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X2) ) ),
    inference(subsumption_resolution,[],[f136,f55])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X2)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f68,f58])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattices(X0,X4,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f180,plain,
    ( spl8_3
    | ~ spl8_4
    | spl8_6 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl8_3
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f178,f55])).

fof(f178,plain,
    ( v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f177,f58])).

fof(f177,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | ~ spl8_4
    | spl8_6 ),
    inference(subsumption_resolution,[],[f176,f133])).

fof(f176,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_3
    | spl8_6 ),
    inference(subsumption_resolution,[],[f174,f130])).

fof(f174,plain,
    ( r3_lattice3(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2))
    | ~ m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_6 ),
    inference(resolution,[],[f163,f73])).

fof(f163,plain,
    ( ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f161])).

fof(f169,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl8_4 ),
    inference(subsumption_resolution,[],[f167,f55])).

fof(f167,plain,
    ( v2_struct_0(sK0)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f165,f58])).

fof(f165,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_4 ),
    inference(resolution,[],[f134,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f134,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f135,plain,
    ( ~ spl8_3
    | ~ spl8_4
    | spl8_1 ),
    inference(avatar_split_clause,[],[f126,f89,f132,f128])).

fof(f89,plain,
    ( spl8_1
  <=> r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f126,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0))
    | ~ r3_lattice3(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2))
    | spl8_1 ),
    inference(resolution,[],[f125,f91])).

fof(f91,plain,
    ( ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X1,k15_lattice3(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X1,a_2_2_lattice3(sK0,X0)) ) ),
    inference(superposition,[],[f124,f101])).

fof(f96,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f60,f93,f89])).

fof(f60,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:41:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (15415)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.46  % (15422)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.48  % (15415)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f396,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f96,f135,f169,f180,f245,f252,f269,f279,f288,f299,f320,f395])).
% 0.21/0.48  fof(f395,plain,(
% 0.21/0.48    spl8_3 | ~spl8_4 | ~spl8_6 | ~spl8_7),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f394])).
% 0.21/0.48  fof(f394,plain,(
% 0.21/0.48    $false | (spl8_3 | ~spl8_4 | ~spl8_6 | ~spl8_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f393,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ((~r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1)) | ~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))) & r1_tarski(sK1,sK2)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f32,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X2,X1] : ((~r3_lattices(sK0,k16_lattice3(sK0,X2),k16_lattice3(sK0,X1)) | ~r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2))) & r1_tarski(X1,X2)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ? [X2,X1] : ((~r3_lattices(sK0,k16_lattice3(sK0,X2),k16_lattice3(sK0,X1)) | ~r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2))) & r1_tarski(X1,X2)) => ((~r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1)) | ~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))) & r1_tarski(sK1,sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : (? [X1,X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) & r1_tarski(X1,X2)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).
% 0.21/0.49  fof(f393,plain,(
% 0.21/0.49    v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_6 | ~spl8_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f392,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    l3_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f392,plain,(
% 0.21/0.49    ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_6 | ~spl8_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f391,f162])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0)) | ~spl8_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f161])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    spl8_6 <=> m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.49  fof(f391,plain,(
% 0.21/0.49    ~m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_6 | ~spl8_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f389,f234])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    ~r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1) | (spl8_3 | ~spl8_4 | ~spl8_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f233,f55])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    ~r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f232,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    v10_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ~r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f231,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    v4_lattice3(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ~r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f230,f58])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ~r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f228,f162])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    ~r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1) | ~m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_6)),
% 0.21/0.49    inference(resolution,[],[f223,f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK7(X0,X1,X2),X2) & sK7(X0,X1,X2) = X0 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f52,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK7(X0,X1,X2),X2) & sK7(X0,X1,X2) = X0 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 0.21/0.49    inference(rectify,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),a_2_2_lattice3(sK0,sK1)) | (spl8_3 | ~spl8_4 | ~spl8_6)),
% 0.21/0.49    inference(resolution,[],[f222,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ( ! [X0] : (r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0))) )),
% 0.21/0.49    inference(superposition,[],[f119,f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f100,f55])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f99,f56])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f98,f58])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X0] : (~l3_lattices(sK0) | k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f61,f57])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_lattice3(X0) | ~l3_lattices(X0) | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ( ! [X0] : (r3_lattice3(sK0,k16_lattice3(sK0,X0),X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f118,f55])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ( ! [X0] : (r3_lattice3(sK0,k16_lattice3(sK0,X0),X0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f117,f56])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ( ! [X0] : (r3_lattice3(sK0,k16_lattice3(sK0,X0),X0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f116,f58])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    ( ! [X0] : (~l3_lattices(sK0) | r3_lattice3(sK0,k16_lattice3(sK0,X0),X0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f115,f57])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~v4_lattice3(X0) | ~l3_lattices(X0) | r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f86,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK3(X0,X1,X2),X1) & r3_lattice3(X0,sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(rectify,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ( ! [X0] : (~r3_lattice3(sK0,k15_lattice3(sK0,sK1),X0) | ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),X0)) ) | (spl8_3 | ~spl8_4 | ~spl8_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f221,f162])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ( ! [X0] : (~r3_lattice3(sK0,k15_lattice3(sK0,sK1),X0) | ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),X0) | ~m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0))) ) | (spl8_3 | ~spl8_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f218,f133])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0)) | ~spl8_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f132])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl8_4 <=> m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    ( ! [X0] : (~r3_lattice3(sK0,k15_lattice3(sK0,sK1),X0) | ~m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0)) | ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),X0) | ~m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0))) ) | spl8_3),
% 0.21/0.49    inference(resolution,[],[f215,f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~r3_lattice3(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)) | spl8_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl8_3 <=> r3_lattice3(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (r3_lattice3(sK0,X3,X4) | ~r3_lattice3(sK0,X3,X5) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(sK5(sK0,X3,X4),X5) | ~m1_subset_1(sK5(sK0,X3,X4),u1_struct_0(sK0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f214,f55])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~m1_subset_1(sK5(sK0,X3,X4),u1_struct_0(sK0)) | ~r3_lattice3(sK0,X3,X5) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(sK5(sK0,X3,X4),X5) | r3_lattice3(sK0,X3,X4) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f210,f58])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~m1_subset_1(sK5(sK0,X3,X4),u1_struct_0(sK0)) | ~r3_lattice3(sK0,X3,X5) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(sK5(sK0,X3,X4),X5) | r3_lattice3(sK0,X3,X4) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f209])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~m1_subset_1(sK5(sK0,X3,X4),u1_struct_0(sK0)) | ~r3_lattice3(sK0,X3,X5) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(sK5(sK0,X3,X4),X5) | r3_lattice3(sK0,X3,X4) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f207,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,sK5(X0,X1,X2)) | r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK5(X0,X1,X2)) & r2_hidden(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(rectify,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_lattices(sK0,X2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f206,f55])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,X2,X0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f72,f58])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (~l3_lattices(X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattices(X0,X1,X4) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f389,plain,(
% 0.21/0.49    r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1) | ~m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_7)),
% 0.21/0.49    inference(resolution,[],[f387,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(rectify,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 0.21/0.49  fof(f387,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),sK1) | (spl8_3 | ~spl8_4 | ~spl8_7)),
% 0.21/0.49    inference(resolution,[],[f386,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f386,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK2) | ~r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),X0)) ) | (spl8_3 | ~spl8_4 | ~spl8_7)),
% 0.21/0.49    inference(resolution,[],[f380,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.49  fof(f380,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),sK2) | (spl8_3 | ~spl8_4 | ~spl8_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f379,f55])).
% 0.21/0.49  fof(f379,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),sK2) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f378,f58])).
% 0.21/0.49  fof(f378,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),sK2) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f377,f133])).
% 0.21/0.49  fof(f377,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),sK2) | ~m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl8_3 | ~spl8_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f374,f130])).
% 0.21/0.49  fof(f374,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),sK2) | r3_lattice3(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)) | ~m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl8_7),
% 0.21/0.49    inference(resolution,[],[f240,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),a_2_2_lattice3(sK0,X0)) | ~r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),X0)) ) | ~spl8_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f239])).
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    spl8_7 <=> ! [X0] : (~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),a_2_2_lattice3(sK0,X0)) | ~r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.49  fof(f320,plain,(
% 0.21/0.49    spl8_9 | ~spl8_10 | ~spl8_12),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f319])).
% 0.21/0.49  fof(f319,plain,(
% 0.21/0.49    $false | (spl8_9 | ~spl8_10 | ~spl8_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f318,f55])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    v2_struct_0(sK0) | (spl8_9 | ~spl8_10 | ~spl8_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f317,f58])).
% 0.21/0.49  fof(f317,plain,(
% 0.21/0.49    ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl8_9 | ~spl8_10 | ~spl8_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f316,f267])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~spl8_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f266])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    spl8_10 <=> m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl8_9 | ~spl8_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f314,f264])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    ~r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1) | spl8_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f262])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    spl8_9 <=> r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl8_12),
% 0.21/0.49    inference(resolution,[],[f312,f74])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    ~r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),sK1) | ~spl8_12),
% 0.21/0.49    inference(resolution,[],[f311,f59])).
% 0.21/0.49  fof(f311,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK2) | ~r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),X0)) ) | ~spl8_12),
% 0.21/0.49    inference(resolution,[],[f306,f78])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    ~r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),sK2) | ~spl8_12),
% 0.21/0.49    inference(resolution,[],[f278,f119])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    ( ! [X0] : (~r3_lattice3(sK0,k16_lattice3(sK0,sK2),X0) | ~r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),X0)) ) | ~spl8_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f277])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    spl8_12 <=> ! [X0] : (~r3_lattice3(sK0,k16_lattice3(sK0,sK2),X0) | ~r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    spl8_9 | ~spl8_10 | spl8_11),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f298])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    $false | (spl8_9 | ~spl8_10 | spl8_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f297,f55])).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    v2_struct_0(sK0) | (spl8_9 | ~spl8_10 | spl8_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f296,f58])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl8_9 | ~spl8_10 | spl8_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f295,f267])).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl8_9 | spl8_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f293,f264])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | spl8_11),
% 0.21/0.49    inference(resolution,[],[f275,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    ~m1_subset_1(sK5(sK0,k16_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | spl8_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f273])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    spl8_11 <=> m1_subset_1(sK5(sK0,k16_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    spl8_10),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f287])).
% 0.21/0.49  fof(f287,plain,(
% 0.21/0.49    $false | spl8_10),
% 0.21/0.49    inference(subsumption_resolution,[],[f286,f55])).
% 0.21/0.49  fof(f286,plain,(
% 0.21/0.49    v2_struct_0(sK0) | spl8_10),
% 0.21/0.49    inference(subsumption_resolution,[],[f284,f58])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl8_10),
% 0.21/0.49    inference(resolution,[],[f268,f77])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | spl8_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f266])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    ~spl8_11 | ~spl8_10 | spl8_12 | spl8_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f270,f262,f277,f266,f273])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    ( ! [X0] : (~r3_lattice3(sK0,k16_lattice3(sK0,sK2),X0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~r2_hidden(sK5(sK0,k16_lattice3(sK0,sK2),sK1),X0) | ~m1_subset_1(sK5(sK0,k16_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))) ) | spl8_9),
% 0.21/0.49    inference(resolution,[],[f264,f215])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    ~spl8_9 | ~spl8_10 | spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f260,f93,f266,f262])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl8_2 <=> r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k16_lattice3(sK0,sK2),sK1) | spl8_2),
% 0.21/0.49    inference(resolution,[],[f95,f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f123,f55])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f122,f56])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f121,f58])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r3_lattices(sK0,X0,k16_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f62,f57])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ~r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1)) | spl8_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    spl8_3 | ~spl8_4 | ~spl8_6 | spl8_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f251])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    $false | (spl8_3 | ~spl8_4 | ~spl8_6 | spl8_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f250,f55])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_6 | spl8_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f249,f58])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_6 | spl8_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f248,f162])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    ~m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | ~spl8_6 | spl8_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f246,f234])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    r4_lattice3(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1) | ~m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | spl8_8),
% 0.21/0.49    inference(resolution,[],[f244,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    ~m1_subset_1(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),u1_struct_0(sK0)) | spl8_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f242])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    spl8_8 <=> m1_subset_1(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    spl8_7 | ~spl8_8 | spl8_3 | ~spl8_4 | ~spl8_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f237,f161,f132,f128,f242,f239])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),u1_struct_0(sK0)) | ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),a_2_2_lattice3(sK0,X0)) | ~r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),X0)) ) | (spl8_3 | ~spl8_4 | ~spl8_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f235,f162])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),u1_struct_0(sK0)) | ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),a_2_2_lattice3(sK0,X0)) | ~r2_hidden(sK4(sK0,sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),sK1),X0)) ) | (spl8_3 | ~spl8_4 | ~spl8_6)),
% 0.21/0.49    inference(resolution,[],[f234,f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X2)) | ~r2_hidden(sK4(sK0,X0,X1),X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f144,f55])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X2)) | r4_lattice3(sK0,X0,X1) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f143,f58])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X2)) | r4_lattice3(sK0,X0,X1) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f140])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK4(sK0,X0,X1),X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,X0,X1),u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X2)) | r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f139,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_lattices(X0,sK4(X0,X1,X2),X1) | r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (r1_lattices(sK0,X3,X5) | ~r2_hidden(X3,X4) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X5,a_2_2_lattice3(sK0,X4))) )),
% 0.21/0.49    inference(resolution,[],[f137,f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r4_lattice3(sK0,X0,X1) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X1))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f113,f55])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r4_lattice3(sK0,X0,X1) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X1)) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f112,f56])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r4_lattice3(sK0,X0,X1) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f111,f57])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r4_lattice3(sK0,X0,X1) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X1)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f110,f58])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r4_lattice3(sK0,X0,X1) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X1)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r4_lattice3(sK0,X0,X1) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X1)) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X1)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(superposition,[],[f108,f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sK7(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f54])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r4_lattice3(sK0,sK7(X0,sK0,X1),X1) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X1))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f107,f55])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,a_2_2_lattice3(sK0,X1)) | r4_lattice3(sK0,sK7(X0,sK0,X1),X1) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f106,f56])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,a_2_2_lattice3(sK0,X1)) | r4_lattice3(sK0,sK7(X0,sK0,X1),X1) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f105,f58])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,a_2_2_lattice3(sK0,X1)) | ~l3_lattices(sK0) | r4_lattice3(sK0,sK7(X0,sK0,X1),X1) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f83,f57])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v4_lattice3(X1) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | r4_lattice3(X1,sK7(X0,X1,X2),X2) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f54])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r4_lattice3(sK0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f136,f55])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X2) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f68,f58])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (~l3_lattices(X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattices(X0,X4,X1) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    spl8_3 | ~spl8_4 | spl8_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f179])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    $false | (spl8_3 | ~spl8_4 | spl8_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f178,f55])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | spl8_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f177,f58])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl8_3 | ~spl8_4 | spl8_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f176,f133])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    ~m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl8_3 | spl8_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f174,f130])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    r3_lattice3(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)) | ~m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | spl8_6),
% 0.21/0.49    inference(resolution,[],[f163,f73])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ~m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)),u1_struct_0(sK0)) | spl8_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f161])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    spl8_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f168])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    $false | spl8_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f167,f55])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    v2_struct_0(sK0) | spl8_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f165,f58])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl8_4),
% 0.21/0.49    inference(resolution,[],[f134,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ~m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0)) | spl8_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f132])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ~spl8_3 | ~spl8_4 | spl8_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f126,f89,f132,f128])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl8_1 <=> r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ~m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k15_lattice3(sK0,sK1),a_2_2_lattice3(sK0,sK2)) | spl8_1),
% 0.21/0.49    inference(resolution,[],[f125,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) | spl8_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f89])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r3_lattices(sK0,X1,k15_lattice3(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X1,a_2_2_lattice3(sK0,X0))) )),
% 0.21/0.49    inference(superposition,[],[f124,f101])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ~spl8_1 | ~spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f60,f93,f89])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ~r3_lattices(sK0,k16_lattice3(sK0,sK2),k16_lattice3(sK0,sK1)) | ~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (15415)------------------------------
% 0.21/0.49  % (15415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15415)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (15415)Memory used [KB]: 11001
% 0.21/0.49  % (15415)Time elapsed: 0.074 s
% 0.21/0.49  % (15415)------------------------------
% 0.21/0.49  % (15415)------------------------------
% 0.21/0.49  % (15411)Success in time 0.133 s
%------------------------------------------------------------------------------
