%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 (3623 expanded)
%              Number of leaves         :   12 (1038 expanded)
%              Depth                    :   23
%              Number of atoms          :  444 (28972 expanded)
%              Number of equality atoms :   27 ( 264 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    8 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f63,f107,f159])).

fof(f159,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f37,f38,f56,f112,f110,f148,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
                  & r2_hidden(sK3(X0,X1,X2),X2)
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(f148,plain,
    ( r2_hidden(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),sK0)
    | spl5_2 ),
    inference(backward_demodulation,[],[f135,f145])).

fof(f145,plain,
    ( sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = sK4(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1)
    | spl5_2 ),
    inference(forward_demodulation,[],[f144,f113])).

fof(f113,plain,
    ( sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f110,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).

fof(f36,plain,(
    v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
      | ~ r3_lattice3(sK1,sK2,sK0) )
    & ( r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
      | r3_lattice3(sK1,sK2,sK0) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v17_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
              | ~ r3_lattice3(X1,X2,X0) )
            & ( r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
              | r3_lattice3(X1,X2,X0) )
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l3_lattices(X1)
        & v17_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ r4_lattice3(sK1,k7_lattices(sK1,X2),a_2_0_lattice3(sK0,sK1))
            | ~ r3_lattice3(sK1,X2,sK0) )
          & ( r4_lattice3(sK1,k7_lattices(sK1,X2),a_2_0_lattice3(sK0,sK1))
            | r3_lattice3(sK1,X2,sK0) )
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v17_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ( ~ r4_lattice3(sK1,k7_lattices(sK1,X2),a_2_0_lattice3(sK0,sK1))
          | ~ r3_lattice3(sK1,X2,sK0) )
        & ( r4_lattice3(sK1,k7_lattices(sK1,X2),a_2_0_lattice3(sK0,sK1))
          | r3_lattice3(sK1,X2,sK0) )
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ( ~ r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
        | ~ r3_lattice3(sK1,sK2,sK0) )
      & ( r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
        | r3_lattice3(sK1,sK2,sK0) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | ~ r3_lattice3(X1,X2,X0) )
          & ( r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | r3_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | ~ r3_lattice3(X1,X2,X0) )
          & ( r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | r3_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r3_lattice3(X1,X2,X0)
          <~> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r3_lattice3(X1,X2,X0)
          <~> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( l3_lattices(X1)
          & v17_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( r3_lattice3(X1,X2,X0)
            <=> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v17_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r3_lattice3(X1,X2,X0)
          <=> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_lattice3)).

fof(f35,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f144,plain,
    ( k7_lattices(sK1,k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)))) = sK4(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1)
    | spl5_2 ),
    inference(forward_demodulation,[],[f138,f134])).

fof(f134,plain,
    ( k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))) = k7_lattices(sK1,sK4(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f132,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X2,sK4(X0,X1,X2)) = X0
      | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | k7_lattices(X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & k7_lattices(X2,sK4(X0,X1,X2)) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & k7_lattices(X2,X4) = X0
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & k7_lattices(X2,sK4(X0,X1,X2)) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | k7_lattices(X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & k7_lattices(X2,X4) = X0
              & m1_subset_1(X4,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | k7_lattices(X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & k7_lattices(X2,X3) = X0
              & m1_subset_1(X3,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & k7_lattices(X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & k7_lattices(X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X2)
        & v17_lattices(X2)
        & v10_lattices(X2)
        & ~ v2_struct_0(X2) )
     => ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & k7_lattices(X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_lattice3)).

fof(f132,plain,
    ( r2_hidden(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),a_2_0_lattice3(sK0,sK1))
    | spl5_2 ),
    inference(backward_demodulation,[],[f123,f129])).

fof(f129,plain,
    ( k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))) = sK4(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1)
    | spl5_2 ),
    inference(forward_demodulation,[],[f126,f122])).

fof(f122,plain,
    ( sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,sK4(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f111,f50])).

fof(f111,plain,
    ( r2_hidden(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f37,f38,f109,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f109,plain,
    ( ~ r3_lattice3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | spl5_2 ),
    inference(forward_demodulation,[],[f108,f64])).

fof(f64,plain,(
    sK2 = k7_lattices(sK1,k7_lattices(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f38,f41])).

fof(f108,plain,
    ( ~ r3_lattice3(sK1,k7_lattices(sK1,k7_lattices(sK1,sK2)),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f65,f61,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,X2,X0)
      | ~ r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v17_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r4_lattice3(X1,X2,X0)
              | ~ r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
            & ( r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
              | ~ r4_lattice3(X1,X2,X0) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v17_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v17_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v17_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v17_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r4_lattice3(X1,X2,X0)
          <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattice3)).

fof(f61,plain,
    ( ~ r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_2
  <=> r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f65,plain,(
    m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f34,f37,f38,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f126,plain,
    ( sK4(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1) = k7_lattices(sK1,k7_lattices(sK1,sK4(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1)))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f121,f41])).

fof(f121,plain,
    ( m1_subset_1(sK4(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),u1_struct_0(sK1))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f111,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X2))
      | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f123,plain,
    ( r2_hidden(sK4(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),a_2_0_lattice3(sK0,sK1))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f111,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f138,plain,
    ( sK4(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1) = k7_lattices(sK1,k7_lattices(sK1,sK4(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1)))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f133,f41])).

fof(f133,plain,
    ( m1_subset_1(sK4(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),u1_struct_0(sK1))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f132,f49])).

fof(f135,plain,
    ( r2_hidden(sK4(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),sK0)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f132,f51])).

fof(f110,plain,
    ( m1_subset_1(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),u1_struct_0(sK1))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f37,f38,f109,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f112,plain,
    ( ~ r1_lattices(sK1,sK2,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f37,f38,f109,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,
    ( r3_lattice3(sK1,sK2,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl5_1
  <=> r3_lattice3(sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f38,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f107,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f37,f38,f68,f84,f66,f93,f42])).

fof(f93,plain,
    ( r2_hidden(sK3(sK1,sK2,sK0),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | spl5_1 ),
    inference(forward_demodulation,[],[f92,f79])).

fof(f79,plain,
    ( sK3(sK1,sK2,sK0) = k7_lattices(sK1,k7_lattices(sK1,sK3(sK1,sK2,sK0)))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f66,f41])).

fof(f92,plain,
    ( r2_hidden(k7_lattices(sK1,k7_lattices(sK1,sK3(sK1,sK2,sK0))),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f80,f81,f53])).

fof(f53,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k7_lattices(X2,X3),a_2_0_lattice3(X1,X2))
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | ~ r2_hidden(X3,X1)
      | k7_lattices(X2,X3) != X0
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,
    ( r2_hidden(k7_lattices(sK1,sK3(sK1,sK2,sK0)),a_2_0_lattice3(sK0,sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f67,f66,f53])).

fof(f67,plain,
    ( r2_hidden(sK3(sK1,sK2,sK0),sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f34,f37,f38,f57,f44])).

fof(f57,plain,
    ( ~ r3_lattice3(sK1,sK2,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f80,plain,
    ( m1_subset_1(k7_lattices(sK1,sK3(sK1,sK2,sK0)),u1_struct_0(sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f34,f37,f66,f48])).

fof(f66,plain,
    ( m1_subset_1(sK3(sK1,sK2,sK0),u1_struct_0(sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f34,f37,f38,f57,f43])).

fof(f84,plain,
    ( r3_lattice3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f83,f64])).

fof(f83,plain,
    ( r3_lattice3(sK1,k7_lattices(sK1,k7_lattices(sK1,sK2)),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f65,f60,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
      | ~ r4_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v17_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,
    ( r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f68,plain,
    ( ~ r1_lattices(sK1,sK2,sK3(sK1,sK2,sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f34,f37,f38,f57,f45])).

fof(f63,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f39,f59,f55])).

fof(f39,plain,
    ( r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
    | r3_lattice3(sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f40,f59,f55])).

fof(f40,plain,
    ( ~ r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
    | ~ r3_lattice3(sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:31:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (13720)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (13715)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (13730)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (13728)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (13722)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (13723)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.53  % (13718)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (13717)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.55  % (13719)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.55  % (13729)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.56  % (13732)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.56  % (13716)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (13735)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.56  % (13733)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.56  % (13716)Refutation not found, incomplete strategy% (13716)------------------------------
% 0.22/0.56  % (13716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (13716)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (13716)Memory used [KB]: 10618
% 0.22/0.56  % (13716)Time elapsed: 0.125 s
% 0.22/0.56  % (13716)------------------------------
% 0.22/0.56  % (13716)------------------------------
% 0.22/0.56  % (13735)Refutation not found, incomplete strategy% (13735)------------------------------
% 0.22/0.56  % (13735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (13735)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (13735)Memory used [KB]: 10490
% 0.22/0.56  % (13735)Time elapsed: 0.127 s
% 0.22/0.56  % (13735)------------------------------
% 0.22/0.56  % (13735)------------------------------
% 0.22/0.57  % (13721)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.57  % (13724)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.57  % (13734)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.58  % (13731)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.58  % (13726)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.58  % (13725)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.58  % (13727)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.58  % (13726)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.60  fof(f160,plain,(
% 0.22/0.60    $false),
% 0.22/0.60    inference(avatar_sat_refutation,[],[f62,f63,f107,f159])).
% 0.22/0.60  fof(f159,plain,(
% 0.22/0.60    ~spl5_1 | spl5_2),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f157])).
% 0.22/0.60  fof(f157,plain,(
% 0.22/0.60    $false | (~spl5_1 | spl5_2)),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f37,f38,f56,f112,f110,f148,f42])).
% 0.22/0.60  fof(f42,plain,(
% 0.22/0.60    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f28])).
% 0.22/0.60  fof(f28,plain,(
% 0.22/0.60    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 0.22/0.60  fof(f27,plain,(
% 0.22/0.60    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X2) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f26,plain,(
% 0.22/0.60    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.60    inference(rectify,[],[f25])).
% 0.22/0.60  fof(f25,plain,(
% 0.22/0.60    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.60    inference(nnf_transformation,[],[f13])).
% 0.22/0.60  fof(f13,plain,(
% 0.22/0.60    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.60    inference(flattening,[],[f12])).
% 0.22/0.60  fof(f12,plain,(
% 0.22/0.60    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f3])).
% 0.22/0.60  fof(f3,axiom,(
% 0.22/0.60    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 0.22/0.60  fof(f148,plain,(
% 0.22/0.60    r2_hidden(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),sK0) | spl5_2),
% 0.22/0.60    inference(backward_demodulation,[],[f135,f145])).
% 0.22/0.60  fof(f145,plain,(
% 0.22/0.60    sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = sK4(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1) | spl5_2),
% 0.22/0.60    inference(forward_demodulation,[],[f144,f113])).
% 0.22/0.60  fof(f113,plain,(
% 0.22/0.60    sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)))) | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f110,f41])).
% 0.22/0.60  fof(f41,plain,(
% 0.22/0.60    ( ! [X0,X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f11])).
% 0.22/0.60  fof(f11,plain,(
% 0.22/0.60    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.60    inference(flattening,[],[f10])).
% 0.22/0.60  fof(f10,plain,(
% 0.22/0.60    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f2])).
% 0.22/0.60  fof(f2,axiom,(
% 0.22/0.60    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).
% 0.22/0.60  fof(f36,plain,(
% 0.22/0.60    v17_lattices(sK1)),
% 0.22/0.60    inference(cnf_transformation,[],[f24])).
% 0.22/0.60  fof(f24,plain,(
% 0.22/0.60    ((~r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1)) | ~r3_lattice3(sK1,sK2,sK0)) & (r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1)) | r3_lattice3(sK1,sK2,sK0)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l3_lattices(sK1) & v17_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1)),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).
% 0.22/0.60  fof(f22,plain,(
% 0.22/0.60    ? [X0,X1] : (? [X2] : ((~r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r3_lattice3(X1,X2,X0)) & (r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | r3_lattice3(X1,X2,X0)) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (? [X2] : ((~r4_lattice3(sK1,k7_lattices(sK1,X2),a_2_0_lattice3(sK0,sK1)) | ~r3_lattice3(sK1,X2,sK0)) & (r4_lattice3(sK1,k7_lattices(sK1,X2),a_2_0_lattice3(sK0,sK1)) | r3_lattice3(sK1,X2,sK0)) & m1_subset_1(X2,u1_struct_0(sK1))) & l3_lattices(sK1) & v17_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f23,plain,(
% 0.22/0.60    ? [X2] : ((~r4_lattice3(sK1,k7_lattices(sK1,X2),a_2_0_lattice3(sK0,sK1)) | ~r3_lattice3(sK1,X2,sK0)) & (r4_lattice3(sK1,k7_lattices(sK1,X2),a_2_0_lattice3(sK0,sK1)) | r3_lattice3(sK1,X2,sK0)) & m1_subset_1(X2,u1_struct_0(sK1))) => ((~r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1)) | ~r3_lattice3(sK1,sK2,sK0)) & (r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1)) | r3_lattice3(sK1,sK2,sK0)) & m1_subset_1(sK2,u1_struct_0(sK1)))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f21,plain,(
% 0.22/0.60    ? [X0,X1] : (? [X2] : ((~r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r3_lattice3(X1,X2,X0)) & (r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | r3_lattice3(X1,X2,X0)) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 0.22/0.60    inference(flattening,[],[f20])).
% 0.22/0.60  fof(f20,plain,(
% 0.22/0.60    ? [X0,X1] : (? [X2] : (((~r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r3_lattice3(X1,X2,X0)) & (r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | r3_lattice3(X1,X2,X0))) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 0.22/0.60    inference(nnf_transformation,[],[f9])).
% 0.22/0.60  fof(f9,plain,(
% 0.22/0.60    ? [X0,X1] : (? [X2] : ((r3_lattice3(X1,X2,X0) <~> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 0.22/0.60    inference(flattening,[],[f8])).
% 0.22/0.60  fof(f8,plain,(
% 0.22/0.60    ? [X0,X1] : (? [X2] : ((r3_lattice3(X1,X2,X0) <~> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))) & m1_subset_1(X2,u1_struct_0(X1))) & (l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)))),
% 0.22/0.60    inference(ennf_transformation,[],[f7])).
% 0.22/0.60  fof(f7,negated_conjecture,(
% 0.22/0.60    ~! [X0,X1] : ((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (r3_lattice3(X1,X2,X0) <=> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)))))),
% 0.22/0.60    inference(negated_conjecture,[],[f6])).
% 0.22/0.60  fof(f6,conjecture,(
% 0.22/0.60    ! [X0,X1] : ((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (r3_lattice3(X1,X2,X0) <=> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_lattice3)).
% 0.22/0.60  fof(f35,plain,(
% 0.22/0.60    v10_lattices(sK1)),
% 0.22/0.60    inference(cnf_transformation,[],[f24])).
% 0.22/0.60  fof(f144,plain,(
% 0.22/0.60    k7_lattices(sK1,k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)))) = sK4(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1) | spl5_2),
% 0.22/0.60    inference(forward_demodulation,[],[f138,f134])).
% 0.22/0.60  fof(f134,plain,(
% 0.22/0.60    k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))) = k7_lattices(sK1,sK4(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1)) | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f132,f50])).
% 0.22/0.60  fof(f50,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (k7_lattices(X2,sK4(X0,X1,X2)) = X0 | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f33])).
% 0.22/0.60  fof(f33,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ! [X3] : (~r2_hidden(X3,X1) | k7_lattices(X2,X3) != X0 | ~m1_subset_1(X3,u1_struct_0(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & k7_lattices(X2,sK4(X0,X1,X2)) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X2))) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)))) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2))),
% 0.22/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 0.22/0.60  fof(f32,plain,(
% 0.22/0.60    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & k7_lattices(X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & k7_lattices(X2,sK4(X0,X1,X2)) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X2))))),
% 0.22/0.60    introduced(choice_axiom,[])).
% 0.22/0.60  fof(f31,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ! [X3] : (~r2_hidden(X3,X1) | k7_lattices(X2,X3) != X0 | ~m1_subset_1(X3,u1_struct_0(X2)))) & (? [X4] : (r2_hidden(X4,X1) & k7_lattices(X2,X4) = X0 & m1_subset_1(X4,u1_struct_0(X2))) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)))) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2))),
% 0.22/0.60    inference(rectify,[],[f30])).
% 0.22/0.60  fof(f30,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ! [X3] : (~r2_hidden(X3,X1) | k7_lattices(X2,X3) != X0 | ~m1_subset_1(X3,u1_struct_0(X2)))) & (? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2))) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)))) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2))),
% 0.22/0.60    inference(nnf_transformation,[],[f19])).
% 0.22/0.60  fof(f19,plain,(
% 0.22/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_lattice3(X1,X2)) <=> ? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2)))) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2))),
% 0.22/0.60    inference(flattening,[],[f18])).
% 0.22/0.60  fof(f18,plain,(
% 0.22/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_lattice3(X1,X2)) <=> ? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2)))) | (~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)))),
% 0.22/0.60    inference(ennf_transformation,[],[f4])).
% 0.22/0.60  fof(f4,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : ((l3_lattices(X2) & v17_lattices(X2) & v10_lattices(X2) & ~v2_struct_0(X2)) => (r2_hidden(X0,a_2_0_lattice3(X1,X2)) <=> ? [X3] : (r2_hidden(X3,X1) & k7_lattices(X2,X3) = X0 & m1_subset_1(X3,u1_struct_0(X2)))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_lattice3)).
% 0.22/0.60  fof(f132,plain,(
% 0.22/0.60    r2_hidden(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),a_2_0_lattice3(sK0,sK1)) | spl5_2),
% 0.22/0.60    inference(backward_demodulation,[],[f123,f129])).
% 0.22/0.60  fof(f129,plain,(
% 0.22/0.60    k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))) = sK4(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1) | spl5_2),
% 0.22/0.60    inference(forward_demodulation,[],[f126,f122])).
% 0.22/0.60  fof(f122,plain,(
% 0.22/0.60    sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,sK4(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1)) | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f111,f50])).
% 0.22/0.60  fof(f111,plain,(
% 0.22/0.60    r2_hidden(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f37,f38,f109,f44])).
% 0.22/0.60  fof(f44,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | r2_hidden(sK3(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f28])).
% 0.22/0.60  fof(f109,plain,(
% 0.22/0.60    ~r3_lattice3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) | spl5_2),
% 0.22/0.60    inference(forward_demodulation,[],[f108,f64])).
% 0.22/0.60  fof(f64,plain,(
% 0.22/0.60    sK2 = k7_lattices(sK1,k7_lattices(sK1,sK2))),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f38,f41])).
% 0.22/0.60  fof(f108,plain,(
% 0.22/0.60    ~r3_lattice3(sK1,k7_lattices(sK1,k7_lattices(sK1,sK2)),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f65,f61,f47])).
% 0.22/0.60  fof(f47,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (r4_lattice3(X1,X2,X0) | ~r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v17_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f29])).
% 0.22/0.60  fof(f29,plain,(
% 0.22/0.60    ! [X0,X1] : (! [X2] : (((r4_lattice3(X1,X2,X0) | ~r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))) & (r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r4_lattice3(X1,X2,X0))) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l3_lattices(X1) | ~v17_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 0.22/0.60    inference(nnf_transformation,[],[f15])).
% 0.22/0.60  fof(f15,plain,(
% 0.22/0.60    ! [X0,X1] : (! [X2] : ((r4_lattice3(X1,X2,X0) <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l3_lattices(X1) | ~v17_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 0.22/0.60    inference(flattening,[],[f14])).
% 0.22/0.60  fof(f14,plain,(
% 0.22/0.60    ! [X0,X1] : (! [X2] : ((r4_lattice3(X1,X2,X0) <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l3_lattices(X1) | ~v17_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 0.22/0.60    inference(ennf_transformation,[],[f5])).
% 0.22/0.60  fof(f5,axiom,(
% 0.22/0.60    ! [X0,X1] : ((l3_lattices(X1) & v17_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (r4_lattice3(X1,X2,X0) <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattice3)).
% 0.22/0.60  fof(f61,plain,(
% 0.22/0.60    ~r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1)) | spl5_2),
% 0.22/0.60    inference(avatar_component_clause,[],[f59])).
% 0.22/0.60  fof(f59,plain,(
% 0.22/0.60    spl5_2 <=> r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.60  fof(f65,plain,(
% 0.22/0.60    m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1))),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f37,f38,f48])).
% 0.22/0.60  fof(f48,plain,(
% 0.22/0.60    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f17])).
% 0.22/0.60  fof(f17,plain,(
% 0.22/0.60    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.60    inference(flattening,[],[f16])).
% 0.22/0.60  fof(f16,plain,(
% 0.22/0.60    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f1])).
% 0.22/0.60  fof(f1,axiom,(
% 0.22/0.60    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).
% 0.22/0.60  fof(f126,plain,(
% 0.22/0.60    sK4(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1) = k7_lattices(sK1,k7_lattices(sK1,sK4(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1))) | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f121,f41])).
% 0.22/0.60  fof(f121,plain,(
% 0.22/0.60    m1_subset_1(sK4(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),u1_struct_0(sK1)) | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f111,f49])).
% 0.22/0.60  fof(f49,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X2)) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f33])).
% 0.22/0.60  fof(f123,plain,(
% 0.22/0.60    r2_hidden(sK4(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),a_2_0_lattice3(sK0,sK1)) | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f111,f51])).
% 0.22/0.60  fof(f51,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f33])).
% 0.22/0.60  fof(f138,plain,(
% 0.22/0.60    sK4(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1) = k7_lattices(sK1,k7_lattices(sK1,sK4(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1))) | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f133,f41])).
% 0.22/0.60  fof(f133,plain,(
% 0.22/0.60    m1_subset_1(sK4(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),u1_struct_0(sK1)) | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f132,f49])).
% 0.22/0.60  fof(f135,plain,(
% 0.22/0.60    r2_hidden(sK4(k7_lattices(sK1,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),sK0) | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f132,f51])).
% 0.22/0.60  fof(f110,plain,(
% 0.22/0.60    m1_subset_1(sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),u1_struct_0(sK1)) | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f37,f38,f109,f43])).
% 0.22/0.60  fof(f43,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f28])).
% 0.22/0.60  fof(f112,plain,(
% 0.22/0.60    ~r1_lattices(sK1,sK2,sK3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))) | spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f37,f38,f109,f45])).
% 0.22/0.60  fof(f45,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | ~r1_lattices(X0,X1,sK3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f28])).
% 0.22/0.60  fof(f56,plain,(
% 0.22/0.60    r3_lattice3(sK1,sK2,sK0) | ~spl5_1),
% 0.22/0.60    inference(avatar_component_clause,[],[f55])).
% 0.22/0.60  fof(f55,plain,(
% 0.22/0.60    spl5_1 <=> r3_lattice3(sK1,sK2,sK0)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.60  fof(f38,plain,(
% 0.22/0.60    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.22/0.60    inference(cnf_transformation,[],[f24])).
% 0.22/0.60  fof(f37,plain,(
% 0.22/0.60    l3_lattices(sK1)),
% 0.22/0.60    inference(cnf_transformation,[],[f24])).
% 0.22/0.60  fof(f34,plain,(
% 0.22/0.60    ~v2_struct_0(sK1)),
% 0.22/0.60    inference(cnf_transformation,[],[f24])).
% 0.22/0.60  fof(f107,plain,(
% 0.22/0.60    spl5_1 | ~spl5_2),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f105])).
% 0.22/0.60  fof(f105,plain,(
% 0.22/0.60    $false | (spl5_1 | ~spl5_2)),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f37,f38,f68,f84,f66,f93,f42])).
% 0.22/0.60  fof(f93,plain,(
% 0.22/0.60    r2_hidden(sK3(sK1,sK2,sK0),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) | spl5_1),
% 0.22/0.60    inference(forward_demodulation,[],[f92,f79])).
% 0.22/0.60  fof(f79,plain,(
% 0.22/0.60    sK3(sK1,sK2,sK0) = k7_lattices(sK1,k7_lattices(sK1,sK3(sK1,sK2,sK0))) | spl5_1),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f66,f41])).
% 0.22/0.60  fof(f92,plain,(
% 0.22/0.60    r2_hidden(k7_lattices(sK1,k7_lattices(sK1,sK3(sK1,sK2,sK0))),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) | spl5_1),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f80,f81,f53])).
% 0.22/0.60  fof(f53,plain,(
% 0.22/0.60    ( ! [X2,X3,X1] : (r2_hidden(k7_lattices(X2,X3),a_2_0_lattice3(X1,X2)) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 0.22/0.60    inference(equality_resolution,[],[f52])).
% 0.22/0.60  fof(f52,plain,(
% 0.22/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_lattice3(X1,X2)) | ~r2_hidden(X3,X1) | k7_lattices(X2,X3) != X0 | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v17_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f33])).
% 0.22/0.60  fof(f81,plain,(
% 0.22/0.60    r2_hidden(k7_lattices(sK1,sK3(sK1,sK2,sK0)),a_2_0_lattice3(sK0,sK1)) | spl5_1),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f67,f66,f53])).
% 0.22/0.60  fof(f67,plain,(
% 0.22/0.60    r2_hidden(sK3(sK1,sK2,sK0),sK0) | spl5_1),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f37,f38,f57,f44])).
% 0.22/0.60  fof(f57,plain,(
% 0.22/0.60    ~r3_lattice3(sK1,sK2,sK0) | spl5_1),
% 0.22/0.60    inference(avatar_component_clause,[],[f55])).
% 0.22/0.60  fof(f80,plain,(
% 0.22/0.60    m1_subset_1(k7_lattices(sK1,sK3(sK1,sK2,sK0)),u1_struct_0(sK1)) | spl5_1),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f37,f66,f48])).
% 0.22/0.60  fof(f66,plain,(
% 0.22/0.60    m1_subset_1(sK3(sK1,sK2,sK0),u1_struct_0(sK1)) | spl5_1),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f37,f38,f57,f43])).
% 0.22/0.60  fof(f84,plain,(
% 0.22/0.60    r3_lattice3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) | ~spl5_2),
% 0.22/0.60    inference(forward_demodulation,[],[f83,f64])).
% 0.22/0.60  fof(f83,plain,(
% 0.22/0.60    r3_lattice3(sK1,k7_lattices(sK1,k7_lattices(sK1,sK2)),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) | ~spl5_2),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f35,f36,f37,f65,f60,f46])).
% 0.22/0.60  fof(f46,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) | ~r4_lattice3(X1,X2,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v17_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f29])).
% 0.22/0.60  fof(f60,plain,(
% 0.22/0.60    r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1)) | ~spl5_2),
% 0.22/0.60    inference(avatar_component_clause,[],[f59])).
% 0.22/0.60  fof(f68,plain,(
% 0.22/0.60    ~r1_lattices(sK1,sK2,sK3(sK1,sK2,sK0)) | spl5_1),
% 0.22/0.60    inference(unit_resulting_resolution,[],[f34,f37,f38,f57,f45])).
% 0.22/0.60  fof(f63,plain,(
% 0.22/0.60    spl5_1 | spl5_2),
% 0.22/0.60    inference(avatar_split_clause,[],[f39,f59,f55])).
% 0.22/0.60  fof(f39,plain,(
% 0.22/0.60    r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1)) | r3_lattice3(sK1,sK2,sK0)),
% 0.22/0.60    inference(cnf_transformation,[],[f24])).
% 0.22/0.60  fof(f62,plain,(
% 0.22/0.60    ~spl5_1 | ~spl5_2),
% 0.22/0.60    inference(avatar_split_clause,[],[f40,f59,f55])).
% 0.22/0.60  fof(f40,plain,(
% 0.22/0.60    ~r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1)) | ~r3_lattice3(sK1,sK2,sK0)),
% 0.22/0.60    inference(cnf_transformation,[],[f24])).
% 0.22/0.60  % SZS output end Proof for theBenchmark
% 0.22/0.60  % (13726)------------------------------
% 0.22/0.60  % (13726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (13726)Termination reason: Refutation
% 0.22/0.60  
% 0.22/0.60  % (13726)Memory used [KB]: 10746
% 0.22/0.60  % (13726)Time elapsed: 0.152 s
% 0.22/0.60  % (13726)------------------------------
% 0.22/0.60  % (13726)------------------------------
% 0.22/0.60  % (13714)Success in time 0.241 s
%------------------------------------------------------------------------------
