%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 790 expanded)
%              Number of leaves         :   23 ( 264 expanded)
%              Depth                    :   46
%              Number of atoms          : 1047 (5181 expanded)
%              Number of equality atoms :   86 ( 643 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f529,plain,(
    $false ),
    inference(subsumption_resolution,[],[f528,f71])).

fof(f71,plain,(
    m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( sK10 != k16_lattice3(sK9,sK11)
    & r3_lattice3(sK9,sK10,sK11)
    & r2_hidden(sK10,sK11)
    & m1_subset_1(sK10,u1_struct_0(sK9))
    & l3_lattices(sK9)
    & v4_lattice3(sK9)
    & v10_lattices(sK9)
    & ~ v2_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f11,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k16_lattice3(X0,X2) != X1
                & r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(sK9,X2) != X1
              & r3_lattice3(sK9,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK9)) )
      & l3_lattices(sK9)
      & v4_lattice3(sK9)
      & v10_lattices(sK9)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k16_lattice3(sK9,X2) != X1
            & r3_lattice3(sK9,X1,X2)
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK9)) )
   => ( ? [X2] :
          ( k16_lattice3(sK9,X2) != sK10
          & r3_lattice3(sK9,sK10,X2)
          & r2_hidden(sK10,X2) )
      & m1_subset_1(sK10,u1_struct_0(sK9)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( k16_lattice3(sK9,X2) != sK10
        & r3_lattice3(sK9,sK10,X2)
        & r2_hidden(sK10,X2) )
   => ( sK10 != k16_lattice3(sK9,sK11)
      & r3_lattice3(sK9,sK10,sK11)
      & r2_hidden(sK10,sK11) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( r3_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k16_lattice3(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

fof(f528,plain,(
    ~ m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(subsumption_resolution,[],[f522,f72])).

fof(f72,plain,(
    r2_hidden(sK10,sK11) ),
    inference(cnf_transformation,[],[f42])).

fof(f522,plain,
    ( ~ r2_hidden(sK10,sK11)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(resolution,[],[f511,f73])).

fof(f73,plain,(
    r3_lattice3(sK9,sK10,sK11) ),
    inference(cnf_transformation,[],[f42])).

fof(f511,plain,(
    ! [X0] :
      ( ~ r3_lattice3(sK9,X0,sK11)
      | ~ r2_hidden(X0,sK11)
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(resolution,[],[f507,f111])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( sP7(X0,X1,X3)
      | ~ r3_lattice3(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X0,X1,X2)
      | ~ r3_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r3_lattice3(X1,sK15(X0,X1,X2),X0)
          & sK15(X0,X1,X2) = X2
          & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f64,f65])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK15(X0,X1,X2),X0)
        & sK15(X0,X1,X2) = X2
        & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r3_lattice3(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ( sP7(X2,X1,X0)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP7(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( sP7(X2,X1,X0)
    <=> ? [X3] :
          ( r3_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f507,plain,(
    ! [X0] :
      ( ~ sP7(sK11,sK9,X0)
      | ~ r2_hidden(X0,sK11) ) ),
    inference(subsumption_resolution,[],[f506,f67])).

fof(f67,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f42])).

fof(f506,plain,(
    ! [X0] :
      ( ~ sP7(sK11,sK9,X0)
      | ~ r2_hidden(X0,sK11)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f505,f68])).

fof(f68,plain,(
    v10_lattices(sK9) ),
    inference(cnf_transformation,[],[f42])).

fof(f505,plain,(
    ! [X0] :
      ( ~ sP7(sK11,sK9,X0)
      | ~ r2_hidden(X0,sK11)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f504,f69])).

fof(f69,plain,(
    v4_lattice3(sK9) ),
    inference(cnf_transformation,[],[f42])).

fof(f504,plain,(
    ! [X0] :
      ( ~ sP7(sK11,sK9,X0)
      | ~ r2_hidden(X0,sK11)
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f503,f70])).

fof(f70,plain,(
    l3_lattices(sK9) ),
    inference(cnf_transformation,[],[f42])).

fof(f503,plain,(
    ! [X0] :
      ( ~ sP7(sK11,sK9,X0)
      | ~ r2_hidden(X0,sK11)
      | ~ l3_lattices(sK9)
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(resolution,[],[f500,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( sP8(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( sP8(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f25,f37,f36])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
      <=> sP7(X2,X1,X0) )
      | ~ sP8(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_9_lattice3)).

fof(f500,plain,(
    ! [X0] :
      ( ~ sP8(X0,sK9,sK11)
      | ~ sP7(sK11,sK9,X0)
      | ~ r2_hidden(X0,sK11) ) ),
    inference(subsumption_resolution,[],[f499,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X0,X1,X2)
      | m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X1))
      | ~ sP7(X0,X1,X2)
      | ~ sP7(X0,X1,X2) ) ),
    inference(superposition,[],[f105,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( sK15(X0,X1,X2) = X2
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f499,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ r2_hidden(X0,sK11)
      | ~ sP7(sK11,sK9,X0)
      | ~ sP8(X0,sK9,sK11) ) ),
    inference(subsumption_resolution,[],[f496,f422])).

fof(f422,plain,(
    ! [X0] :
      ( ~ sP7(sK11,sK9,X0)
      | sK10 = X0
      | ~ r2_hidden(X0,sK11) ) ),
    inference(duplicate_literal_removal,[],[f421])).

fof(f421,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK11)
      | sK10 = X0
      | ~ sP7(sK11,sK9,X0)
      | ~ sP7(sK11,sK9,X0) ) ),
    inference(superposition,[],[f413,f106])).

fof(f413,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK15(sK11,sK9,X5),sK11)
      | sK10 = sK15(sK11,sK9,X5)
      | ~ sP7(sK11,sK9,X5) ) ),
    inference(subsumption_resolution,[],[f389,f105])).

fof(f389,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK15(sK11,sK9,X5),sK11)
      | sK10 = sK15(sK11,sK9,X5)
      | ~ m1_subset_1(sK15(sK11,sK9,X5),u1_struct_0(sK9))
      | ~ sP7(sK11,sK9,X5) ) ),
    inference(resolution,[],[f378,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK15(X0,X1,X2),X0)
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f378,plain,(
    ! [X0] :
      ( ~ r3_lattice3(sK9,X0,sK11)
      | ~ r2_hidden(X0,sK11)
      | sK10 = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(subsumption_resolution,[],[f377,f71])).

fof(f377,plain,(
    ! [X0] :
      ( sK10 = X0
      | ~ r2_hidden(X0,sK11)
      | ~ m1_subset_1(sK10,u1_struct_0(sK9))
      | ~ r3_lattice3(sK9,X0,sK11)
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(subsumption_resolution,[],[f376,f68])).

fof(f376,plain,(
    ! [X0] :
      ( sK10 = X0
      | ~ r2_hidden(X0,sK11)
      | ~ v10_lattices(sK9)
      | ~ m1_subset_1(sK10,u1_struct_0(sK9))
      | ~ r3_lattice3(sK9,X0,sK11)
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(subsumption_resolution,[],[f375,f69])).

fof(f375,plain,(
    ! [X0] :
      ( sK10 = X0
      | ~ r2_hidden(X0,sK11)
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | ~ m1_subset_1(sK10,u1_struct_0(sK9))
      | ~ r3_lattice3(sK9,X0,sK11)
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(subsumption_resolution,[],[f374,f70])).

fof(f374,plain,(
    ! [X0] :
      ( sK10 = X0
      | ~ r2_hidden(X0,sK11)
      | ~ l3_lattices(sK9)
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | ~ m1_subset_1(sK10,u1_struct_0(sK9))
      | ~ r3_lattice3(sK9,X0,sK11)
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(subsumption_resolution,[],[f373,f72])).

fof(f373,plain,(
    ! [X0] :
      ( sK10 = X0
      | ~ r2_hidden(X0,sK11)
      | ~ r2_hidden(sK10,sK11)
      | ~ l3_lattices(sK9)
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | ~ m1_subset_1(sK10,u1_struct_0(sK9))
      | ~ r3_lattice3(sK9,X0,sK11)
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(subsumption_resolution,[],[f365,f67])).

fof(f365,plain,(
    ! [X0] :
      ( v2_struct_0(sK9)
      | sK10 = X0
      | ~ r2_hidden(X0,sK11)
      | ~ r2_hidden(sK10,sK11)
      | ~ l3_lattices(sK9)
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | ~ m1_subset_1(sK10,u1_struct_0(sK9))
      | ~ r3_lattice3(sK9,X0,sK11)
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(resolution,[],[f360,f73])).

fof(f360,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattice3(X0,X2,X3)
      | v2_struct_0(X0)
      | X1 = X2
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X2,X3)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f355,f111])).

fof(f355,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X0,X1)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | X1 = X2
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X2,X3)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ r3_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f350,f111])).

fof(f350,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X0,X2)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | X1 = X2
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X2,X3)
      | ~ l3_lattices(X0)
      | ~ sP7(X3,X0,X1) ) ),
    inference(subsumption_resolution,[],[f349,f109])).

fof(f349,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | X1 = X2
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X2,X3)
      | ~ sP7(X3,X0,X2)
      | ~ sP7(X3,X0,X1)
      | ~ sP8(X1,X0,X3) ) ),
    inference(subsumption_resolution,[],[f348,f135])).

fof(f348,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | X1 = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X2,X3)
      | ~ sP7(X3,X0,X2)
      | ~ sP7(X3,X0,X1)
      | ~ sP8(X1,X0,X3) ) ),
    inference(subsumption_resolution,[],[f345,f135])).

fof(f345,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | X1 = X2
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X2,X3)
      | ~ sP7(X3,X0,X2)
      | ~ sP7(X3,X0,X1)
      | ~ sP8(X1,X0,X3) ) ),
    inference(resolution,[],[f342,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
      | ~ sP7(X2,X1,X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
          | ~ sP7(X2,X1,X0) )
        & ( sP7(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_9_lattice3(X1,X2)) ) )
      | ~ sP8(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f342,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X3))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | X0 = X2
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r2_hidden(X0,X3)
      | ~ r2_hidden(X2,X3)
      | ~ sP7(X3,X1,X2) ) ),
    inference(subsumption_resolution,[],[f339,f109])).

fof(f339,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | X0 = X2
      | ~ r2_hidden(X0,a_2_9_lattice3(X1,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r2_hidden(X0,X3)
      | ~ r2_hidden(X2,X3)
      | ~ sP7(X3,X1,X2)
      | ~ sP8(X2,X1,X3) ) ),
    inference(resolution,[],[f338,f104])).

fof(f338,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,a_2_9_lattice3(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | X0 = X3
      | ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f337])).

fof(f337,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | X0 = X3
      | ~ r2_hidden(X3,a_2_9_lattice3(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X3,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f297,f267])).

fof(f267,plain,(
    ! [X6,X4,X5] :
      ( r4_lattice3(X5,X4,a_2_9_lattice3(X5,X6))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | ~ v4_lattice3(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | ~ m1_subset_1(X4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f266,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP4(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP4(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f19,f31,f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP3(X1,X0,X2) )
      | ~ sP4(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

fof(f266,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | ~ v4_lattice3(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | r4_lattice3(X5,X4,a_2_9_lattice3(X5,X6))
      | ~ sP4(X5,X4) ) ),
    inference(resolution,[],[f264,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP3(X1,X0,X2) )
          & ( sP3(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP4(X0,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f264,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X2,a_2_9_lattice3(X2,X1))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f263,f127])).

fof(f127,plain,(
    ! [X6,X7,X5] :
      ( sP6(X5,sK13(X6,X5,X7))
      | ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | sP3(X6,X5,X7) ) ),
    inference(resolution,[],[f101,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK13(X0,X1,X2),X0)
          & r2_hidden(sK13(X0,X1,X2),X2)
          & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK13(X0,X1,X2),X0)
        & r2_hidden(sK13(X0,X1,X2),X2)
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X3,X1)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X3,X1)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP6(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP6(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f21,f34,f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( sP5(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP5(X1,X0,X2) )
      | ~ sP6(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f263,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ sP6(X2,sK13(X0,X2,a_2_9_lattice3(X2,X1)))
      | sP3(X0,X2,a_2_9_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f262])).

fof(f262,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ sP6(X2,sK13(X0,X2,a_2_9_lattice3(X2,X1)))
      | sP3(X0,X2,a_2_9_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | sP3(X0,X2,a_2_9_lattice3(X2,X1)) ) ),
    inference(resolution,[],[f189,f233])).

fof(f233,plain,(
    ! [X14,X12,X15,X13] :
      ( r3_lattice3(X14,sK13(X12,X13,a_2_9_lattice3(X14,X15)),X15)
      | ~ l3_lattices(X14)
      | ~ v4_lattice3(X14)
      | ~ v10_lattices(X14)
      | v2_struct_0(X14)
      | sP3(X12,X13,a_2_9_lattice3(X14,X15)) ) ),
    inference(resolution,[],[f229,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X0,X1,X2)
      | r3_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,X2,X0)
      | ~ sP7(X0,X1,X2)
      | ~ sP7(X0,X1,X2) ) ),
    inference(superposition,[],[f107,f106])).

fof(f229,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X0,X1,sK13(X2,X3,a_2_9_lattice3(X1,X0)))
      | sP3(X2,X3,a_2_9_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f157,f109])).

fof(f157,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP8(sK13(X2,X3,a_2_9_lattice3(X1,X0)),X1,X0)
      | sP7(X0,X1,sK13(X2,X3,a_2_9_lattice3(X1,X0)))
      | sP3(X2,X3,a_2_9_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f103,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK13(X0,X1,X2),X2)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
      | sP7(X2,X1,X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f189,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattice3(X1,sK13(X0,X1,X3),X2)
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ sP6(X1,sK13(X0,X1,X3))
      | sP3(X0,X1,X3) ) ),
    inference(resolution,[],[f179,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK13(X0,X1,X2),X0)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f179,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X2,X3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ r3_lattice3(X2,X3,X1)
      | ~ sP6(X2,X3) ) ),
    inference(resolution,[],[f97,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( sP5(X1,X0,X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ sP6(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP5(X1,X0,X2) )
          & ( sP5(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP6(X0,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK14(X0,X1,X2))
          & r2_hidden(sK14(X0,X1,X2),X2)
          & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f59,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK14(X0,X1,X2))
        & r2_hidden(sK14(X0,X1,X2),X2)
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X1,X0,X2] :
      ( ( sP5(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X1,X3)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP5(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f297,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_lattice3(X2,X0,a_2_9_lattice3(X2,X3))
      | ~ r2_hidden(X1,a_2_9_lattice3(X2,X3))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | X0 = X1
      | ~ r2_hidden(X0,a_2_9_lattice3(X2,X3))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X1,X3) ) ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X1
      | ~ r2_hidden(X1,a_2_9_lattice3(X2,X3))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ r4_lattice3(X2,X0,a_2_9_lattice3(X2,X3))
      | ~ r2_hidden(X0,a_2_9_lattice3(X2,X3))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X1,X3)
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f223,f267])).

fof(f223,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_lattice3(X0,X3,X1)
      | X2 = X3
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ r4_lattice3(X0,X2,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r4_lattice3(X0,X3,X1)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ r4_lattice3(X0,X2,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f77,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X2) = X1
      | ~ r4_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k15_lattice3(X0,X2) = X1
              | ~ r4_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k15_lattice3(X0,X2) = X1
              | ~ r4_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
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
              ( ( r4_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k15_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattice3)).

fof(f496,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ r2_hidden(X0,sK11)
      | ~ sP7(sK11,sK9,X0)
      | ~ sP8(X0,sK9,sK11) ) ),
    inference(resolution,[],[f495,f104])).

fof(f495,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_9_lattice3(sK9,sK11))
      | sK10 != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ r2_hidden(X0,sK11) ) ),
    inference(subsumption_resolution,[],[f494,f67])).

fof(f494,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r2_hidden(X0,a_2_9_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ r2_hidden(X0,sK11)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f493,f68])).

fof(f493,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r2_hidden(X0,a_2_9_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ r2_hidden(X0,sK11)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f492,f69])).

fof(f492,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r2_hidden(X0,a_2_9_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ r2_hidden(X0,sK11)
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f491,f70])).

fof(f491,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r2_hidden(X0,a_2_9_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ r2_hidden(X0,sK11)
      | ~ l3_lattices(sK9)
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(duplicate_literal_removal,[],[f490])).

fof(f490,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r2_hidden(X0,a_2_9_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ r2_hidden(X0,sK11)
      | ~ l3_lattices(sK9)
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9)
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(resolution,[],[f484,f267])).

fof(f484,plain,(
    ! [X0] :
      ( ~ r4_lattice3(sK9,X0,a_2_9_lattice3(sK9,sK11))
      | sK10 != X0
      | ~ r2_hidden(X0,a_2_9_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(subsumption_resolution,[],[f483,f67])).

fof(f483,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r4_lattice3(sK9,X0,a_2_9_lattice3(sK9,sK11))
      | ~ r2_hidden(X0,a_2_9_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f482,f68])).

fof(f482,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r4_lattice3(sK9,X0,a_2_9_lattice3(sK9,sK11))
      | ~ r2_hidden(X0,a_2_9_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f481,f69])).

fof(f481,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r4_lattice3(sK9,X0,a_2_9_lattice3(sK9,sK11))
      | ~ r2_hidden(X0,a_2_9_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f480,f70])).

fof(f480,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r4_lattice3(sK9,X0,a_2_9_lattice3(sK9,sK11))
      | ~ r2_hidden(X0,a_2_9_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ l3_lattices(sK9)
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(superposition,[],[f477,f77])).

fof(f477,plain,(
    sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)) ),
    inference(subsumption_resolution,[],[f476,f171])).

fof(f171,plain,(
    sP2(sK10,sK9) ),
    inference(subsumption_resolution,[],[f170,f67])).

fof(f170,plain,
    ( sP2(sK10,sK9)
    | v2_struct_0(sK9) ),
    inference(subsumption_resolution,[],[f169,f68])).

fof(f169,plain,
    ( sP2(sK10,sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(subsumption_resolution,[],[f168,f69])).

fof(f168,plain,
    ( sP2(sK10,sK9)
    | ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(subsumption_resolution,[],[f162,f70])).

fof(f162,plain,
    ( sP2(sK10,sK9)
    | ~ l3_lattices(sK9)
    | ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(resolution,[],[f87,f71])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP2(X1,X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f28,f27,f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r3_lattices(X0,X3,X1)
          | ~ r3_lattice3(X0,X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
    <=> ( sP0(X1,X0,X2)
        & r3_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( k16_lattice3(X0,X2) = X1
        <=> sP1(X2,X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(f476,plain,
    ( sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11))
    | ~ sP2(sK10,sK9) ),
    inference(subsumption_resolution,[],[f475,f73])).

fof(f475,plain,
    ( ~ r3_lattice3(sK9,sK10,sK11)
    | sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11))
    | ~ sP2(sK10,sK9) ),
    inference(inner_rewriting,[],[f474])).

fof(f474,plain,
    ( ~ r3_lattice3(sK9,k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK11)
    | sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11))
    | ~ sP2(k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK9) ),
    inference(subsumption_resolution,[],[f473,f68])).

fof(f473,plain,
    ( ~ v10_lattices(sK9)
    | ~ r3_lattice3(sK9,k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK11)
    | sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11))
    | ~ sP2(k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK9) ),
    inference(subsumption_resolution,[],[f472,f70])).

fof(f472,plain,
    ( ~ l3_lattices(sK9)
    | ~ v10_lattices(sK9)
    | ~ r3_lattice3(sK9,k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK11)
    | sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11))
    | ~ sP2(k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK9) ),
    inference(subsumption_resolution,[],[f471,f69])).

fof(f471,plain,
    ( ~ v4_lattice3(sK9)
    | ~ l3_lattices(sK9)
    | ~ v10_lattices(sK9)
    | ~ r3_lattice3(sK9,k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK11)
    | sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11))
    | ~ sP2(k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK9) ),
    inference(subsumption_resolution,[],[f451,f67])).

fof(f451,plain,
    ( v2_struct_0(sK9)
    | ~ v4_lattice3(sK9)
    | ~ l3_lattices(sK9)
    | ~ v10_lattices(sK9)
    | ~ r3_lattice3(sK9,k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK11)
    | sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11))
    | ~ sP2(k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK9) ),
    inference(resolution,[],[f449,f152])).

fof(f152,plain,(
    ! [X6] :
      ( ~ sP0(X6,sK9,sK11)
      | ~ r3_lattice3(sK9,X6,sK11)
      | sK10 != X6
      | ~ sP2(X6,sK9) ) ),
    inference(resolution,[],[f82,f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ sP1(sK11,sK9,X0)
      | sK10 != X0
      | ~ sP2(X0,sK9) ) ),
    inference(superposition,[],[f74,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X1,X2) = X0
      | ~ sP1(X2,X1,X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k16_lattice3(X1,X2) = X0
            | ~ sP1(X2,X1,X0) )
          & ( sP1(X2,X1,X0)
            | k16_lattice3(X1,X2) != X0 ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( ( k16_lattice3(X0,X2) = X1
            | ~ sP1(X2,X0,X1) )
          & ( sP1(X2,X0,X1)
            | k16_lattice3(X0,X2) != X1 ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f74,plain,(
    sK10 != k16_lattice3(sK9,sK11) ),
    inference(cnf_transformation,[],[f42])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | ~ r3_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ~ sP0(X2,X1,X0)
        | ~ r3_lattice3(X1,X2,X0) )
      & ( ( sP0(X2,X1,X0)
          & r3_lattice3(X1,X2,X0) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ~ sP0(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP0(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ~ sP0(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP0(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f449,plain,(
    ! [X0,X1] :
      ( sP0(k15_lattice3(X0,a_2_9_lattice3(X0,X1)),X0,X1)
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f448,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r3_lattices(X1,sK12(X0,X1,X2),X0)
          & r3_lattice3(X1,sK12(X0,X1,X2),X2)
          & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r3_lattices(X1,X4,X0)
            | ~ r3_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X1,X3,X0)
          & r3_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r3_lattices(X1,sK12(X0,X1,X2),X0)
        & r3_lattice3(X1,sK12(X0,X1,X2),X2)
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r3_lattices(X1,X3,X0)
            & r3_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r3_lattices(X1,X4,X0)
            | ~ r3_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ~ r3_lattices(X0,X3,X1)
            & r3_lattice3(X0,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r3_lattices(X0,X3,X1)
            | ~ r3_lattice3(X0,X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f448,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_9_lattice3(X0,X1)),X0,X1)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | ~ m1_subset_1(sK12(k15_lattice3(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f445])).

fof(f445,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_9_lattice3(X0,X1)),X0,X1)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ m1_subset_1(sK12(k15_lattice3(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0))
      | sP0(k15_lattice3(X0,a_2_9_lattice3(X0,X1)),X0,X1) ) ),
    inference(resolution,[],[f327,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK12(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f327,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattice3(X1,sK12(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3),X2)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X0)
      | ~ m1_subset_1(sK12(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f319,f111])).

fof(f319,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X2,X1,sK12(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f226,f109])).

fof(f226,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP8(sK12(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3),X1,X2)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3)
      | ~ sP7(X2,X1,sK12(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3))
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f185,f104])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK12(k15_lattice3(X0,X1),X0,X2),X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,X1),X0,X2) ) ),
    inference(subsumption_resolution,[],[f184,f84])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK12(k15_lattice3(X0,X1),X0,X2),X1)
      | ~ m1_subset_1(sK12(k15_lattice3(X0,X1),X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,X1),X0,X2) ) ),
    inference(resolution,[],[f75,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X1,sK12(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (16731)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (16723)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (16720)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (16719)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (16719)Refutation not found, incomplete strategy% (16719)------------------------------
% 0.20/0.50  % (16719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16719)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16719)Memory used [KB]: 10490
% 0.20/0.50  % (16719)Time elapsed: 0.085 s
% 0.20/0.50  % (16719)------------------------------
% 0.20/0.50  % (16719)------------------------------
% 0.20/0.50  % (16730)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (16730)Refutation not found, incomplete strategy% (16730)------------------------------
% 0.20/0.50  % (16730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16730)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16730)Memory used [KB]: 10490
% 0.20/0.50  % (16730)Time elapsed: 0.099 s
% 0.20/0.50  % (16730)------------------------------
% 0.20/0.50  % (16730)------------------------------
% 0.20/0.51  % (16743)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (16737)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (16733)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (16736)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (16726)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (16725)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (16732)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (16721)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (16732)Refutation not found, incomplete strategy% (16732)------------------------------
% 0.20/0.51  % (16732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16732)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (16732)Memory used [KB]: 6140
% 0.20/0.51  % (16732)Time elapsed: 0.102 s
% 0.20/0.51  % (16732)------------------------------
% 0.20/0.51  % (16732)------------------------------
% 0.20/0.51  % (16726)Refutation not found, incomplete strategy% (16726)------------------------------
% 0.20/0.51  % (16726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16725)Refutation not found, incomplete strategy% (16725)------------------------------
% 0.20/0.51  % (16725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16725)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (16725)Memory used [KB]: 10618
% 0.20/0.51  % (16725)Time elapsed: 0.007 s
% 0.20/0.51  % (16724)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (16725)------------------------------
% 0.20/0.51  % (16725)------------------------------
% 0.20/0.51  % (16727)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (16740)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (16741)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (16735)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (16729)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (16726)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (16726)Memory used [KB]: 1663
% 0.20/0.52  % (16726)Time elapsed: 0.101 s
% 0.20/0.52  % (16726)------------------------------
% 0.20/0.52  % (16726)------------------------------
% 0.20/0.52  % (16742)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.53  % (16722)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.53  % (16744)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (16728)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (16723)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f529,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f528,f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    m1_subset_1(sK10,u1_struct_0(sK9))),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ((sK10 != k16_lattice3(sK9,sK11) & r3_lattice3(sK9,sK10,sK11) & r2_hidden(sK10,sK11)) & m1_subset_1(sK10,u1_struct_0(sK9))) & l3_lattices(sK9) & v4_lattice3(sK9) & v10_lattices(sK9) & ~v2_struct_0(sK9)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f11,f41,f40,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK9,X2) != X1 & r3_lattice3(sK9,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK9))) & l3_lattices(sK9) & v4_lattice3(sK9) & v10_lattices(sK9) & ~v2_struct_0(sK9))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ? [X1] : (? [X2] : (k16_lattice3(sK9,X2) != X1 & r3_lattice3(sK9,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK9))) => (? [X2] : (k16_lattice3(sK9,X2) != sK10 & r3_lattice3(sK9,sK10,X2) & r2_hidden(sK10,X2)) & m1_subset_1(sK10,u1_struct_0(sK9)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ? [X2] : (k16_lattice3(sK9,X2) != sK10 & r3_lattice3(sK9,sK10,X2) & r2_hidden(sK10,X2)) => (sK10 != k16_lattice3(sK9,sK11) & r3_lattice3(sK9,sK10,sK11) & r2_hidden(sK10,sK11))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.20/0.53    inference(negated_conjecture,[],[f8])).
% 0.20/0.53  fof(f8,conjecture,(
% 0.20/0.53    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).
% 0.20/0.53  fof(f528,plain,(
% 0.20/0.53    ~m1_subset_1(sK10,u1_struct_0(sK9))),
% 0.20/0.53    inference(subsumption_resolution,[],[f522,f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    r2_hidden(sK10,sK11)),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f522,plain,(
% 0.20/0.53    ~r2_hidden(sK10,sK11) | ~m1_subset_1(sK10,u1_struct_0(sK9))),
% 0.20/0.53    inference(resolution,[],[f511,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    r3_lattice3(sK9,sK10,sK11)),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f511,plain,(
% 0.20/0.53    ( ! [X0] : (~r3_lattice3(sK9,X0,sK11) | ~r2_hidden(X0,sK11) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 0.20/0.53    inference(resolution,[],[f507,f111])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (sP7(X0,X1,X3) | ~r3_lattice3(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f108])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (sP7(X0,X1,X2) | ~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK15(X0,X1,X2),X0) & sK15(X0,X1,X2) = X2 & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f64,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK15(X0,X1,X2),X0) & sK15(X0,X1,X2) = X2 & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 0.20/0.53    inference(rectify,[],[f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ! [X2,X1,X0] : ((sP7(X2,X1,X0) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP7(X2,X1,X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (sP7(X2,X1,X0) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 0.20/0.53  fof(f507,plain,(
% 0.20/0.53    ( ! [X0] : (~sP7(sK11,sK9,X0) | ~r2_hidden(X0,sK11)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f506,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ~v2_struct_0(sK9)),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f506,plain,(
% 0.20/0.53    ( ! [X0] : (~sP7(sK11,sK9,X0) | ~r2_hidden(X0,sK11) | v2_struct_0(sK9)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f505,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    v10_lattices(sK9)),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f505,plain,(
% 0.20/0.53    ( ! [X0] : (~sP7(sK11,sK9,X0) | ~r2_hidden(X0,sK11) | ~v10_lattices(sK9) | v2_struct_0(sK9)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f504,f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    v4_lattice3(sK9)),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f504,plain,(
% 0.20/0.53    ( ! [X0] : (~sP7(sK11,sK9,X0) | ~r2_hidden(X0,sK11) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f503,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    l3_lattices(sK9)),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f503,plain,(
% 0.20/0.53    ( ! [X0] : (~sP7(sK11,sK9,X0) | ~r2_hidden(X0,sK11) | ~l3_lattices(sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) )),
% 0.20/0.53    inference(resolution,[],[f500,f109])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP8(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (sP8(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 0.20/0.53    inference(definition_folding,[],[f25,f37,f36])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_9_lattice3(X1,X2)) <=> sP7(X2,X1,X0)) | ~sP8(X0,X1,X2))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_9_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 0.20/0.53    inference(flattening,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_9_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_9_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_9_lattice3)).
% 0.20/0.53  fof(f500,plain,(
% 0.20/0.53    ( ! [X0] : (~sP8(X0,sK9,sK11) | ~sP7(sK11,sK9,X0) | ~r2_hidden(X0,sK11)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f499,f135])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~sP7(X0,X1,X2) | m1_subset_1(X2,u1_struct_0(X1))) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f134])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X1)) | ~sP7(X0,X1,X2) | ~sP7(X0,X1,X2)) )),
% 0.20/0.53    inference(superposition,[],[f105,f106])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sK15(X0,X1,X2) = X2 | ~sP7(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f66])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) | ~sP7(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f66])).
% 0.20/0.53  fof(f499,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11) | ~sP7(sK11,sK9,X0) | ~sP8(X0,sK9,sK11)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f496,f422])).
% 0.20/0.53  fof(f422,plain,(
% 0.20/0.53    ( ! [X0] : (~sP7(sK11,sK9,X0) | sK10 = X0 | ~r2_hidden(X0,sK11)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f421])).
% 0.20/0.53  fof(f421,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,sK11) | sK10 = X0 | ~sP7(sK11,sK9,X0) | ~sP7(sK11,sK9,X0)) )),
% 0.20/0.53    inference(superposition,[],[f413,f106])).
% 0.20/0.53  fof(f413,plain,(
% 0.20/0.53    ( ! [X5] : (~r2_hidden(sK15(sK11,sK9,X5),sK11) | sK10 = sK15(sK11,sK9,X5) | ~sP7(sK11,sK9,X5)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f389,f105])).
% 0.20/0.53  fof(f389,plain,(
% 0.20/0.53    ( ! [X5] : (~r2_hidden(sK15(sK11,sK9,X5),sK11) | sK10 = sK15(sK11,sK9,X5) | ~m1_subset_1(sK15(sK11,sK9,X5),u1_struct_0(sK9)) | ~sP7(sK11,sK9,X5)) )),
% 0.20/0.53    inference(resolution,[],[f378,f107])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK15(X0,X1,X2),X0) | ~sP7(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f66])).
% 0.20/0.53  fof(f378,plain,(
% 0.20/0.53    ( ! [X0] : (~r3_lattice3(sK9,X0,sK11) | ~r2_hidden(X0,sK11) | sK10 = X0 | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f377,f71])).
% 0.20/0.53  fof(f377,plain,(
% 0.20/0.53    ( ! [X0] : (sK10 = X0 | ~r2_hidden(X0,sK11) | ~m1_subset_1(sK10,u1_struct_0(sK9)) | ~r3_lattice3(sK9,X0,sK11) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f376,f68])).
% 0.20/0.53  fof(f376,plain,(
% 0.20/0.53    ( ! [X0] : (sK10 = X0 | ~r2_hidden(X0,sK11) | ~v10_lattices(sK9) | ~m1_subset_1(sK10,u1_struct_0(sK9)) | ~r3_lattice3(sK9,X0,sK11) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f375,f69])).
% 0.20/0.53  fof(f375,plain,(
% 0.20/0.53    ( ! [X0] : (sK10 = X0 | ~r2_hidden(X0,sK11) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | ~m1_subset_1(sK10,u1_struct_0(sK9)) | ~r3_lattice3(sK9,X0,sK11) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f374,f70])).
% 0.20/0.53  fof(f374,plain,(
% 0.20/0.53    ( ! [X0] : (sK10 = X0 | ~r2_hidden(X0,sK11) | ~l3_lattices(sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | ~m1_subset_1(sK10,u1_struct_0(sK9)) | ~r3_lattice3(sK9,X0,sK11) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f373,f72])).
% 0.20/0.53  fof(f373,plain,(
% 0.20/0.53    ( ! [X0] : (sK10 = X0 | ~r2_hidden(X0,sK11) | ~r2_hidden(sK10,sK11) | ~l3_lattices(sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | ~m1_subset_1(sK10,u1_struct_0(sK9)) | ~r3_lattice3(sK9,X0,sK11) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f365,f67])).
% 0.20/0.53  fof(f365,plain,(
% 0.20/0.53    ( ! [X0] : (v2_struct_0(sK9) | sK10 = X0 | ~r2_hidden(X0,sK11) | ~r2_hidden(sK10,sK11) | ~l3_lattices(sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | ~m1_subset_1(sK10,u1_struct_0(sK9)) | ~r3_lattice3(sK9,X0,sK11) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 0.20/0.53    inference(resolution,[],[f360,f73])).
% 0.20/0.53  fof(f360,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X0,X2,X3) | v2_struct_0(X0) | X1 = X2 | ~r2_hidden(X1,X3) | ~r2_hidden(X2,X3) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X3) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 0.20/0.53    inference(resolution,[],[f355,f111])).
% 0.20/0.53  fof(f355,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~sP7(X3,X0,X1) | ~v10_lattices(X0) | v2_struct_0(X0) | X1 = X2 | ~r2_hidden(X1,X3) | ~r2_hidden(X2,X3) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~r3_lattice3(X0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.20/0.53    inference(resolution,[],[f350,f111])).
% 0.20/0.53  fof(f350,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~sP7(X3,X0,X2) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | X1 = X2 | ~r2_hidden(X1,X3) | ~r2_hidden(X2,X3) | ~l3_lattices(X0) | ~sP7(X3,X0,X1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f349,f109])).
% 0.20/0.53  fof(f349,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | X1 = X2 | ~r2_hidden(X1,X3) | ~r2_hidden(X2,X3) | ~sP7(X3,X0,X2) | ~sP7(X3,X0,X1) | ~sP8(X1,X0,X3)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f348,f135])).
% 0.20/0.53  fof(f348,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | X1 = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X1,X3) | ~r2_hidden(X2,X3) | ~sP7(X3,X0,X2) | ~sP7(X3,X0,X1) | ~sP8(X1,X0,X3)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f345,f135])).
% 0.20/0.53  fof(f345,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | X1 = X2 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X1,X3) | ~r2_hidden(X2,X3) | ~sP7(X3,X0,X2) | ~sP7(X3,X0,X1) | ~sP8(X1,X0,X3)) )),
% 0.20/0.53    inference(resolution,[],[f342,f104])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ~sP7(X2,X1,X0) | ~sP8(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ~sP7(X2,X1,X0)) & (sP7(X2,X1,X0) | ~r2_hidden(X0,a_2_9_lattice3(X1,X2)))) | ~sP8(X0,X1,X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f37])).
% 0.20/0.53  fof(f342,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,a_2_9_lattice3(X1,X3)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | X0 = X2 | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r2_hidden(X0,X3) | ~r2_hidden(X2,X3) | ~sP7(X3,X1,X2)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f339,f109])).
% 0.20/0.53  fof(f339,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | X0 = X2 | ~r2_hidden(X0,a_2_9_lattice3(X1,X3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r2_hidden(X0,X3) | ~r2_hidden(X2,X3) | ~sP7(X3,X1,X2) | ~sP8(X2,X1,X3)) )),
% 0.20/0.53    inference(resolution,[],[f338,f104])).
% 0.20/0.53  fof(f338,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,a_2_9_lattice3(X1,X2)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | X0 = X3 | ~r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | ~r2_hidden(X3,X2)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f337])).
% 0.20/0.53  fof(f337,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | X0 = X3 | ~r2_hidden(X3,a_2_9_lattice3(X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | ~r2_hidden(X3,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.20/0.53    inference(resolution,[],[f297,f267])).
% 0.20/0.53  fof(f267,plain,(
% 0.20/0.53    ( ! [X6,X4,X5] : (r4_lattice3(X5,X4,a_2_9_lattice3(X5,X6)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | ~v4_lattice3(X5) | ~v10_lattices(X5) | v2_struct_0(X5) | ~m1_subset_1(X4,u1_struct_0(X5))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f266,f94])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP4(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (sP4(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(definition_folding,[],[f19,f31,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> sP3(X1,X0,X2)) | ~sP4(X0,X1))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 0.20/0.53  fof(f266,plain,(
% 0.20/0.53    ( ! [X6,X4,X5] : (~m1_subset_1(X4,u1_struct_0(X5)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | ~v4_lattice3(X5) | ~v10_lattices(X5) | v2_struct_0(X5) | r4_lattice3(X5,X4,a_2_9_lattice3(X5,X6)) | ~sP4(X5,X4)) )),
% 0.20/0.53    inference(resolution,[],[f264,f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~sP3(X1,X0,X2) | r4_lattice3(X0,X1,X2) | ~sP4(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | ~r4_lattice3(X0,X1,X2))) | ~sP4(X0,X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f31])).
% 0.20/0.53  fof(f264,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP3(X0,X2,a_2_9_lattice3(X2,X1)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~l3_lattices(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f263,f127])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    ( ! [X6,X7,X5] : (sP6(X5,sK13(X6,X5,X7)) | ~l3_lattices(X5) | v2_struct_0(X5) | sP3(X6,X5,X7)) )),
% 0.20/0.53    inference(resolution,[],[f101,f91])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) | sP3(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (~r1_lattices(X1,sK13(X0,X1,X2),X0) & r2_hidden(sK13(X0,X1,X2),X2) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f54,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,sK13(X0,X1,X2),X0) & r2_hidden(sK13(X0,X1,X2),X2) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 0.20/0.53    inference(rectify,[],[f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP3(X1,X0,X2)))),
% 0.20/0.53    inference(nnf_transformation,[],[f30])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP6(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (sP6(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(definition_folding,[],[f21,f34,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X1,X0,X2] : (sP5(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP5(X1,X0,X2)) | ~sP6(X0,X1))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 0.20/0.53  fof(f263,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~sP6(X2,sK13(X0,X2,a_2_9_lattice3(X2,X1))) | sP3(X0,X2,a_2_9_lattice3(X2,X1)) | ~l3_lattices(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f262])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~sP6(X2,sK13(X0,X2,a_2_9_lattice3(X2,X1))) | sP3(X0,X2,a_2_9_lattice3(X2,X1)) | ~l3_lattices(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | sP3(X0,X2,a_2_9_lattice3(X2,X1))) )),
% 0.20/0.53    inference(resolution,[],[f189,f233])).
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    ( ! [X14,X12,X15,X13] : (r3_lattice3(X14,sK13(X12,X13,a_2_9_lattice3(X14,X15)),X15) | ~l3_lattices(X14) | ~v4_lattice3(X14) | ~v10_lattices(X14) | v2_struct_0(X14) | sP3(X12,X13,a_2_9_lattice3(X14,X15))) )),
% 0.20/0.53    inference(resolution,[],[f229,f137])).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~sP7(X0,X1,X2) | r3_lattice3(X1,X2,X0)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f136])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r3_lattice3(X1,X2,X0) | ~sP7(X0,X1,X2) | ~sP7(X0,X1,X2)) )),
% 0.20/0.53    inference(superposition,[],[f107,f106])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (sP7(X0,X1,sK13(X2,X3,a_2_9_lattice3(X1,X0))) | sP3(X2,X3,a_2_9_lattice3(X1,X0)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 0.20/0.53    inference(resolution,[],[f157,f109])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~sP8(sK13(X2,X3,a_2_9_lattice3(X1,X0)),X1,X0) | sP7(X0,X1,sK13(X2,X3,a_2_9_lattice3(X1,X0))) | sP3(X2,X3,a_2_9_lattice3(X1,X0))) )),
% 0.20/0.53    inference(resolution,[],[f103,f92])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK13(X0,X1,X2),X2) | sP3(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f56])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_9_lattice3(X1,X2)) | sP7(X2,X1,X0) | ~sP8(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f62])).
% 0.20/0.53  fof(f189,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X1,sK13(X0,X1,X3),X2) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~sP6(X1,sK13(X0,X1,X3)) | sP3(X0,X1,X3)) )),
% 0.20/0.53    inference(resolution,[],[f179,f93])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_lattices(X1,sK13(X0,X1,X2),X0) | sP3(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f56])).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (r1_lattices(X2,X3,X0) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~r3_lattice3(X2,X3,X1) | ~sP6(X2,X3)) )),
% 0.20/0.53    inference(resolution,[],[f97,f95])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP5(X1,X0,X2) | ~r3_lattice3(X0,X1,X2) | ~sP6(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP5(X1,X0,X2)) & (sP5(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP6(X0,X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f34])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (~sP5(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | (~r1_lattices(X1,X0,sK14(X0,X1,X2)) & r2_hidden(sK14(X0,X1,X2),X2) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP5(X0,X1,X2)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f59,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK14(X0,X1,X2)) & r2_hidden(sK14(X0,X1,X2),X2) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP5(X0,X1,X2)))),
% 0.20/0.53    inference(rectify,[],[f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP5(X1,X0,X2)))),
% 0.20/0.53    inference(nnf_transformation,[],[f33])).
% 0.20/0.53  fof(f297,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r4_lattice3(X2,X0,a_2_9_lattice3(X2,X3)) | ~r2_hidden(X1,a_2_9_lattice3(X2,X3)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | X0 = X1 | ~r2_hidden(X0,a_2_9_lattice3(X2,X3)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X1,X3)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f296])).
% 0.20/0.53  fof(f296,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (X0 = X1 | ~r2_hidden(X1,a_2_9_lattice3(X2,X3)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | ~r4_lattice3(X2,X0,a_2_9_lattice3(X2,X3)) | ~r2_hidden(X0,a_2_9_lattice3(X2,X3)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X1,X3) | ~l3_lattices(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X2))) )),
% 0.20/0.53    inference(resolution,[],[f223,f267])).
% 0.20/0.53  fof(f223,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r4_lattice3(X0,X3,X1) | X2 = X3 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~r4_lattice3(X0,X2,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f212])).
% 0.20/0.53  fof(f212,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r4_lattice3(X0,X3,X1) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~r4_lattice3(X0,X2,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(superposition,[],[f77,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k15_lattice3(X0,X2) = X1 | ~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | ~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | (~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattice3)).
% 0.20/0.53  fof(f496,plain,(
% 0.20/0.53    ( ! [X0] : (sK10 != X0 | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11) | ~sP7(sK11,sK9,X0) | ~sP8(X0,sK9,sK11)) )),
% 0.20/0.53    inference(resolution,[],[f495,f104])).
% 0.20/0.53  fof(f495,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,a_2_9_lattice3(sK9,sK11)) | sK10 != X0 | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f494,f67])).
% 0.20/0.53  fof(f494,plain,(
% 0.20/0.53    ( ! [X0] : (sK10 != X0 | ~r2_hidden(X0,a_2_9_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11) | v2_struct_0(sK9)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f493,f68])).
% 0.20/0.53  fof(f493,plain,(
% 0.20/0.53    ( ! [X0] : (sK10 != X0 | ~r2_hidden(X0,a_2_9_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11) | ~v10_lattices(sK9) | v2_struct_0(sK9)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f492,f69])).
% 0.20/0.53  fof(f492,plain,(
% 0.20/0.53    ( ! [X0] : (sK10 != X0 | ~r2_hidden(X0,a_2_9_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f491,f70])).
% 0.20/0.53  fof(f491,plain,(
% 0.20/0.53    ( ! [X0] : (sK10 != X0 | ~r2_hidden(X0,a_2_9_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11) | ~l3_lattices(sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f490])).
% 0.20/0.53  fof(f490,plain,(
% 0.20/0.53    ( ! [X0] : (sK10 != X0 | ~r2_hidden(X0,a_2_9_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11) | ~l3_lattices(sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 0.20/0.53    inference(resolution,[],[f484,f267])).
% 0.20/0.53  fof(f484,plain,(
% 0.20/0.53    ( ! [X0] : (~r4_lattice3(sK9,X0,a_2_9_lattice3(sK9,sK11)) | sK10 != X0 | ~r2_hidden(X0,a_2_9_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f483,f67])).
% 0.20/0.53  fof(f483,plain,(
% 0.20/0.53    ( ! [X0] : (sK10 != X0 | ~r4_lattice3(sK9,X0,a_2_9_lattice3(sK9,sK11)) | ~r2_hidden(X0,a_2_9_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | v2_struct_0(sK9)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f482,f68])).
% 0.20/0.53  fof(f482,plain,(
% 0.20/0.53    ( ! [X0] : (sK10 != X0 | ~r4_lattice3(sK9,X0,a_2_9_lattice3(sK9,sK11)) | ~r2_hidden(X0,a_2_9_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~v10_lattices(sK9) | v2_struct_0(sK9)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f481,f69])).
% 0.20/0.53  fof(f481,plain,(
% 0.20/0.53    ( ! [X0] : (sK10 != X0 | ~r4_lattice3(sK9,X0,a_2_9_lattice3(sK9,sK11)) | ~r2_hidden(X0,a_2_9_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f480,f70])).
% 0.20/0.53  fof(f480,plain,(
% 0.20/0.53    ( ! [X0] : (sK10 != X0 | ~r4_lattice3(sK9,X0,a_2_9_lattice3(sK9,sK11)) | ~r2_hidden(X0,a_2_9_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~l3_lattices(sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) )),
% 0.20/0.53    inference(superposition,[],[f477,f77])).
% 0.20/0.53  fof(f477,plain,(
% 0.20/0.53    sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11))),
% 0.20/0.53    inference(subsumption_resolution,[],[f476,f171])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    sP2(sK10,sK9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f170,f67])).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    sP2(sK10,sK9) | v2_struct_0(sK9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f169,f68])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    sP2(sK10,sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f168,f69])).
% 0.20/0.53  fof(f168,plain,(
% 0.20/0.53    sP2(sK10,sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f162,f70])).
% 0.20/0.53  fof(f162,plain,(
% 0.20/0.53    sP2(sK10,sK9) | ~l3_lattices(sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)),
% 0.20/0.53    inference(resolution,[],[f87,f71])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP2(X1,X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(definition_folding,[],[f17,f28,f27,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X2,X0,X1] : (sP1(X2,X0,X1) <=> (sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X1,X0] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> sP1(X2,X0,X1)) | ~sP2(X1,X0))),
% 0.20/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).
% 0.20/0.53  fof(f476,plain,(
% 0.20/0.53    sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)) | ~sP2(sK10,sK9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f475,f73])).
% 0.20/0.53  fof(f475,plain,(
% 0.20/0.53    ~r3_lattice3(sK9,sK10,sK11) | sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)) | ~sP2(sK10,sK9)),
% 0.20/0.53    inference(inner_rewriting,[],[f474])).
% 0.20/0.53  fof(f474,plain,(
% 0.20/0.53    ~r3_lattice3(sK9,k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK11) | sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)) | ~sP2(k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f473,f68])).
% 0.20/0.53  fof(f473,plain,(
% 0.20/0.53    ~v10_lattices(sK9) | ~r3_lattice3(sK9,k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK11) | sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)) | ~sP2(k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f472,f70])).
% 0.20/0.53  fof(f472,plain,(
% 0.20/0.53    ~l3_lattices(sK9) | ~v10_lattices(sK9) | ~r3_lattice3(sK9,k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK11) | sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)) | ~sP2(k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f471,f69])).
% 0.20/0.53  fof(f471,plain,(
% 0.20/0.53    ~v4_lattice3(sK9) | ~l3_lattices(sK9) | ~v10_lattices(sK9) | ~r3_lattice3(sK9,k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK11) | sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)) | ~sP2(k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f451,f67])).
% 0.20/0.53  fof(f451,plain,(
% 0.20/0.53    v2_struct_0(sK9) | ~v4_lattice3(sK9) | ~l3_lattices(sK9) | ~v10_lattices(sK9) | ~r3_lattice3(sK9,k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK11) | sK10 != k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)) | ~sP2(k15_lattice3(sK9,a_2_9_lattice3(sK9,sK11)),sK9)),
% 0.20/0.53    inference(resolution,[],[f449,f152])).
% 0.20/0.53  fof(f152,plain,(
% 0.20/0.53    ( ! [X6] : (~sP0(X6,sK9,sK11) | ~r3_lattice3(sK9,X6,sK11) | sK10 != X6 | ~sP2(X6,sK9)) )),
% 0.20/0.53    inference(resolution,[],[f82,f141])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    ( ! [X0] : (~sP1(sK11,sK9,X0) | sK10 != X0 | ~sP2(X0,sK9)) )),
% 0.20/0.53    inference(superposition,[],[f74,f79])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k16_lattice3(X1,X2) = X0 | ~sP1(X2,X1,X0) | ~sP2(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : ((k16_lattice3(X1,X2) = X0 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k16_lattice3(X1,X2) != X0)) | ~sP2(X0,X1))),
% 0.20/0.53    inference(rectify,[],[f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ! [X1,X0] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ~sP1(X2,X0,X1)) & (sP1(X2,X0,X1) | k16_lattice3(X0,X2) != X1)) | ~sP2(X1,X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f28])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    sK10 != k16_lattice3(sK9,sK11)),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) & ((sP0(X2,X1,X0) & r3_lattice3(X1,X2,X0)) | ~sP1(X0,X1,X2)))),
% 0.20/0.53    inference(rectify,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | ~sP0(X1,X0,X2) | ~r3_lattice3(X0,X1,X2)) & ((sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP1(X2,X0,X1)))),
% 0.20/0.53    inference(flattening,[],[f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | (~sP0(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) & ((sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP1(X2,X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f27])).
% 0.20/0.53  fof(f449,plain,(
% 0.20/0.53    ( ! [X0,X1] : (sP0(k15_lattice3(X0,a_2_9_lattice3(X0,X1)),X0,X1) | v2_struct_0(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~v10_lattices(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f448,f84])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r3_lattices(X1,sK12(X0,X1,X2),X0) & r3_lattice3(X1,sK12(X0,X1,X2),X2) & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f49,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r3_lattices(X1,sK12(X0,X1,X2),X0) & r3_lattice3(X1,sK12(X0,X1,X2),X2) & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.53    inference(rectify,[],[f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 0.20/0.53    inference(nnf_transformation,[],[f26])).
% 0.20/0.53  fof(f448,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_9_lattice3(X0,X1)),X0,X1) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | ~m1_subset_1(sK12(k15_lattice3(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0))) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f445])).
% 0.20/0.53  fof(f445,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_9_lattice3(X0,X1)),X0,X1) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~m1_subset_1(sK12(k15_lattice3(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0)) | sP0(k15_lattice3(X0,a_2_9_lattice3(X0,X1)),X0,X1)) )),
% 0.20/0.53    inference(resolution,[],[f327,f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK12(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f51])).
% 0.20/0.53  fof(f327,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X1,sK12(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3),X2) | v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X0) | ~m1_subset_1(sK12(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3),u1_struct_0(X1))) )),
% 0.20/0.53    inference(resolution,[],[f319,f111])).
% 0.20/0.53  fof(f319,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~sP7(X2,X1,sK12(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3)) | ~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 0.20/0.53    inference(resolution,[],[f226,f109])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~sP8(sK12(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3),X1,X2) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3) | ~sP7(X2,X1,sK12(k15_lattice3(X0,a_2_9_lattice3(X1,X2)),X0,X3)) | ~l3_lattices(X0)) )),
% 0.20/0.53    inference(resolution,[],[f185,f104])).
% 0.20/0.53  fof(f185,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK12(k15_lattice3(X0,X1),X0,X2),X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,X1),X0,X2)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f184,f84])).
% 0.20/0.53  fof(f184,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK12(k15_lattice3(X0,X1),X0,X2),X1) | ~m1_subset_1(sK12(k15_lattice3(X0,X1),X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,X1),X0,X2)) )),
% 0.20/0.53    inference(resolution,[],[f75,f86])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r3_lattices(X1,sK12(X0,X1,X2),X0) | sP0(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f51])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k15_lattice3(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (16723)------------------------------
% 0.20/0.53  % (16723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16723)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (16723)Memory used [KB]: 6396
% 0.20/0.53  % (16723)Time elapsed: 0.129 s
% 0.20/0.53  % (16723)------------------------------
% 0.20/0.53  % (16723)------------------------------
% 0.20/0.54  % (16715)Success in time 0.174 s
%------------------------------------------------------------------------------
