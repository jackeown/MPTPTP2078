%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:45 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 750 expanded)
%              Number of leaves         :   23 ( 248 expanded)
%              Depth                    :   44
%              Number of atoms          :  985 (4747 expanded)
%              Number of equality atoms :   84 ( 597 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f485,plain,(
    $false ),
    inference(subsumption_resolution,[],[f484,f68])).

fof(f68,plain,(
    m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( sK10 != k16_lattice3(sK9,sK11)
    & r3_lattice3(sK9,sK10,sK11)
    & r2_hidden(sK10,sK11)
    & m1_subset_1(sK10,u1_struct_0(sK9))
    & l3_lattices(sK9)
    & v4_lattice3(sK9)
    & v10_lattices(sK9)
    & ~ v2_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f10,f38,f37,f36])).

fof(f36,plain,
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

fof(f37,plain,
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

fof(f38,plain,
    ( ? [X2] :
        ( k16_lattice3(sK9,X2) != sK10
        & r3_lattice3(sK9,sK10,X2)
        & r2_hidden(sK10,X2) )
   => ( sK10 != k16_lattice3(sK9,sK11)
      & r3_lattice3(sK9,sK10,sK11)
      & r2_hidden(sK10,sK11) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f484,plain,(
    ~ m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(subsumption_resolution,[],[f478,f69])).

fof(f69,plain,(
    r2_hidden(sK10,sK11) ),
    inference(cnf_transformation,[],[f39])).

fof(f478,plain,
    ( ~ r2_hidden(sK10,sK11)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(resolution,[],[f471,f70])).

fof(f70,plain,(
    r3_lattice3(sK9,sK10,sK11) ),
    inference(cnf_transformation,[],[f39])).

fof(f471,plain,(
    ! [X0] :
      ( ~ r3_lattice3(sK9,X0,sK11)
      | ~ r2_hidden(X0,sK11)
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(resolution,[],[f470,f107])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( sP7(X0,X1,X3)
      | ~ r3_lattice3(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X0,X1,X2)
      | ~ r3_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f63])).

% (23947)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f63,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK15(X0,X1,X2),X0)
        & sK15(X0,X1,X2) = X2
        & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( sP7(X2,X1,X0)
    <=> ? [X3] :
          ( r3_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f470,plain,(
    ! [X0] :
      ( ~ sP7(sK11,sK9,X0)
      | ~ r2_hidden(X0,sK11) ) ),
    inference(subsumption_resolution,[],[f469,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f39])).

fof(f469,plain,(
    ! [X0] :
      ( ~ sP7(sK11,sK9,X0)
      | ~ r2_hidden(X0,sK11)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f468,f67])).

fof(f67,plain,(
    l3_lattices(sK9) ),
    inference(cnf_transformation,[],[f39])).

fof(f468,plain,(
    ! [X0] :
      ( ~ sP7(sK11,sK9,X0)
      | ~ r2_hidden(X0,sK11)
      | ~ l3_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(resolution,[],[f465,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( sP8(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( sP8(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f22,f34,f33])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> sP7(X2,X1,X0) )
      | ~ sP8(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

fof(f465,plain,(
    ! [X0] :
      ( ~ sP8(X0,sK9,sK11)
      | ~ sP7(sK11,sK9,X0)
      | ~ r2_hidden(X0,sK11) ) ),
    inference(subsumption_resolution,[],[f464,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X0,X1,X2)
      | m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X1))
      | ~ sP7(X0,X1,X2)
      | ~ sP7(X0,X1,X2) ) ),
    inference(superposition,[],[f101,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( sK15(X0,X1,X2) = X2
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f464,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ r2_hidden(X0,sK11)
      | ~ sP7(sK11,sK9,X0)
      | ~ sP8(X0,sK9,sK11) ) ),
    inference(subsumption_resolution,[],[f461,f403])).

fof(f403,plain,(
    ! [X0] :
      ( ~ sP7(sK11,sK9,X0)
      | sK10 = X0
      | ~ r2_hidden(X0,sK11) ) ),
    inference(duplicate_literal_removal,[],[f402])).

fof(f402,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK11)
      | sK10 = X0
      | ~ sP7(sK11,sK9,X0)
      | ~ sP7(sK11,sK9,X0) ) ),
    inference(superposition,[],[f394,f102])).

fof(f394,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK15(sK11,sK9,X5),sK11)
      | sK10 = sK15(sK11,sK9,X5)
      | ~ sP7(sK11,sK9,X5) ) ),
    inference(subsumption_resolution,[],[f374,f101])).

fof(f374,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK15(sK11,sK9,X5),sK11)
      | sK10 = sK15(sK11,sK9,X5)
      | ~ m1_subset_1(sK15(sK11,sK9,X5),u1_struct_0(sK9))
      | ~ sP7(sK11,sK9,X5) ) ),
    inference(resolution,[],[f363,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK15(X0,X1,X2),X0)
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f363,plain,(
    ! [X0] :
      ( ~ r3_lattice3(sK9,X0,sK11)
      | ~ r2_hidden(X0,sK11)
      | sK10 = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(subsumption_resolution,[],[f362,f68])).

fof(f362,plain,(
    ! [X0] :
      ( sK10 = X0
      | ~ r2_hidden(X0,sK11)
      | ~ m1_subset_1(sK10,u1_struct_0(sK9))
      | ~ r3_lattice3(sK9,X0,sK11)
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(subsumption_resolution,[],[f361,f65])).

fof(f65,plain,(
    v10_lattices(sK9) ),
    inference(cnf_transformation,[],[f39])).

fof(f361,plain,(
    ! [X0] :
      ( sK10 = X0
      | ~ r2_hidden(X0,sK11)
      | ~ v10_lattices(sK9)
      | ~ m1_subset_1(sK10,u1_struct_0(sK9))
      | ~ r3_lattice3(sK9,X0,sK11)
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(subsumption_resolution,[],[f360,f66])).

fof(f66,plain,(
    v4_lattice3(sK9) ),
    inference(cnf_transformation,[],[f39])).

fof(f360,plain,(
    ! [X0] :
      ( sK10 = X0
      | ~ r2_hidden(X0,sK11)
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | ~ m1_subset_1(sK10,u1_struct_0(sK9))
      | ~ r3_lattice3(sK9,X0,sK11)
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(subsumption_resolution,[],[f359,f67])).

fof(f359,plain,(
    ! [X0] :
      ( sK10 = X0
      | ~ r2_hidden(X0,sK11)
      | ~ l3_lattices(sK9)
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | ~ m1_subset_1(sK10,u1_struct_0(sK9))
      | ~ r3_lattice3(sK9,X0,sK11)
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(subsumption_resolution,[],[f358,f69])).

fof(f358,plain,(
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
    inference(subsumption_resolution,[],[f350,f64])).

fof(f350,plain,(
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
    inference(resolution,[],[f345,f70])).

fof(f345,plain,(
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
    inference(resolution,[],[f340,f107])).

fof(f340,plain,(
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
    inference(resolution,[],[f335,f107])).

fof(f335,plain,(
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
    inference(subsumption_resolution,[],[f334,f105])).

fof(f334,plain,(
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
    inference(subsumption_resolution,[],[f333,f127])).

fof(f333,plain,(
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
    inference(subsumption_resolution,[],[f330,f127])).

fof(f330,plain,(
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
    inference(resolution,[],[f327,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ sP7(X2,X1,X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ~ sP7(X2,X1,X0) )
        & ( sP7(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ sP8(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f327,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X3))
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
    inference(subsumption_resolution,[],[f324,f105])).

fof(f324,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | X0 = X2
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r2_hidden(X0,X3)
      | ~ r2_hidden(X2,X3)
      | ~ sP7(X3,X1,X2)
      | ~ sP8(X2,X1,X3) ) ),
    inference(resolution,[],[f323,f100])).

fof(f323,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,a_2_1_lattice3(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | X0 = X3
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f322])).

fof(f322,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | X0 = X3
      | ~ r2_hidden(X3,a_2_1_lattice3(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X3,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f261,f251])).

fof(f251,plain,(
    ! [X6,X4,X5] :
      ( r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | ~ m1_subset_1(X4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f250,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP4(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP4(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f18,f28,f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP3(X1,X0,X2) )
      | ~ sP4(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f250,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6))
      | ~ sP4(X5,X4) ) ),
    inference(resolution,[],[f248,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP3(X1,X0,X2) )
          & ( sP3(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP4(X0,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f248,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f247,f120])).

fof(f120,plain,(
    ! [X4,X5,X3] :
      ( sP6(X3,sK13(X4,X3,X5))
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | sP3(X4,X3,X5) ) ),
    inference(resolution,[],[f98,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK13(X0,X1,X2),X0)
        & r2_hidden(sK13(X0,X1,X2),X2)
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP6(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP6(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f20,f31,f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( sP5(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP5(X1,X0,X2) )
      | ~ sP6(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f247,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ sP6(X2,sK13(X0,X2,a_2_1_lattice3(X2,X1)))
      | sP3(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f246])).

fof(f246,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ sP6(X2,sK13(X0,X2,a_2_1_lattice3(X2,X1)))
      | sP3(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | sP3(X0,X2,a_2_1_lattice3(X2,X1)) ) ),
    inference(resolution,[],[f179,f216])).

fof(f216,plain,(
    ! [X14,X12,X15,X13] :
      ( r3_lattice3(X14,sK13(X12,X13,a_2_1_lattice3(X14,X15)),X15)
      | ~ l3_lattices(X14)
      | v2_struct_0(X14)
      | sP3(X12,X13,a_2_1_lattice3(X14,X15)) ) ),
    inference(resolution,[],[f211,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X0,X1,X2)
      | r3_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,X2,X0)
      | ~ sP7(X0,X1,X2)
      | ~ sP7(X0,X1,X2) ) ),
    inference(superposition,[],[f103,f102])).

fof(f211,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X0,X1,sK13(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP3(X2,X3,a_2_1_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f149,f105])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP8(sK13(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0)
      | sP7(X0,X1,sK13(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP3(X2,X3,a_2_1_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f99,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK13(X0,X1,X2),X2)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | sP7(X2,X1,X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f179,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattice3(X1,sK13(X0,X1,X3),X2)
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ sP6(X1,sK13(X0,X1,X3))
      | sP3(X0,X1,X3) ) ),
    inference(resolution,[],[f169,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK13(X0,X1,X2),X0)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f169,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X2,X3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ r3_lattice3(X2,X3,X1)
      | ~ sP6(X2,X3) ) ),
    inference(resolution,[],[f94,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( sP5(X1,X0,X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ sP6(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP5(X1,X0,X2) )
          & ( sP5(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP6(X0,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK14(X0,X1,X2))
        & r2_hidden(sK14(X0,X1,X2),X2)
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f261,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_lattice3(X2,X0,a_2_1_lattice3(X2,X3))
      | ~ r2_hidden(X1,a_2_1_lattice3(X2,X3))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | X0 = X1
      | ~ r2_hidden(X0,a_2_1_lattice3(X2,X3))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X1,X3) ) ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X1
      | ~ r2_hidden(X1,a_2_1_lattice3(X2,X3))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ r4_lattice3(X2,X0,a_2_1_lattice3(X2,X3))
      | ~ r2_hidden(X0,a_2_1_lattice3(X2,X3))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X1,X3)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f210,f251])).

fof(f210,plain,(
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
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,(
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
    inference(superposition,[],[f74,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X2) = X1
      | ~ r4_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
              ( ( r4_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k15_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattice3)).

fof(f461,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ r2_hidden(X0,sK11)
      | ~ sP7(sK11,sK9,X0)
      | ~ sP8(X0,sK9,sK11) ) ),
    inference(resolution,[],[f460,f100])).

fof(f460,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(sK9,sK11))
      | sK10 != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ r2_hidden(X0,sK11) ) ),
    inference(subsumption_resolution,[],[f459,f64])).

fof(f459,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r2_hidden(X0,a_2_1_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ r2_hidden(X0,sK11)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f458,f67])).

fof(f458,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r2_hidden(X0,a_2_1_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ r2_hidden(X0,sK11)
      | ~ l3_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(duplicate_literal_removal,[],[f457])).

fof(f457,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r2_hidden(X0,a_2_1_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ r2_hidden(X0,sK11)
      | ~ l3_lattices(sK9)
      | v2_struct_0(sK9)
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(resolution,[],[f451,f251])).

fof(f451,plain,(
    ! [X0] :
      ( ~ r4_lattice3(sK9,X0,a_2_1_lattice3(sK9,sK11))
      | sK10 != X0
      | ~ r2_hidden(X0,a_2_1_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9)) ) ),
    inference(subsumption_resolution,[],[f450,f64])).

fof(f450,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r4_lattice3(sK9,X0,a_2_1_lattice3(sK9,sK11))
      | ~ r2_hidden(X0,a_2_1_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f449,f65])).

fof(f449,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r4_lattice3(sK9,X0,a_2_1_lattice3(sK9,sK11))
      | ~ r2_hidden(X0,a_2_1_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f448,f66])).

fof(f448,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r4_lattice3(sK9,X0,a_2_1_lattice3(sK9,sK11))
      | ~ r2_hidden(X0,a_2_1_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f447,f67])).

fof(f447,plain,(
    ! [X0] :
      ( sK10 != X0
      | ~ r4_lattice3(sK9,X0,a_2_1_lattice3(sK9,sK11))
      | ~ r2_hidden(X0,a_2_1_lattice3(sK9,sK11))
      | ~ m1_subset_1(X0,u1_struct_0(sK9))
      | ~ l3_lattices(sK9)
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(superposition,[],[f443,f74])).

fof(f443,plain,(
    sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)) ),
    inference(subsumption_resolution,[],[f442,f161])).

fof(f161,plain,(
    sP2(sK10,sK9) ),
    inference(subsumption_resolution,[],[f160,f64])).

fof(f160,plain,
    ( sP2(sK10,sK9)
    | v2_struct_0(sK9) ),
    inference(subsumption_resolution,[],[f159,f65])).

fof(f159,plain,
    ( sP2(sK10,sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(subsumption_resolution,[],[f158,f66])).

fof(f158,plain,
    ( sP2(sK10,sK9)
    | ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(subsumption_resolution,[],[f153,f67])).

fof(f153,plain,
    ( sP2(sK10,sK9)
    | ~ l3_lattices(sK9)
    | ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(resolution,[],[f84,f68])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP2(X1,X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f25,f24,f23])).

fof(f23,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r3_lattices(X0,X3,X1)
          | ~ r3_lattice3(X0,X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
    <=> ( sP0(X1,X0,X2)
        & r3_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( k16_lattice3(X0,X2) = X1
        <=> sP1(X2,X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f442,plain,
    ( sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11))
    | ~ sP2(sK10,sK9) ),
    inference(subsumption_resolution,[],[f441,f70])).

fof(f441,plain,
    ( ~ r3_lattice3(sK9,sK10,sK11)
    | sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11))
    | ~ sP2(sK10,sK9) ),
    inference(inner_rewriting,[],[f440])).

fof(f440,plain,
    ( ~ r3_lattice3(sK9,k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK11)
    | sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11))
    | ~ sP2(k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK9) ),
    inference(subsumption_resolution,[],[f439,f65])).

fof(f439,plain,
    ( ~ v10_lattices(sK9)
    | ~ r3_lattice3(sK9,k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK11)
    | sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11))
    | ~ sP2(k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK9) ),
    inference(subsumption_resolution,[],[f438,f67])).

fof(f438,plain,
    ( ~ l3_lattices(sK9)
    | ~ v10_lattices(sK9)
    | ~ r3_lattice3(sK9,k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK11)
    | sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11))
    | ~ sP2(k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK9) ),
    inference(subsumption_resolution,[],[f437,f66])).

fof(f437,plain,
    ( ~ v4_lattice3(sK9)
    | ~ l3_lattices(sK9)
    | ~ v10_lattices(sK9)
    | ~ r3_lattice3(sK9,k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK11)
    | sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11))
    | ~ sP2(k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK9) ),
    inference(subsumption_resolution,[],[f417,f64])).

fof(f417,plain,
    ( v2_struct_0(sK9)
    | ~ v4_lattice3(sK9)
    | ~ l3_lattices(sK9)
    | ~ v10_lattices(sK9)
    | ~ r3_lattice3(sK9,k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK11)
    | sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11))
    | ~ sP2(k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK9) ),
    inference(resolution,[],[f408,f144])).

fof(f144,plain,(
    ! [X6] :
      ( ~ sP0(X6,sK9,sK11)
      | ~ r3_lattice3(sK9,X6,sK11)
      | sK10 != X6
      | ~ sP2(X6,sK9) ) ),
    inference(resolution,[],[f79,f133])).

fof(f133,plain,(
    ! [X0] :
      ( ~ sP1(sK11,sK9,X0)
      | sK10 != X0
      | ~ sP2(X0,sK9) ) ),
    inference(superposition,[],[f71,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X1,X2) = X0
      | ~ sP1(X2,X1,X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k16_lattice3(X1,X2) = X0
            | ~ sP1(X2,X1,X0) )
          & ( sP1(X2,X1,X0)
            | k16_lattice3(X1,X2) != X0 ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( ( k16_lattice3(X0,X2) = X1
            | ~ sP1(X2,X0,X1) )
          & ( sP1(X2,X0,X1)
            | k16_lattice3(X0,X2) != X1 ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f71,plain,(
    sK10 != k16_lattice3(sK9,sK11) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | ~ r3_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ~ sP0(X2,X1,X0)
        | ~ r3_lattice3(X1,X2,X0) )
      & ( ( sP0(X2,X1,X0)
          & r3_lattice3(X1,X2,X0) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ~ sP0(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP0(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ~ sP0(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP0(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f408,plain,(
    ! [X0,X1] :
      ( sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1)
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f407,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X1,X3,X0)
          & r3_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r3_lattices(X1,sK12(X0,X1,X2),X0)
        & r3_lattice3(X1,sK12(X0,X1,X2),X2)
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f407,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | ~ m1_subset_1(sK12(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f404])).

fof(f404,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ m1_subset_1(sK12(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1),u1_struct_0(X0))
      | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1) ) ),
    inference(resolution,[],[f309,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK12(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f309,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattice3(X1,sK12(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3),X2)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X0)
      | ~ m1_subset_1(sK12(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f306,f107])).

fof(f306,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X2,X1,sK12(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f204,f105])).

fof(f204,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP8(sK12(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3),X1,X2)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3)
      | ~ sP7(X2,X1,sK12(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3))
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f178,f100])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK12(k15_lattice3(X0,X1),X0,X2),X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,X1),X0,X2) ) ),
    inference(subsumption_resolution,[],[f177,f81])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK12(k15_lattice3(X0,X1),X0,X2),X1)
      | ~ m1_subset_1(sK12(k15_lattice3(X0,X1),X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,X1),X0,X2) ) ),
    inference(resolution,[],[f72,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X1,sK12(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:26:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (23936)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (23944)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (23944)Refutation not found, incomplete strategy% (23944)------------------------------
% 0.21/0.53  % (23944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23944)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23944)Memory used [KB]: 6140
% 0.21/0.53  % (23944)Time elapsed: 0.101 s
% 0.21/0.53  % (23944)------------------------------
% 0.21/0.53  % (23944)------------------------------
% 0.21/0.55  % (23934)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.56  % (23931)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.56  % (23931)Refutation not found, incomplete strategy% (23931)------------------------------
% 0.21/0.56  % (23931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (23931)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (23931)Memory used [KB]: 10490
% 0.21/0.56  % (23931)Time elapsed: 0.126 s
% 0.21/0.56  % (23931)------------------------------
% 0.21/0.56  % (23931)------------------------------
% 0.21/0.56  % (23932)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % (23938)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.57  % (23933)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.57  % (23939)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.54/0.58  % (23955)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.54/0.58  % (23946)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.54/0.58  % (23943)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.54/0.58  % (23942)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.54/0.58  % (23942)Refutation not found, incomplete strategy% (23942)------------------------------
% 1.54/0.58  % (23942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (23942)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  
% 1.54/0.58  % (23942)Memory used [KB]: 10490
% 1.54/0.58  % (23942)Time elapsed: 0.152 s
% 1.54/0.58  % (23942)------------------------------
% 1.54/0.58  % (23942)------------------------------
% 1.54/0.59  % (23938)Refutation not found, incomplete strategy% (23938)------------------------------
% 1.54/0.59  % (23938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.59  % (23938)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.59  
% 1.54/0.59  % (23938)Memory used [KB]: 1663
% 1.54/0.59  % (23938)Time elapsed: 0.114 s
% 1.54/0.59  % (23938)------------------------------
% 1.54/0.59  % (23938)------------------------------
% 1.54/0.59  % (23937)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.54/0.59  % (23951)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.54/0.59  % (23948)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.83/0.59  % (23956)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.83/0.60  % (23935)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.83/0.60  % (23940)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.83/0.60  % (23950)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.83/0.60  % (23953)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.83/0.61  % (23941)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.83/0.61  % (23937)Refutation not found, incomplete strategy% (23937)------------------------------
% 1.83/0.61  % (23937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.61  % (23937)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.61  
% 1.83/0.61  % (23937)Memory used [KB]: 10618
% 1.83/0.61  % (23937)Time elapsed: 0.159 s
% 1.83/0.61  % (23937)------------------------------
% 1.83/0.61  % (23937)------------------------------
% 1.83/0.61  % (23954)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.83/0.61  % (23952)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.83/0.61  % (23949)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.83/0.62  % (23945)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.83/0.63  % (23935)Refutation found. Thanks to Tanya!
% 1.83/0.63  % SZS status Theorem for theBenchmark
% 1.83/0.63  % SZS output start Proof for theBenchmark
% 1.83/0.63  fof(f485,plain,(
% 1.83/0.63    $false),
% 1.83/0.63    inference(subsumption_resolution,[],[f484,f68])).
% 1.83/0.63  fof(f68,plain,(
% 1.83/0.63    m1_subset_1(sK10,u1_struct_0(sK9))),
% 1.83/0.63    inference(cnf_transformation,[],[f39])).
% 1.83/0.63  fof(f39,plain,(
% 1.83/0.63    ((sK10 != k16_lattice3(sK9,sK11) & r3_lattice3(sK9,sK10,sK11) & r2_hidden(sK10,sK11)) & m1_subset_1(sK10,u1_struct_0(sK9))) & l3_lattices(sK9) & v4_lattice3(sK9) & v10_lattices(sK9) & ~v2_struct_0(sK9)),
% 1.83/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f10,f38,f37,f36])).
% 1.83/0.63  fof(f36,plain,(
% 1.83/0.63    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK9,X2) != X1 & r3_lattice3(sK9,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK9))) & l3_lattices(sK9) & v4_lattice3(sK9) & v10_lattices(sK9) & ~v2_struct_0(sK9))),
% 1.83/0.63    introduced(choice_axiom,[])).
% 1.83/0.63  fof(f37,plain,(
% 1.83/0.63    ? [X1] : (? [X2] : (k16_lattice3(sK9,X2) != X1 & r3_lattice3(sK9,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK9))) => (? [X2] : (k16_lattice3(sK9,X2) != sK10 & r3_lattice3(sK9,sK10,X2) & r2_hidden(sK10,X2)) & m1_subset_1(sK10,u1_struct_0(sK9)))),
% 1.83/0.63    introduced(choice_axiom,[])).
% 1.83/0.63  fof(f38,plain,(
% 1.83/0.63    ? [X2] : (k16_lattice3(sK9,X2) != sK10 & r3_lattice3(sK9,sK10,X2) & r2_hidden(sK10,X2)) => (sK10 != k16_lattice3(sK9,sK11) & r3_lattice3(sK9,sK10,sK11) & r2_hidden(sK10,sK11))),
% 1.83/0.63    introduced(choice_axiom,[])).
% 1.83/0.63  fof(f10,plain,(
% 1.83/0.63    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.83/0.63    inference(flattening,[],[f9])).
% 1.83/0.63  fof(f9,plain,(
% 1.83/0.63    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.83/0.63    inference(ennf_transformation,[],[f8])).
% 1.83/0.63  fof(f8,negated_conjecture,(
% 1.83/0.63    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 1.83/0.63    inference(negated_conjecture,[],[f7])).
% 1.83/0.63  fof(f7,conjecture,(
% 1.83/0.63    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 1.83/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).
% 1.83/0.63  fof(f484,plain,(
% 1.83/0.63    ~m1_subset_1(sK10,u1_struct_0(sK9))),
% 1.83/0.63    inference(subsumption_resolution,[],[f478,f69])).
% 1.83/0.63  fof(f69,plain,(
% 1.83/0.63    r2_hidden(sK10,sK11)),
% 1.83/0.63    inference(cnf_transformation,[],[f39])).
% 1.83/0.63  fof(f478,plain,(
% 1.83/0.63    ~r2_hidden(sK10,sK11) | ~m1_subset_1(sK10,u1_struct_0(sK9))),
% 1.83/0.63    inference(resolution,[],[f471,f70])).
% 1.83/0.63  fof(f70,plain,(
% 1.83/0.63    r3_lattice3(sK9,sK10,sK11)),
% 1.83/0.63    inference(cnf_transformation,[],[f39])).
% 1.83/0.63  fof(f471,plain,(
% 1.83/0.63    ( ! [X0] : (~r3_lattice3(sK9,X0,sK11) | ~r2_hidden(X0,sK11) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 1.83/0.63    inference(resolution,[],[f470,f107])).
% 1.83/0.63  fof(f107,plain,(
% 1.83/0.63    ( ! [X0,X3,X1] : (sP7(X0,X1,X3) | ~r3_lattice3(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 1.83/0.63    inference(equality_resolution,[],[f104])).
% 1.83/0.63  fof(f104,plain,(
% 1.83/0.63    ( ! [X2,X0,X3,X1] : (sP7(X0,X1,X2) | ~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 1.83/0.63    inference(cnf_transformation,[],[f63])).
% 1.83/0.64  % (23947)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.83/0.64  fof(f63,plain,(
% 1.83/0.64    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK15(X0,X1,X2),X0) & sK15(X0,X1,X2) = X2 & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 1.83/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f61,f62])).
% 1.83/0.64  fof(f62,plain,(
% 1.83/0.64    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK15(X0,X1,X2),X0) & sK15(X0,X1,X2) = X2 & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))))),
% 1.83/0.64    introduced(choice_axiom,[])).
% 1.83/0.64  fof(f61,plain,(
% 1.83/0.64    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 1.83/0.64    inference(rectify,[],[f60])).
% 1.83/0.64  fof(f60,plain,(
% 1.83/0.64    ! [X2,X1,X0] : ((sP7(X2,X1,X0) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP7(X2,X1,X0)))),
% 1.83/0.64    inference(nnf_transformation,[],[f33])).
% 1.83/0.64  fof(f33,plain,(
% 1.83/0.64    ! [X2,X1,X0] : (sP7(X2,X1,X0) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 1.83/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 1.83/0.64  fof(f470,plain,(
% 1.83/0.64    ( ! [X0] : (~sP7(sK11,sK9,X0) | ~r2_hidden(X0,sK11)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f469,f64])).
% 1.83/0.64  fof(f64,plain,(
% 1.83/0.64    ~v2_struct_0(sK9)),
% 1.83/0.64    inference(cnf_transformation,[],[f39])).
% 1.83/0.64  fof(f469,plain,(
% 1.83/0.64    ( ! [X0] : (~sP7(sK11,sK9,X0) | ~r2_hidden(X0,sK11) | v2_struct_0(sK9)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f468,f67])).
% 1.83/0.64  fof(f67,plain,(
% 1.83/0.64    l3_lattices(sK9)),
% 1.83/0.64    inference(cnf_transformation,[],[f39])).
% 1.83/0.64  fof(f468,plain,(
% 1.83/0.64    ( ! [X0] : (~sP7(sK11,sK9,X0) | ~r2_hidden(X0,sK11) | ~l3_lattices(sK9) | v2_struct_0(sK9)) )),
% 1.83/0.64    inference(resolution,[],[f465,f105])).
% 1.83/0.64  fof(f105,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (sP8(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f35])).
% 1.83/0.64  fof(f35,plain,(
% 1.83/0.64    ! [X0,X1,X2] : (sP8(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 1.83/0.64    inference(definition_folding,[],[f22,f34,f33])).
% 1.83/0.64  fof(f34,plain,(
% 1.83/0.64    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> sP7(X2,X1,X0)) | ~sP8(X0,X1,X2))),
% 1.83/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 1.83/0.64  fof(f22,plain,(
% 1.83/0.64    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 1.83/0.64    inference(flattening,[],[f21])).
% 1.83/0.64  fof(f21,plain,(
% 1.83/0.64    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 1.83/0.64    inference(ennf_transformation,[],[f3])).
% 1.83/0.64  fof(f3,axiom,(
% 1.83/0.64    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.83/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).
% 1.83/0.64  fof(f465,plain,(
% 1.83/0.64    ( ! [X0] : (~sP8(X0,sK9,sK11) | ~sP7(sK11,sK9,X0) | ~r2_hidden(X0,sK11)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f464,f127])).
% 1.83/0.64  fof(f127,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (~sP7(X0,X1,X2) | m1_subset_1(X2,u1_struct_0(X1))) )),
% 1.83/0.64    inference(duplicate_literal_removal,[],[f126])).
% 1.83/0.64  fof(f126,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X1)) | ~sP7(X0,X1,X2) | ~sP7(X0,X1,X2)) )),
% 1.83/0.64    inference(superposition,[],[f101,f102])).
% 1.83/0.64  fof(f102,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (sK15(X0,X1,X2) = X2 | ~sP7(X0,X1,X2)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f63])).
% 1.83/0.64  fof(f101,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) | ~sP7(X0,X1,X2)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f63])).
% 1.83/0.64  fof(f464,plain,(
% 1.83/0.64    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11) | ~sP7(sK11,sK9,X0) | ~sP8(X0,sK9,sK11)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f461,f403])).
% 1.83/0.64  fof(f403,plain,(
% 1.83/0.64    ( ! [X0] : (~sP7(sK11,sK9,X0) | sK10 = X0 | ~r2_hidden(X0,sK11)) )),
% 1.83/0.64    inference(duplicate_literal_removal,[],[f402])).
% 1.83/0.64  fof(f402,plain,(
% 1.83/0.64    ( ! [X0] : (~r2_hidden(X0,sK11) | sK10 = X0 | ~sP7(sK11,sK9,X0) | ~sP7(sK11,sK9,X0)) )),
% 1.83/0.64    inference(superposition,[],[f394,f102])).
% 1.83/0.64  fof(f394,plain,(
% 1.83/0.64    ( ! [X5] : (~r2_hidden(sK15(sK11,sK9,X5),sK11) | sK10 = sK15(sK11,sK9,X5) | ~sP7(sK11,sK9,X5)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f374,f101])).
% 1.83/0.64  fof(f374,plain,(
% 1.83/0.64    ( ! [X5] : (~r2_hidden(sK15(sK11,sK9,X5),sK11) | sK10 = sK15(sK11,sK9,X5) | ~m1_subset_1(sK15(sK11,sK9,X5),u1_struct_0(sK9)) | ~sP7(sK11,sK9,X5)) )),
% 1.83/0.64    inference(resolution,[],[f363,f103])).
% 1.83/0.64  fof(f103,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK15(X0,X1,X2),X0) | ~sP7(X0,X1,X2)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f63])).
% 1.83/0.64  fof(f363,plain,(
% 1.83/0.64    ( ! [X0] : (~r3_lattice3(sK9,X0,sK11) | ~r2_hidden(X0,sK11) | sK10 = X0 | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f362,f68])).
% 1.83/0.64  fof(f362,plain,(
% 1.83/0.64    ( ! [X0] : (sK10 = X0 | ~r2_hidden(X0,sK11) | ~m1_subset_1(sK10,u1_struct_0(sK9)) | ~r3_lattice3(sK9,X0,sK11) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f361,f65])).
% 1.83/0.64  fof(f65,plain,(
% 1.83/0.64    v10_lattices(sK9)),
% 1.83/0.64    inference(cnf_transformation,[],[f39])).
% 1.83/0.64  fof(f361,plain,(
% 1.83/0.64    ( ! [X0] : (sK10 = X0 | ~r2_hidden(X0,sK11) | ~v10_lattices(sK9) | ~m1_subset_1(sK10,u1_struct_0(sK9)) | ~r3_lattice3(sK9,X0,sK11) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f360,f66])).
% 1.83/0.64  fof(f66,plain,(
% 1.83/0.64    v4_lattice3(sK9)),
% 1.83/0.64    inference(cnf_transformation,[],[f39])).
% 1.83/0.64  fof(f360,plain,(
% 1.83/0.64    ( ! [X0] : (sK10 = X0 | ~r2_hidden(X0,sK11) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | ~m1_subset_1(sK10,u1_struct_0(sK9)) | ~r3_lattice3(sK9,X0,sK11) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f359,f67])).
% 1.83/0.64  fof(f359,plain,(
% 1.83/0.64    ( ! [X0] : (sK10 = X0 | ~r2_hidden(X0,sK11) | ~l3_lattices(sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | ~m1_subset_1(sK10,u1_struct_0(sK9)) | ~r3_lattice3(sK9,X0,sK11) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f358,f69])).
% 1.83/0.64  fof(f358,plain,(
% 1.83/0.64    ( ! [X0] : (sK10 = X0 | ~r2_hidden(X0,sK11) | ~r2_hidden(sK10,sK11) | ~l3_lattices(sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | ~m1_subset_1(sK10,u1_struct_0(sK9)) | ~r3_lattice3(sK9,X0,sK11) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f350,f64])).
% 1.83/0.64  fof(f350,plain,(
% 1.83/0.64    ( ! [X0] : (v2_struct_0(sK9) | sK10 = X0 | ~r2_hidden(X0,sK11) | ~r2_hidden(sK10,sK11) | ~l3_lattices(sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | ~m1_subset_1(sK10,u1_struct_0(sK9)) | ~r3_lattice3(sK9,X0,sK11) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 1.83/0.64    inference(resolution,[],[f345,f70])).
% 1.83/0.64  fof(f345,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X0,X2,X3) | v2_struct_0(X0) | X1 = X2 | ~r2_hidden(X1,X3) | ~r2_hidden(X2,X3) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X3) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 1.83/0.64    inference(resolution,[],[f340,f107])).
% 1.83/0.64  fof(f340,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~sP7(X3,X0,X1) | ~v10_lattices(X0) | v2_struct_0(X0) | X1 = X2 | ~r2_hidden(X1,X3) | ~r2_hidden(X2,X3) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~r3_lattice3(X0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.83/0.64    inference(resolution,[],[f335,f107])).
% 1.83/0.64  fof(f335,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~sP7(X3,X0,X2) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | X1 = X2 | ~r2_hidden(X1,X3) | ~r2_hidden(X2,X3) | ~l3_lattices(X0) | ~sP7(X3,X0,X1)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f334,f105])).
% 1.83/0.64  fof(f334,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | X1 = X2 | ~r2_hidden(X1,X3) | ~r2_hidden(X2,X3) | ~sP7(X3,X0,X2) | ~sP7(X3,X0,X1) | ~sP8(X1,X0,X3)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f333,f127])).
% 1.83/0.64  fof(f333,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | X1 = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X1,X3) | ~r2_hidden(X2,X3) | ~sP7(X3,X0,X2) | ~sP7(X3,X0,X1) | ~sP8(X1,X0,X3)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f330,f127])).
% 1.83/0.64  fof(f330,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | X1 = X2 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X1,X3) | ~r2_hidden(X2,X3) | ~sP7(X3,X0,X2) | ~sP7(X3,X0,X1) | ~sP8(X1,X0,X3)) )),
% 1.83/0.64    inference(resolution,[],[f327,f100])).
% 1.83/0.64  fof(f100,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP7(X2,X1,X0) | ~sP8(X0,X1,X2)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f59])).
% 1.83/0.64  fof(f59,plain,(
% 1.83/0.64    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP7(X2,X1,X0)) & (sP7(X2,X1,X0) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~sP8(X0,X1,X2))),
% 1.83/0.64    inference(nnf_transformation,[],[f34])).
% 1.83/0.64  fof(f327,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,a_2_1_lattice3(X1,X3)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | X0 = X2 | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r2_hidden(X0,X3) | ~r2_hidden(X2,X3) | ~sP7(X3,X1,X2)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f324,f105])).
% 1.83/0.64  fof(f324,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | X0 = X2 | ~r2_hidden(X0,a_2_1_lattice3(X1,X3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r2_hidden(X0,X3) | ~r2_hidden(X2,X3) | ~sP7(X3,X1,X2) | ~sP8(X2,X1,X3)) )),
% 1.83/0.64    inference(resolution,[],[f323,f100])).
% 1.83/0.64  fof(f323,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,a_2_1_lattice3(X1,X2)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | X0 = X3 | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | ~r2_hidden(X3,X2)) )),
% 1.83/0.64    inference(duplicate_literal_removal,[],[f322])).
% 1.83/0.64  fof(f322,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | X0 = X3 | ~r2_hidden(X3,a_2_1_lattice3(X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | ~r2_hidden(X3,X2) | ~l3_lattices(X1) | v2_struct_0(X1) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 1.83/0.64    inference(resolution,[],[f261,f251])).
% 1.83/0.64  fof(f251,plain,(
% 1.83/0.64    ( ! [X6,X4,X5] : (r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | v2_struct_0(X5) | ~m1_subset_1(X4,u1_struct_0(X5))) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f250,f91])).
% 1.83/0.64  fof(f91,plain,(
% 1.83/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP4(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f29])).
% 1.83/0.64  fof(f29,plain,(
% 1.83/0.64    ! [X0] : (! [X1] : (sP4(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.83/0.64    inference(definition_folding,[],[f18,f28,f27])).
% 1.83/0.64  fof(f27,plain,(
% 1.83/0.64    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 1.83/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.83/0.64  fof(f28,plain,(
% 1.83/0.64    ! [X0,X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> sP3(X1,X0,X2)) | ~sP4(X0,X1))),
% 1.83/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.83/0.64  fof(f18,plain,(
% 1.83/0.64    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.83/0.64    inference(flattening,[],[f17])).
% 1.83/0.64  fof(f17,plain,(
% 1.83/0.64    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.83/0.64    inference(ennf_transformation,[],[f2])).
% 1.83/0.64  fof(f2,axiom,(
% 1.83/0.64    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 1.83/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 1.83/0.64  fof(f250,plain,(
% 1.83/0.64    ( ! [X6,X4,X5] : (~m1_subset_1(X4,u1_struct_0(X5)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | v2_struct_0(X5) | r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6)) | ~sP4(X5,X4)) )),
% 1.83/0.64    inference(resolution,[],[f248,f86])).
% 1.83/0.64  fof(f86,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (~sP3(X1,X0,X2) | r4_lattice3(X0,X1,X2) | ~sP4(X0,X1)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f49])).
% 1.83/0.64  fof(f49,plain,(
% 1.83/0.64    ! [X0,X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | ~r4_lattice3(X0,X1,X2))) | ~sP4(X0,X1))),
% 1.83/0.64    inference(nnf_transformation,[],[f28])).
% 1.83/0.64  fof(f248,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (sP3(X0,X2,a_2_1_lattice3(X2,X1)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f247,f120])).
% 1.83/0.64  fof(f120,plain,(
% 1.83/0.64    ( ! [X4,X5,X3] : (sP6(X3,sK13(X4,X3,X5)) | ~l3_lattices(X3) | v2_struct_0(X3) | sP3(X4,X3,X5)) )),
% 1.83/0.64    inference(resolution,[],[f98,f88])).
% 1.83/0.64  fof(f88,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) | sP3(X0,X1,X2)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f53])).
% 1.83/0.64  fof(f53,plain,(
% 1.83/0.64    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (~r1_lattices(X1,sK13(X0,X1,X2),X0) & r2_hidden(sK13(X0,X1,X2),X2) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 1.83/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f51,f52])).
% 1.83/0.64  fof(f52,plain,(
% 1.83/0.64    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,sK13(X0,X1,X2),X0) & r2_hidden(sK13(X0,X1,X2),X2) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))))),
% 1.83/0.64    introduced(choice_axiom,[])).
% 1.83/0.64  fof(f51,plain,(
% 1.83/0.64    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 1.83/0.64    inference(rectify,[],[f50])).
% 1.83/0.64  fof(f50,plain,(
% 1.83/0.64    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP3(X1,X0,X2)))),
% 1.83/0.64    inference(nnf_transformation,[],[f27])).
% 1.83/0.64  fof(f98,plain,(
% 1.83/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP6(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f32])).
% 1.83/0.64  fof(f32,plain,(
% 1.83/0.64    ! [X0] : (! [X1] : (sP6(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.83/0.64    inference(definition_folding,[],[f20,f31,f30])).
% 1.83/0.64  fof(f30,plain,(
% 1.83/0.64    ! [X1,X0,X2] : (sP5(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 1.83/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 1.83/0.64  fof(f31,plain,(
% 1.83/0.64    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP5(X1,X0,X2)) | ~sP6(X0,X1))),
% 1.83/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 1.83/0.64  fof(f20,plain,(
% 1.83/0.64    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.83/0.64    inference(flattening,[],[f19])).
% 1.83/0.64  fof(f19,plain,(
% 1.83/0.64    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.83/0.64    inference(ennf_transformation,[],[f1])).
% 1.83/0.64  fof(f1,axiom,(
% 1.83/0.64    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 1.83/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 1.83/0.64  fof(f247,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~sP6(X2,sK13(X0,X2,a_2_1_lattice3(X2,X1))) | sP3(X0,X2,a_2_1_lattice3(X2,X1)) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 1.83/0.64    inference(duplicate_literal_removal,[],[f246])).
% 1.83/0.64  fof(f246,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~sP6(X2,sK13(X0,X2,a_2_1_lattice3(X2,X1))) | sP3(X0,X2,a_2_1_lattice3(X2,X1)) | ~l3_lattices(X2) | v2_struct_0(X2) | sP3(X0,X2,a_2_1_lattice3(X2,X1))) )),
% 1.83/0.64    inference(resolution,[],[f179,f216])).
% 1.83/0.64  fof(f216,plain,(
% 1.83/0.64    ( ! [X14,X12,X15,X13] : (r3_lattice3(X14,sK13(X12,X13,a_2_1_lattice3(X14,X15)),X15) | ~l3_lattices(X14) | v2_struct_0(X14) | sP3(X12,X13,a_2_1_lattice3(X14,X15))) )),
% 1.83/0.64    inference(resolution,[],[f211,f129])).
% 1.83/0.64  fof(f129,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (~sP7(X0,X1,X2) | r3_lattice3(X1,X2,X0)) )),
% 1.83/0.64    inference(duplicate_literal_removal,[],[f128])).
% 1.83/0.64  fof(f128,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (r3_lattice3(X1,X2,X0) | ~sP7(X0,X1,X2) | ~sP7(X0,X1,X2)) )),
% 1.83/0.64    inference(superposition,[],[f103,f102])).
% 1.83/0.64  fof(f211,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (sP7(X0,X1,sK13(X2,X3,a_2_1_lattice3(X1,X0))) | sP3(X2,X3,a_2_1_lattice3(X1,X0)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 1.83/0.64    inference(resolution,[],[f149,f105])).
% 1.83/0.64  fof(f149,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~sP8(sK13(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0) | sP7(X0,X1,sK13(X2,X3,a_2_1_lattice3(X1,X0))) | sP3(X2,X3,a_2_1_lattice3(X1,X0))) )),
% 1.83/0.64    inference(resolution,[],[f99,f89])).
% 1.83/0.64  fof(f89,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (r2_hidden(sK13(X0,X1,X2),X2) | sP3(X0,X1,X2)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f53])).
% 1.83/0.64  fof(f99,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | sP7(X2,X1,X0) | ~sP8(X0,X1,X2)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f59])).
% 1.83/0.64  fof(f179,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X1,sK13(X0,X1,X3),X2) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~sP6(X1,sK13(X0,X1,X3)) | sP3(X0,X1,X3)) )),
% 1.83/0.64    inference(resolution,[],[f169,f90])).
% 1.83/0.64  fof(f90,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (~r1_lattices(X1,sK13(X0,X1,X2),X0) | sP3(X0,X1,X2)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f53])).
% 1.83/0.64  fof(f169,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (r1_lattices(X2,X3,X0) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~r3_lattice3(X2,X3,X1) | ~sP6(X2,X3)) )),
% 1.83/0.64    inference(resolution,[],[f94,f92])).
% 1.83/0.64  fof(f92,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (sP5(X1,X0,X2) | ~r3_lattice3(X0,X1,X2) | ~sP6(X0,X1)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f54])).
% 1.83/0.64  fof(f54,plain,(
% 1.83/0.64    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP5(X1,X0,X2)) & (sP5(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP6(X0,X1))),
% 1.83/0.64    inference(nnf_transformation,[],[f31])).
% 1.83/0.64  fof(f94,plain,(
% 1.83/0.64    ( ! [X4,X2,X0,X1] : (~sP5(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f58])).
% 1.83/0.64  fof(f58,plain,(
% 1.83/0.64    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | (~r1_lattices(X1,X0,sK14(X0,X1,X2)) & r2_hidden(sK14(X0,X1,X2),X2) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP5(X0,X1,X2)))),
% 1.83/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f56,f57])).
% 1.83/0.64  fof(f57,plain,(
% 1.83/0.64    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK14(X0,X1,X2)) & r2_hidden(sK14(X0,X1,X2),X2) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1))))),
% 1.83/0.64    introduced(choice_axiom,[])).
% 1.83/0.64  fof(f56,plain,(
% 1.83/0.64    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP5(X0,X1,X2)))),
% 1.83/0.64    inference(rectify,[],[f55])).
% 1.83/0.64  fof(f55,plain,(
% 1.83/0.64    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP5(X1,X0,X2)))),
% 1.83/0.64    inference(nnf_transformation,[],[f30])).
% 1.83/0.64  fof(f261,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~r4_lattice3(X2,X0,a_2_1_lattice3(X2,X3)) | ~r2_hidden(X1,a_2_1_lattice3(X2,X3)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | X0 = X1 | ~r2_hidden(X0,a_2_1_lattice3(X2,X3)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X1,X3)) )),
% 1.83/0.64    inference(duplicate_literal_removal,[],[f260])).
% 1.83/0.64  fof(f260,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (X0 = X1 | ~r2_hidden(X1,a_2_1_lattice3(X2,X3)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | ~r4_lattice3(X2,X0,a_2_1_lattice3(X2,X3)) | ~r2_hidden(X0,a_2_1_lattice3(X2,X3)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X1,X3) | ~l3_lattices(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X2))) )),
% 1.83/0.64    inference(resolution,[],[f210,f251])).
% 1.83/0.64  fof(f210,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~r4_lattice3(X0,X3,X1) | X2 = X3 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~r4_lattice3(X0,X2,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.83/0.64    inference(duplicate_literal_removal,[],[f205])).
% 1.83/0.64  fof(f205,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r4_lattice3(X0,X3,X1) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~r4_lattice3(X0,X2,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.83/0.64    inference(superposition,[],[f74,f74])).
% 1.83/0.64  fof(f74,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (k15_lattice3(X0,X2) = X1 | ~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f14])).
% 1.83/0.64  fof(f14,plain,(
% 1.83/0.64    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | ~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.83/0.64    inference(flattening,[],[f13])).
% 1.83/0.64  fof(f13,plain,(
% 1.83/0.64    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | (~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.83/0.64    inference(ennf_transformation,[],[f6])).
% 1.83/0.64  fof(f6,axiom,(
% 1.83/0.64    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 1.83/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattice3)).
% 1.83/0.64  fof(f461,plain,(
% 1.83/0.64    ( ! [X0] : (sK10 != X0 | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11) | ~sP7(sK11,sK9,X0) | ~sP8(X0,sK9,sK11)) )),
% 1.83/0.64    inference(resolution,[],[f460,f100])).
% 1.83/0.64  fof(f460,plain,(
% 1.83/0.64    ( ! [X0] : (~r2_hidden(X0,a_2_1_lattice3(sK9,sK11)) | sK10 != X0 | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f459,f64])).
% 1.83/0.64  fof(f459,plain,(
% 1.83/0.64    ( ! [X0] : (sK10 != X0 | ~r2_hidden(X0,a_2_1_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11) | v2_struct_0(sK9)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f458,f67])).
% 1.83/0.64  fof(f458,plain,(
% 1.83/0.64    ( ! [X0] : (sK10 != X0 | ~r2_hidden(X0,a_2_1_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11) | ~l3_lattices(sK9) | v2_struct_0(sK9)) )),
% 1.83/0.64    inference(duplicate_literal_removal,[],[f457])).
% 1.83/0.64  fof(f457,plain,(
% 1.83/0.64    ( ! [X0] : (sK10 != X0 | ~r2_hidden(X0,a_2_1_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11) | ~l3_lattices(sK9) | v2_struct_0(sK9) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 1.83/0.64    inference(resolution,[],[f451,f251])).
% 1.83/0.64  fof(f451,plain,(
% 1.83/0.64    ( ! [X0] : (~r4_lattice3(sK9,X0,a_2_1_lattice3(sK9,sK11)) | sK10 != X0 | ~r2_hidden(X0,a_2_1_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9))) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f450,f64])).
% 1.83/0.64  fof(f450,plain,(
% 1.83/0.64    ( ! [X0] : (sK10 != X0 | ~r4_lattice3(sK9,X0,a_2_1_lattice3(sK9,sK11)) | ~r2_hidden(X0,a_2_1_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | v2_struct_0(sK9)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f449,f65])).
% 1.83/0.64  fof(f449,plain,(
% 1.83/0.64    ( ! [X0] : (sK10 != X0 | ~r4_lattice3(sK9,X0,a_2_1_lattice3(sK9,sK11)) | ~r2_hidden(X0,a_2_1_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~v10_lattices(sK9) | v2_struct_0(sK9)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f448,f66])).
% 1.83/0.64  fof(f448,plain,(
% 1.83/0.64    ( ! [X0] : (sK10 != X0 | ~r4_lattice3(sK9,X0,a_2_1_lattice3(sK9,sK11)) | ~r2_hidden(X0,a_2_1_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f447,f67])).
% 1.83/0.64  fof(f447,plain,(
% 1.83/0.64    ( ! [X0] : (sK10 != X0 | ~r4_lattice3(sK9,X0,a_2_1_lattice3(sK9,sK11)) | ~r2_hidden(X0,a_2_1_lattice3(sK9,sK11)) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~l3_lattices(sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) )),
% 1.83/0.64    inference(superposition,[],[f443,f74])).
% 1.83/0.64  fof(f443,plain,(
% 1.83/0.64    sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11))),
% 1.83/0.64    inference(subsumption_resolution,[],[f442,f161])).
% 1.83/0.64  fof(f161,plain,(
% 1.83/0.64    sP2(sK10,sK9)),
% 1.83/0.64    inference(subsumption_resolution,[],[f160,f64])).
% 1.83/0.64  fof(f160,plain,(
% 1.83/0.64    sP2(sK10,sK9) | v2_struct_0(sK9)),
% 1.83/0.64    inference(subsumption_resolution,[],[f159,f65])).
% 1.83/0.64  fof(f159,plain,(
% 1.83/0.64    sP2(sK10,sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)),
% 1.83/0.64    inference(subsumption_resolution,[],[f158,f66])).
% 1.83/0.64  fof(f158,plain,(
% 1.83/0.64    sP2(sK10,sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)),
% 1.83/0.64    inference(subsumption_resolution,[],[f153,f67])).
% 1.83/0.64  fof(f153,plain,(
% 1.83/0.64    sP2(sK10,sK9) | ~l3_lattices(sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)),
% 1.83/0.64    inference(resolution,[],[f84,f68])).
% 1.83/0.64  fof(f84,plain,(
% 1.83/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP2(X1,X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f26])).
% 1.83/0.64  fof(f26,plain,(
% 1.83/0.64    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.83/0.64    inference(definition_folding,[],[f16,f25,f24,f23])).
% 1.83/0.64  fof(f23,plain,(
% 1.83/0.64    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 1.83/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.83/0.64  fof(f24,plain,(
% 1.83/0.64    ! [X2,X0,X1] : (sP1(X2,X0,X1) <=> (sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)))),
% 1.83/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.83/0.64  fof(f25,plain,(
% 1.83/0.64    ! [X1,X0] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> sP1(X2,X0,X1)) | ~sP2(X1,X0))),
% 1.83/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.83/0.64  fof(f16,plain,(
% 1.83/0.64    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.83/0.64    inference(flattening,[],[f15])).
% 1.83/0.64  fof(f15,plain,(
% 1.83/0.64    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.83/0.64    inference(ennf_transformation,[],[f4])).
% 1.83/0.64  fof(f4,axiom,(
% 1.83/0.64    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 1.83/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).
% 1.83/0.64  fof(f442,plain,(
% 1.83/0.64    sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)) | ~sP2(sK10,sK9)),
% 1.83/0.64    inference(subsumption_resolution,[],[f441,f70])).
% 1.83/0.64  fof(f441,plain,(
% 1.83/0.64    ~r3_lattice3(sK9,sK10,sK11) | sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)) | ~sP2(sK10,sK9)),
% 1.83/0.64    inference(inner_rewriting,[],[f440])).
% 1.83/0.64  fof(f440,plain,(
% 1.83/0.64    ~r3_lattice3(sK9,k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK11) | sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)) | ~sP2(k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK9)),
% 1.83/0.64    inference(subsumption_resolution,[],[f439,f65])).
% 1.83/0.64  fof(f439,plain,(
% 1.83/0.64    ~v10_lattices(sK9) | ~r3_lattice3(sK9,k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK11) | sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)) | ~sP2(k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK9)),
% 1.83/0.64    inference(subsumption_resolution,[],[f438,f67])).
% 1.83/0.64  fof(f438,plain,(
% 1.83/0.64    ~l3_lattices(sK9) | ~v10_lattices(sK9) | ~r3_lattice3(sK9,k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK11) | sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)) | ~sP2(k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK9)),
% 1.83/0.64    inference(subsumption_resolution,[],[f437,f66])).
% 1.83/0.64  fof(f437,plain,(
% 1.83/0.64    ~v4_lattice3(sK9) | ~l3_lattices(sK9) | ~v10_lattices(sK9) | ~r3_lattice3(sK9,k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK11) | sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)) | ~sP2(k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK9)),
% 1.83/0.64    inference(subsumption_resolution,[],[f417,f64])).
% 1.83/0.64  fof(f417,plain,(
% 1.83/0.64    v2_struct_0(sK9) | ~v4_lattice3(sK9) | ~l3_lattices(sK9) | ~v10_lattices(sK9) | ~r3_lattice3(sK9,k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK11) | sK10 != k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)) | ~sP2(k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)),sK9)),
% 1.83/0.64    inference(resolution,[],[f408,f144])).
% 1.83/0.64  fof(f144,plain,(
% 1.83/0.64    ( ! [X6] : (~sP0(X6,sK9,sK11) | ~r3_lattice3(sK9,X6,sK11) | sK10 != X6 | ~sP2(X6,sK9)) )),
% 1.83/0.64    inference(resolution,[],[f79,f133])).
% 1.83/0.64  fof(f133,plain,(
% 1.83/0.64    ( ! [X0] : (~sP1(sK11,sK9,X0) | sK10 != X0 | ~sP2(X0,sK9)) )),
% 1.83/0.64    inference(superposition,[],[f71,f76])).
% 1.83/0.64  fof(f76,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (k16_lattice3(X1,X2) = X0 | ~sP1(X2,X1,X0) | ~sP2(X0,X1)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f41])).
% 1.83/0.64  fof(f41,plain,(
% 1.83/0.64    ! [X0,X1] : (! [X2] : ((k16_lattice3(X1,X2) = X0 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k16_lattice3(X1,X2) != X0)) | ~sP2(X0,X1))),
% 1.83/0.64    inference(rectify,[],[f40])).
% 1.83/0.64  fof(f40,plain,(
% 1.83/0.64    ! [X1,X0] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ~sP1(X2,X0,X1)) & (sP1(X2,X0,X1) | k16_lattice3(X0,X2) != X1)) | ~sP2(X1,X0))),
% 1.83/0.64    inference(nnf_transformation,[],[f25])).
% 1.83/0.64  fof(f71,plain,(
% 1.83/0.64    sK10 != k16_lattice3(sK9,sK11)),
% 1.83/0.64    inference(cnf_transformation,[],[f39])).
% 1.83/0.64  fof(f79,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f44])).
% 1.83/0.64  fof(f44,plain,(
% 1.83/0.64    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) & ((sP0(X2,X1,X0) & r3_lattice3(X1,X2,X0)) | ~sP1(X0,X1,X2)))),
% 1.83/0.64    inference(rectify,[],[f43])).
% 1.83/0.64  fof(f43,plain,(
% 1.83/0.64    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | ~sP0(X1,X0,X2) | ~r3_lattice3(X0,X1,X2)) & ((sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP1(X2,X0,X1)))),
% 1.83/0.64    inference(flattening,[],[f42])).
% 1.83/0.64  fof(f42,plain,(
% 1.83/0.64    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | (~sP0(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) & ((sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP1(X2,X0,X1)))),
% 1.83/0.64    inference(nnf_transformation,[],[f24])).
% 1.83/0.64  fof(f408,plain,(
% 1.83/0.64    ( ! [X0,X1] : (sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1) | v2_struct_0(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~v10_lattices(X0)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f407,f81])).
% 1.83/0.64  fof(f81,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f48])).
% 1.83/0.64  fof(f48,plain,(
% 1.83/0.64    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r3_lattices(X1,sK12(X0,X1,X2),X0) & r3_lattice3(X1,sK12(X0,X1,X2),X2) & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 1.83/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f46,f47])).
% 1.83/0.64  fof(f47,plain,(
% 1.83/0.64    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r3_lattices(X1,sK12(X0,X1,X2),X0) & r3_lattice3(X1,sK12(X0,X1,X2),X2) & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))))),
% 1.83/0.64    introduced(choice_axiom,[])).
% 1.83/0.64  fof(f46,plain,(
% 1.83/0.64    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 1.83/0.64    inference(rectify,[],[f45])).
% 1.83/0.64  fof(f45,plain,(
% 1.83/0.64    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 1.83/0.64    inference(nnf_transformation,[],[f23])).
% 1.83/0.64  fof(f407,plain,(
% 1.83/0.64    ( ! [X0,X1] : (v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | ~m1_subset_1(sK12(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1),u1_struct_0(X0))) )),
% 1.83/0.64    inference(duplicate_literal_removal,[],[f404])).
% 1.83/0.64  fof(f404,plain,(
% 1.83/0.64    ( ! [X0,X1] : (v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~m1_subset_1(sK12(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1),u1_struct_0(X0)) | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1)) )),
% 1.83/0.64    inference(resolution,[],[f309,f82])).
% 1.83/0.64  fof(f82,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK12(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f48])).
% 1.83/0.64  fof(f309,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X1,sK12(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3),X2) | v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~l3_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X0) | ~m1_subset_1(sK12(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3),u1_struct_0(X1))) )),
% 1.83/0.64    inference(resolution,[],[f306,f107])).
% 1.83/0.64  fof(f306,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~sP7(X2,X1,sK12(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3)) | ~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 1.83/0.64    inference(resolution,[],[f204,f105])).
% 1.83/0.64  fof(f204,plain,(
% 1.83/0.64    ( ! [X2,X0,X3,X1] : (~sP8(sK12(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3),X1,X2) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3) | ~sP7(X2,X1,sK12(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3)) | ~l3_lattices(X0)) )),
% 1.83/0.64    inference(resolution,[],[f178,f100])).
% 1.83/0.64  fof(f178,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (~r2_hidden(sK12(k15_lattice3(X0,X1),X0,X2),X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,X1),X0,X2)) )),
% 1.83/0.64    inference(subsumption_resolution,[],[f177,f81])).
% 1.83/0.64  fof(f177,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (~r2_hidden(sK12(k15_lattice3(X0,X1),X0,X2),X1) | ~m1_subset_1(sK12(k15_lattice3(X0,X1),X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,X1),X0,X2)) )),
% 1.83/0.64    inference(resolution,[],[f72,f83])).
% 1.83/0.64  fof(f83,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (~r3_lattices(X1,sK12(X0,X1,X2),X0) | sP0(X0,X1,X2)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f48])).
% 1.83/0.64  fof(f72,plain,(
% 1.83/0.64    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k15_lattice3(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.83/0.64    inference(cnf_transformation,[],[f12])).
% 1.83/0.64  fof(f12,plain,(
% 1.83/0.64    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.83/0.64    inference(flattening,[],[f11])).
% 1.83/0.64  fof(f11,plain,(
% 1.83/0.64    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.83/0.64    inference(ennf_transformation,[],[f5])).
% 1.83/0.64  fof(f5,axiom,(
% 1.83/0.64    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.83/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).
% 1.83/0.64  % SZS output end Proof for theBenchmark
% 1.83/0.64  % (23935)------------------------------
% 1.83/0.64  % (23935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.64  % (23935)Termination reason: Refutation
% 1.83/0.64  
% 1.83/0.64  % (23935)Memory used [KB]: 6396
% 1.83/0.64  % (23935)Time elapsed: 0.211 s
% 1.83/0.64  % (23935)------------------------------
% 1.83/0.64  % (23935)------------------------------
% 1.83/0.65  % (23930)Success in time 0.282 s
%------------------------------------------------------------------------------
