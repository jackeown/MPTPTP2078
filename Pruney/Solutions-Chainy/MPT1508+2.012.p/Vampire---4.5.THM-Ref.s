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
% DateTime   : Thu Dec  3 13:15:44 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 712 expanded)
%              Number of leaves         :   17 ( 254 expanded)
%              Depth                    :   53
%              Number of atoms          :  788 (5212 expanded)
%              Number of equality atoms :  153 ( 930 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f356,plain,(
    $false ),
    inference(subsumption_resolution,[],[f352,f57])).

fof(f57,plain,(
    sK4 != k16_lattice3(sK3,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK4 != k16_lattice3(sK3,sK5)
    & r3_lattice3(sK3,sK4,sK5)
    & r2_hidden(sK4,sK5)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l3_lattices(sK3)
    & v4_lattice3(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f10,f28,f27,f26])).

fof(f26,plain,
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
              ( k16_lattice3(sK3,X2) != X1
              & r3_lattice3(sK3,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l3_lattices(sK3)
      & v4_lattice3(sK3)
      & v10_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k16_lattice3(sK3,X2) != X1
            & r3_lattice3(sK3,X1,X2)
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK3)) )
   => ( ? [X2] :
          ( k16_lattice3(sK3,X2) != sK4
          & r3_lattice3(sK3,sK4,X2)
          & r2_hidden(sK4,X2) )
      & m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( k16_lattice3(sK3,X2) != sK4
        & r3_lattice3(sK3,sK4,X2)
        & r2_hidden(sK4,X2) )
   => ( sK4 != k16_lattice3(sK3,sK5)
      & r3_lattice3(sK3,sK4,sK5)
      & r2_hidden(sK4,sK5) ) ),
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

% (23240)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).

fof(f352,plain,(
    sK4 = k16_lattice3(sK3,sK5) ),
    inference(resolution,[],[f351,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ sP0(sK4,sK3,X0)
      | sK4 = k16_lattice3(sK3,X0) ) ),
    inference(resolution,[],[f101,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0,X2)
      | k16_lattice3(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k16_lattice3(X0,X2) = X1
            | ~ sP0(X1,X0,X2) )
          & ( sP0(X1,X0,X2)
            | k16_lattice3(X0,X2) != X1 ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k16_lattice3(X0,X2) = X1
        <=> sP0(X1,X0,X2) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f101,plain,(
    sP1(sK3,sK4) ),
    inference(resolution,[],[f100,f54])).

fof(f54,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f99,f50])).

fof(f50,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f99,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP1(sK3,X0)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f98,f51])).

fof(f51,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP1(sK3,X0)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f97,f53])).

fof(f53,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | sP1(sK3,X0)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f68,f52])).

fof(f52,plain,(
    v4_lattice3(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | sP1(X0,X1)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f22,f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ( ! [X3] :
            ( r3_lattices(X0,X3,X1)
            | ~ r3_lattice3(X0,X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & r3_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(f351,plain,(
    sP0(sK4,sK3,sK5) ),
    inference(subsumption_resolution,[],[f350,f56])).

fof(f56,plain,(
    r3_lattice3(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f350,plain,
    ( sP0(sK4,sK3,sK5)
    | ~ r3_lattice3(sK3,sK4,sK5) ),
    inference(resolution,[],[f339,f92])).

fof(f92,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f87,f88])).

fof(f88,plain,(
    ! [X0,X1] : sP2(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP2(X1,X0,X2) )
      & ( sP2(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP2(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f87,plain,(
    ! [X4,X2,X0] :
      ( ~ sP2(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ( sK9(X0,X1,X2) != X0
              & sK9(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( sK9(X0,X1,X2) = X0
            | sK9(X0,X1,X2) = X1
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK9(X0,X1,X2) != X0
            & sK9(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( sK9(X0,X1,X2) = X0
          | sK9(X0,X1,X2) = X1
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f339,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK4,sK3,X0),k2_tarski(sK6(sK4,sK3,sK5),sK4))
      | sP0(sK4,sK3,X0)
      | ~ r3_lattice3(sK3,sK4,X0) ) ),
    inference(superposition,[],[f124,f338])).

fof(f338,plain,(
    sK4 = k15_lattice3(sK3,k2_tarski(sK6(sK4,sK3,sK5),sK4)) ),
    inference(subsumption_resolution,[],[f334,f57])).

fof(f334,plain,
    ( sK4 = k15_lattice3(sK3,k2_tarski(sK6(sK4,sK3,sK5),sK4))
    | sK4 = k16_lattice3(sK3,sK5) ),
    inference(resolution,[],[f331,f103])).

fof(f331,plain,
    ( sP0(sK4,sK3,sK5)
    | sK4 = k15_lattice3(sK3,k2_tarski(sK6(sK4,sK3,sK5),sK4)) ),
    inference(resolution,[],[f328,f56])).

fof(f328,plain,(
    ! [X0] :
      ( ~ r3_lattice3(sK3,X0,sK5)
      | sP0(X0,sK3,sK5)
      | sK4 = k15_lattice3(sK3,k2_tarski(sK6(X0,sK3,sK5),sK4)) ) ),
    inference(resolution,[],[f294,f55])).

fof(f55,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f294,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4,X1)
      | sK4 = k15_lattice3(sK3,k2_tarski(sK6(X0,sK3,X1),sK4))
      | sP0(X0,sK3,X1)
      | ~ r3_lattice3(sK3,X0,X1) ) ),
    inference(subsumption_resolution,[],[f293,f54])).

fof(f293,plain,(
    ! [X0,X1] :
      ( sK4 = k15_lattice3(sK3,k2_tarski(sK6(X0,sK3,X1),sK4))
      | ~ r2_hidden(sK4,X1)
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | sP0(X0,sK3,X1)
      | ~ r3_lattice3(sK3,X0,X1) ) ),
    inference(resolution,[],[f291,f131])).

fof(f131,plain,(
    ! [X2,X3,X1] :
      ( r1_lattices(sK3,sK6(X3,sK3,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | sP0(X3,sK3,X2)
      | ~ r3_lattice3(sK3,X3,X2) ) ),
    inference(subsumption_resolution,[],[f129,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2)
      | ~ r3_lattice3(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r3_lattices(X1,sK6(X0,X1,X2),X0)
          & r3_lattice3(X1,sK6(X0,X1,X2),X2)
          & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) )
        | ~ r3_lattice3(X1,X0,X2) )
      & ( ( ! [X4] :
              ( r3_lattices(X1,X4,X0)
              | ~ r3_lattice3(X1,X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r3_lattice3(X1,X0,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X1,X3,X0)
          & r3_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r3_lattices(X1,sK6(X0,X1,X2),X0)
        & r3_lattice3(X1,sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r3_lattices(X1,X3,X0)
            & r3_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ r3_lattice3(X1,X0,X2) )
      & ( ( ! [X4] :
              ( r3_lattices(X1,X4,X0)
              | ~ r3_lattice3(X1,X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r3_lattice3(X1,X0,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f129,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(sK6(X3,sK3,X2),u1_struct_0(sK3))
      | r1_lattices(sK3,sK6(X3,sK3,X2),X1)
      | sP0(X3,sK3,X2)
      | ~ r3_lattice3(sK3,X3,X2) ) ),
    inference(resolution,[],[f127,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK6(X0,X1,X2),X2)
      | sP0(X0,X1,X2)
      | ~ r3_lattice3(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattice3(sK3,X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | r1_lattices(sK3,X2,X0) ) ),
    inference(subsumption_resolution,[],[f126,f50])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ r3_lattice3(sK3,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | r1_lattices(sK3,X2,X0)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f73,f53])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattices(X0,X1,X4)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK8(X0,X1,X2))
                  & r2_hidden(sK8(X0,X1,X2),X2)
                  & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f20])).

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

fof(f291,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK3,X0,sK4)
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) ) ),
    inference(subsumption_resolution,[],[f290,f50])).

fof(f290,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK3,X0,sK4)
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f289,f51])).

fof(f289,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK3,X0,sK4)
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f288,f52])).

fof(f288,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK3,X0,sK4)
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f287,f53])).

fof(f287,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK3,X0,sK4)
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | ~ l3_lattices(sK3)
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f286,f54])).

fof(f286,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK3,X0,sK4)
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f285,f91])).

fof(f91,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(resolution,[],[f86,f88])).

fof(f86,plain,(
    ! [X4,X2,X1] :
      ( ~ sP2(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f285,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK3,X0,sK4)
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | ~ r2_hidden(sK4,k2_tarski(X0,sK4))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK3,X0,sK4)
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | ~ r2_hidden(sK4,k2_tarski(X0,sK4))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f263,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_lattice3(X0,X1,X2)
      | k15_lattice3(X0,X2) = X1
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).

fof(f263,plain,(
    ! [X7] :
      ( r4_lattice3(sK3,sK4,k2_tarski(X7,sK4))
      | ~ r1_lattices(sK3,X7,sK4)
      | sK4 = k15_lattice3(sK3,k2_tarski(X7,sK4)) ) ),
    inference(subsumption_resolution,[],[f262,f50])).

fof(f262,plain,(
    ! [X7] :
      ( ~ r1_lattices(sK3,X7,sK4)
      | r4_lattice3(sK3,sK4,k2_tarski(X7,sK4))
      | v2_struct_0(sK3)
      | sK4 = k15_lattice3(sK3,k2_tarski(X7,sK4)) ) ),
    inference(subsumption_resolution,[],[f261,f53])).

fof(f261,plain,(
    ! [X7] :
      ( ~ r1_lattices(sK3,X7,sK4)
      | r4_lattice3(sK3,sK4,k2_tarski(X7,sK4))
      | ~ l3_lattices(sK3)
      | v2_struct_0(sK3)
      | sK4 = k15_lattice3(sK3,k2_tarski(X7,sK4)) ) ),
    inference(subsumption_resolution,[],[f255,f54])).

fof(f255,plain,(
    ! [X7] :
      ( ~ r1_lattices(sK3,X7,sK4)
      | r4_lattice3(sK3,sK4,k2_tarski(X7,sK4))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | v2_struct_0(sK3)
      | sK4 = k15_lattice3(sK3,k2_tarski(X7,sK4)) ) ),
    inference(superposition,[],[f72,f248])).

fof(f248,plain,(
    ! [X0] :
      ( sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) ) ),
    inference(subsumption_resolution,[],[f247,f50])).

fof(f247,plain,(
    ! [X0] :
      ( sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f246,f51])).

fof(f246,plain,(
    ! [X0] :
      ( sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f245,f52])).

fof(f245,plain,(
    ! [X0] :
      ( sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f244,f53])).

fof(f244,plain,(
    ! [X0] :
      ( sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | ~ l3_lattices(sK3)
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f243,f54])).

fof(f243,plain,(
    ! [X0] :
      ( sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f242,f91])).

fof(f242,plain,(
    ! [X0] :
      ( sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | ~ r2_hidden(sK4,k2_tarski(X0,sK4))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,(
    ! [X0] :
      ( sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))
      | ~ r2_hidden(sK4,k2_tarski(X0,sK4))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f194,f60])).

fof(f194,plain,(
    ! [X5] :
      ( r4_lattice3(sK3,sK4,k2_tarski(X5,sK4))
      | sK7(sK3,sK4,k2_tarski(X5,sK4)) = X5
      | sK4 = k15_lattice3(sK3,k2_tarski(X5,sK4)) ) ),
    inference(subsumption_resolution,[],[f193,f50])).

fof(f193,plain,(
    ! [X5] :
      ( r4_lattice3(sK3,sK4,k2_tarski(X5,sK4))
      | v2_struct_0(sK3)
      | sK7(sK3,sK4,k2_tarski(X5,sK4)) = X5
      | sK4 = k15_lattice3(sK3,k2_tarski(X5,sK4)) ) ),
    inference(subsumption_resolution,[],[f192,f53])).

fof(f192,plain,(
    ! [X5] :
      ( r4_lattice3(sK3,sK4,k2_tarski(X5,sK4))
      | ~ l3_lattices(sK3)
      | v2_struct_0(sK3)
      | sK7(sK3,sK4,k2_tarski(X5,sK4)) = X5
      | sK4 = k15_lattice3(sK3,k2_tarski(X5,sK4)) ) ),
    inference(subsumption_resolution,[],[f191,f54])).

fof(f191,plain,(
    ! [X5] :
      ( r4_lattice3(sK3,sK4,k2_tarski(X5,sK4))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | v2_struct_0(sK3)
      | sK7(sK3,sK4,k2_tarski(X5,sK4)) = X5
      | sK4 = k15_lattice3(sK3,k2_tarski(X5,sK4)) ) ),
    inference(subsumption_resolution,[],[f181,f136])).

fof(f136,plain,(
    r1_lattices(sK3,sK4,sK4) ),
    inference(subsumption_resolution,[],[f132,f55])).

fof(f132,plain,
    ( ~ r2_hidden(sK4,sK5)
    | r1_lattices(sK3,sK4,sK4) ),
    inference(resolution,[],[f130,f54])).

fof(f130,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ r2_hidden(X0,sK5)
      | r1_lattices(sK3,sK4,X0) ) ),
    inference(subsumption_resolution,[],[f128,f54])).

fof(f128,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ r2_hidden(X0,sK5)
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | r1_lattices(sK3,sK4,X0) ) ),
    inference(resolution,[],[f127,f56])).

fof(f181,plain,(
    ! [X5] :
      ( ~ r1_lattices(sK3,sK4,sK4)
      | r4_lattice3(sK3,sK4,k2_tarski(X5,sK4))
      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | v2_struct_0(sK3)
      | sK7(sK3,sK4,k2_tarski(X5,sK4)) = X5
      | sK4 = k15_lattice3(sK3,k2_tarski(X5,sK4)) ) ),
    inference(superposition,[],[f72,f173])).

fof(f173,plain,(
    ! [X0] :
      ( sK4 = sK7(sK3,sK4,k2_tarski(X0,sK4))
      | sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) ) ),
    inference(resolution,[],[f165,f91])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4,k2_tarski(X0,X1))
      | sK7(sK3,sK4,k2_tarski(X0,X1)) = X1
      | sK4 = k15_lattice3(sK3,k2_tarski(X0,X1))
      | sK7(sK3,sK4,k2_tarski(X0,X1)) = X0 ) ),
    inference(resolution,[],[f159,f54])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sK7(sK3,X0,k2_tarski(X1,X2)) = X1
      | sK7(sK3,X0,k2_tarski(X1,X2)) = X2
      | k15_lattice3(sK3,k2_tarski(X1,X2)) = X0
      | ~ r2_hidden(X0,k2_tarski(X1,X2)) ) ),
    inference(subsumption_resolution,[],[f158,f50])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sK7(sK3,X0,k2_tarski(X1,X2)) = X1
      | sK7(sK3,X0,k2_tarski(X1,X2)) = X2
      | k15_lattice3(sK3,k2_tarski(X1,X2)) = X0
      | ~ r2_hidden(X0,k2_tarski(X1,X2))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f157,f51])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sK7(sK3,X0,k2_tarski(X1,X2)) = X1
      | sK7(sK3,X0,k2_tarski(X1,X2)) = X2
      | k15_lattice3(sK3,k2_tarski(X1,X2)) = X0
      | ~ r2_hidden(X0,k2_tarski(X1,X2))
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f156,f52])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sK7(sK3,X0,k2_tarski(X1,X2)) = X1
      | sK7(sK3,X0,k2_tarski(X1,X2)) = X2
      | k15_lattice3(sK3,k2_tarski(X1,X2)) = X0
      | ~ r2_hidden(X0,k2_tarski(X1,X2))
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f155,f53])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sK7(sK3,X0,k2_tarski(X1,X2)) = X1
      | sK7(sK3,X0,k2_tarski(X1,X2)) = X2
      | k15_lattice3(sK3,k2_tarski(X1,X2)) = X0
      | ~ r2_hidden(X0,k2_tarski(X1,X2))
      | ~ l3_lattices(sK3)
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sK7(sK3,X0,k2_tarski(X1,X2)) = X1
      | sK7(sK3,X0,k2_tarski(X1,X2)) = X2
      | k15_lattice3(sK3,k2_tarski(X1,X2)) = X0
      | ~ r2_hidden(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | ~ v4_lattice3(sK3)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f107,f60])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(sK3,X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sK7(sK3,X0,k2_tarski(X1,X2)) = X1
      | sK7(sK3,X0,k2_tarski(X1,X2)) = X2 ) ),
    inference(resolution,[],[f106,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f77,f88])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(sK3,X0,X1),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r4_lattice3(sK3,X0,X1) ) ),
    inference(subsumption_resolution,[],[f105,f50])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(sK3,X0,X1),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r4_lattice3(sK3,X0,X1)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f71,f53])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r4_lattice3(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK7(X0,X1,X2),X1)
                  & r2_hidden(sK7(X0,X1,X2),X2)
                  & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK7(X0,X1,X2),X1)
        & r2_hidden(sK7(X0,X1,X2),X2)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f18])).

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

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,sK7(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(sK3,k15_lattice3(sK3,X0),X1)
      | sP0(k15_lattice3(sK3,X0),sK3,X1)
      | ~ r2_hidden(sK6(k15_lattice3(sK3,X0),sK3,X1),X0) ) ),
    inference(subsumption_resolution,[],[f123,f65])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(k15_lattice3(sK3,X0),sK3,X1),u1_struct_0(sK3))
      | ~ r2_hidden(sK6(k15_lattice3(sK3,X0),sK3,X1),X0)
      | sP0(k15_lattice3(sK3,X0),sK3,X1)
      | ~ r3_lattice3(sK3,k15_lattice3(sK3,X0),X1) ) ),
    inference(resolution,[],[f122,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X1,sK6(X0,X1,X2),X0)
      | sP0(X0,X1,X2)
      | ~ r3_lattice3(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK3,X0,k15_lattice3(sK3,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f121,f50])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r3_lattices(sK3,X0,k15_lattice3(sK3,X1))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f120,f51])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r3_lattices(sK3,X0,k15_lattice3(sK3,X1))
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f119,f53])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | r3_lattices(sK3,X0,k15_lattice3(sK3,X1))
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f58,f52])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,k15_lattice3(X0,X2))
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:35:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.47  % (23229)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (23236)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.47  % (23235)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.48  % (23217)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.48  % (23237)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.48  % (23219)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (23215)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.48  % (23215)Refutation not found, incomplete strategy% (23215)------------------------------
% 0.20/0.48  % (23215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23215)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (23215)Memory used [KB]: 10490
% 0.20/0.49  % (23215)Time elapsed: 0.094 s
% 0.20/0.49  % (23215)------------------------------
% 0.20/0.49  % (23215)------------------------------
% 0.20/0.49  % (23223)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.49  % (23218)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (23231)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.49  % (23226)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.49  % (23226)Refutation not found, incomplete strategy% (23226)------------------------------
% 0.20/0.49  % (23226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23226)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (23226)Memory used [KB]: 10490
% 0.20/0.49  % (23226)Time elapsed: 0.098 s
% 0.20/0.49  % (23226)------------------------------
% 0.20/0.49  % (23226)------------------------------
% 0.20/0.49  % (23221)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (23216)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (23238)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.50  % (23239)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.50  % (23224)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (23230)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (23220)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (23232)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.30/0.51  % (23222)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.30/0.51  % (23228)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.30/0.51  % (23228)Refutation not found, incomplete strategy% (23228)------------------------------
% 1.30/0.51  % (23228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.51  % (23228)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.51  
% 1.30/0.51  % (23228)Memory used [KB]: 6140
% 1.30/0.51  % (23228)Time elapsed: 0.120 s
% 1.30/0.51  % (23228)------------------------------
% 1.30/0.51  % (23228)------------------------------
% 1.30/0.51  % (23222)Refutation not found, incomplete strategy% (23222)------------------------------
% 1.30/0.51  % (23222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.51  % (23222)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.51  
% 1.30/0.51  % (23222)Memory used [KB]: 1663
% 1.30/0.51  % (23222)Time elapsed: 0.083 s
% 1.30/0.51  % (23222)------------------------------
% 1.30/0.51  % (23222)------------------------------
% 1.30/0.51  % (23227)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.30/0.51  % (23225)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.30/0.52  % (23234)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.30/0.52  % (23233)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.30/0.53  % (23218)Refutation found. Thanks to Tanya!
% 1.30/0.53  % SZS status Theorem for theBenchmark
% 1.30/0.53  % SZS output start Proof for theBenchmark
% 1.30/0.53  fof(f356,plain,(
% 1.30/0.53    $false),
% 1.30/0.53    inference(subsumption_resolution,[],[f352,f57])).
% 1.30/0.53  fof(f57,plain,(
% 1.30/0.53    sK4 != k16_lattice3(sK3,sK5)),
% 1.30/0.53    inference(cnf_transformation,[],[f29])).
% 1.30/0.53  fof(f29,plain,(
% 1.30/0.53    ((sK4 != k16_lattice3(sK3,sK5) & r3_lattice3(sK3,sK4,sK5) & r2_hidden(sK4,sK5)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3)),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f10,f28,f27,f26])).
% 1.30/0.53  fof(f26,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK3,X2) != X1 & r3_lattice3(sK3,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK3))) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f27,plain,(
% 1.30/0.53    ? [X1] : (? [X2] : (k16_lattice3(sK3,X2) != X1 & r3_lattice3(sK3,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK3))) => (? [X2] : (k16_lattice3(sK3,X2) != sK4 & r3_lattice3(sK3,sK4,X2) & r2_hidden(sK4,X2)) & m1_subset_1(sK4,u1_struct_0(sK3)))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f28,plain,(
% 1.30/0.53    ? [X2] : (k16_lattice3(sK3,X2) != sK4 & r3_lattice3(sK3,sK4,X2) & r2_hidden(sK4,X2)) => (sK4 != k16_lattice3(sK3,sK5) & r3_lattice3(sK3,sK4,sK5) & r2_hidden(sK4,sK5))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f10,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.30/0.53    inference(flattening,[],[f9])).
% 1.30/0.53  fof(f9,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.30/0.53    inference(ennf_transformation,[],[f8])).
% 1.30/0.53  % (23240)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.30/0.53  fof(f8,negated_conjecture,(
% 1.30/0.53    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 1.30/0.53    inference(negated_conjecture,[],[f7])).
% 1.30/0.53  fof(f7,conjecture,(
% 1.30/0.53    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).
% 1.30/0.53  fof(f352,plain,(
% 1.30/0.53    sK4 = k16_lattice3(sK3,sK5)),
% 1.30/0.53    inference(resolution,[],[f351,f103])).
% 1.30/0.53  fof(f103,plain,(
% 1.30/0.53    ( ! [X0] : (~sP0(sK4,sK3,X0) | sK4 = k16_lattice3(sK3,X0)) )),
% 1.30/0.53    inference(resolution,[],[f101,f62])).
% 1.30/0.53  fof(f62,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0,X2) | k16_lattice3(X0,X2) = X1) )),
% 1.30/0.53    inference(cnf_transformation,[],[f30])).
% 1.30/0.53  fof(f30,plain,(
% 1.30/0.53    ! [X0,X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k16_lattice3(X0,X2) != X1)) | ~sP1(X0,X1))),
% 1.30/0.53    inference(nnf_transformation,[],[f22])).
% 1.30/0.53  fof(f22,plain,(
% 1.30/0.53    ! [X0,X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> sP0(X1,X0,X2)) | ~sP1(X0,X1))),
% 1.30/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.30/0.53  fof(f101,plain,(
% 1.30/0.53    sP1(sK3,sK4)),
% 1.30/0.53    inference(resolution,[],[f100,f54])).
% 1.30/0.53  fof(f54,plain,(
% 1.30/0.53    m1_subset_1(sK4,u1_struct_0(sK3))),
% 1.30/0.53    inference(cnf_transformation,[],[f29])).
% 1.30/0.53  fof(f100,plain,(
% 1.30/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | sP1(sK3,X0)) )),
% 1.30/0.53    inference(subsumption_resolution,[],[f99,f50])).
% 1.30/0.53  fof(f50,plain,(
% 1.30/0.53    ~v2_struct_0(sK3)),
% 1.30/0.53    inference(cnf_transformation,[],[f29])).
% 1.30/0.53  fof(f99,plain,(
% 1.30/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | sP1(sK3,X0) | v2_struct_0(sK3)) )),
% 1.30/0.53    inference(subsumption_resolution,[],[f98,f51])).
% 1.30/0.53  fof(f51,plain,(
% 1.30/0.53    v10_lattices(sK3)),
% 1.30/0.53    inference(cnf_transformation,[],[f29])).
% 1.30/0.53  fof(f98,plain,(
% 1.30/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | sP1(sK3,X0) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.30/0.53    inference(subsumption_resolution,[],[f97,f53])).
% 1.30/0.53  fof(f53,plain,(
% 1.30/0.53    l3_lattices(sK3)),
% 1.30/0.53    inference(cnf_transformation,[],[f29])).
% 1.30/0.53  fof(f97,plain,(
% 1.30/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~l3_lattices(sK3) | sP1(sK3,X0) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.30/0.53    inference(resolution,[],[f68,f52])).
% 1.30/0.53  fof(f52,plain,(
% 1.30/0.53    v4_lattice3(sK3)),
% 1.30/0.53    inference(cnf_transformation,[],[f29])).
% 1.30/0.53  fof(f68,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~v4_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | sP1(X0,X1) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f23])).
% 1.30/0.53  fof(f23,plain,(
% 1.30/0.53    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.30/0.53    inference(definition_folding,[],[f16,f22,f21])).
% 1.30/0.53  fof(f21,plain,(
% 1.30/0.53    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)))),
% 1.30/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.30/0.53  fof(f16,plain,(
% 1.30/0.53    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.30/0.53    inference(flattening,[],[f15])).
% 1.30/0.53  fof(f15,plain,(
% 1.30/0.53    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.30/0.53    inference(ennf_transformation,[],[f4])).
% 1.30/0.53  fof(f4,axiom,(
% 1.30/0.53    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 1.30/0.53  fof(f351,plain,(
% 1.30/0.53    sP0(sK4,sK3,sK5)),
% 1.30/0.53    inference(subsumption_resolution,[],[f350,f56])).
% 1.30/0.53  fof(f56,plain,(
% 1.30/0.53    r3_lattice3(sK3,sK4,sK5)),
% 1.30/0.53    inference(cnf_transformation,[],[f29])).
% 1.30/0.53  fof(f350,plain,(
% 1.30/0.53    sP0(sK4,sK3,sK5) | ~r3_lattice3(sK3,sK4,sK5)),
% 1.30/0.53    inference(resolution,[],[f339,f92])).
% 1.30/0.53  fof(f92,plain,(
% 1.30/0.53    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.30/0.53    inference(resolution,[],[f87,f88])).
% 1.30/0.53  fof(f88,plain,(
% 1.30/0.53    ( ! [X0,X1] : (sP2(X1,X0,k2_tarski(X0,X1))) )),
% 1.30/0.53    inference(equality_resolution,[],[f83])).
% 1.30/0.53  fof(f83,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.30/0.53    inference(cnf_transformation,[],[f49])).
% 1.30/0.53  fof(f49,plain,(
% 1.30/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.30/0.53    inference(nnf_transformation,[],[f25])).
% 1.30/0.53  fof(f25,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP2(X1,X0,X2))),
% 1.30/0.53    inference(definition_folding,[],[f1,f24])).
% 1.30/0.53  fof(f24,plain,(
% 1.30/0.53    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.30/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.30/0.53  fof(f1,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.30/0.53  fof(f87,plain,(
% 1.30/0.53    ( ! [X4,X2,X0] : (~sP2(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.30/0.53    inference(equality_resolution,[],[f78])).
% 1.30/0.53  fof(f78,plain,(
% 1.30/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP2(X0,X1,X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f48])).
% 1.30/0.53  fof(f48,plain,(
% 1.30/0.53    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (((sK9(X0,X1,X2) != X0 & sK9(X0,X1,X2) != X1) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sK9(X0,X1,X2) = X0 | sK9(X0,X1,X2) = X1 | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f46,f47])).
% 1.30/0.53  fof(f47,plain,(
% 1.30/0.53    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK9(X0,X1,X2) != X0 & sK9(X0,X1,X2) != X1) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sK9(X0,X1,X2) = X0 | sK9(X0,X1,X2) = X1 | r2_hidden(sK9(X0,X1,X2),X2))))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f46,plain,(
% 1.30/0.53    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.30/0.53    inference(rectify,[],[f45])).
% 1.30/0.53  fof(f45,plain,(
% 1.30/0.53    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 1.30/0.53    inference(flattening,[],[f44])).
% 1.30/0.53  fof(f44,plain,(
% 1.30/0.53    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 1.30/0.53    inference(nnf_transformation,[],[f24])).
% 1.30/0.53  fof(f339,plain,(
% 1.30/0.53    ( ! [X0] : (~r2_hidden(sK6(sK4,sK3,X0),k2_tarski(sK6(sK4,sK3,sK5),sK4)) | sP0(sK4,sK3,X0) | ~r3_lattice3(sK3,sK4,X0)) )),
% 1.30/0.53    inference(superposition,[],[f124,f338])).
% 1.30/0.53  fof(f338,plain,(
% 1.30/0.53    sK4 = k15_lattice3(sK3,k2_tarski(sK6(sK4,sK3,sK5),sK4))),
% 1.30/0.53    inference(subsumption_resolution,[],[f334,f57])).
% 1.30/0.53  fof(f334,plain,(
% 1.30/0.53    sK4 = k15_lattice3(sK3,k2_tarski(sK6(sK4,sK3,sK5),sK4)) | sK4 = k16_lattice3(sK3,sK5)),
% 1.30/0.53    inference(resolution,[],[f331,f103])).
% 1.30/0.53  fof(f331,plain,(
% 1.30/0.53    sP0(sK4,sK3,sK5) | sK4 = k15_lattice3(sK3,k2_tarski(sK6(sK4,sK3,sK5),sK4))),
% 1.30/0.53    inference(resolution,[],[f328,f56])).
% 1.30/0.53  fof(f328,plain,(
% 1.30/0.53    ( ! [X0] : (~r3_lattice3(sK3,X0,sK5) | sP0(X0,sK3,sK5) | sK4 = k15_lattice3(sK3,k2_tarski(sK6(X0,sK3,sK5),sK4))) )),
% 1.30/0.53    inference(resolution,[],[f294,f55])).
% 1.30/0.53  fof(f55,plain,(
% 1.30/0.53    r2_hidden(sK4,sK5)),
% 1.30/0.53    inference(cnf_transformation,[],[f29])).
% 1.30/0.53  fof(f294,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~r2_hidden(sK4,X1) | sK4 = k15_lattice3(sK3,k2_tarski(sK6(X0,sK3,X1),sK4)) | sP0(X0,sK3,X1) | ~r3_lattice3(sK3,X0,X1)) )),
% 1.30/0.53    inference(subsumption_resolution,[],[f293,f54])).
% 1.30/0.53  fof(f293,plain,(
% 1.30/0.53    ( ! [X0,X1] : (sK4 = k15_lattice3(sK3,k2_tarski(sK6(X0,sK3,X1),sK4)) | ~r2_hidden(sK4,X1) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | sP0(X0,sK3,X1) | ~r3_lattice3(sK3,X0,X1)) )),
% 1.30/0.53    inference(resolution,[],[f291,f131])).
% 1.30/0.53  fof(f131,plain,(
% 1.30/0.53    ( ! [X2,X3,X1] : (r1_lattices(sK3,sK6(X3,sK3,X2),X1) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK3)) | sP0(X3,sK3,X2) | ~r3_lattice3(sK3,X3,X2)) )),
% 1.30/0.53    inference(subsumption_resolution,[],[f129,f65])).
% 1.30/0.53  fof(f65,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2) | ~r3_lattice3(X1,X0,X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f35])).
% 1.30/0.53  fof(f35,plain,(
% 1.30/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r3_lattices(X1,sK6(X0,X1,X2),X0) & r3_lattice3(X1,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))) | ~r3_lattice3(X1,X0,X2)) & ((! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & r3_lattice3(X1,X0,X2)) | ~sP0(X0,X1,X2)))),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).
% 1.30/0.53  fof(f34,plain,(
% 1.30/0.53    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r3_lattices(X1,sK6(X0,X1,X2),X0) & r3_lattice3(X1,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f33,plain,(
% 1.30/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) | ~r3_lattice3(X1,X0,X2)) & ((! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & r3_lattice3(X1,X0,X2)) | ~sP0(X0,X1,X2)))),
% 1.30/0.53    inference(rectify,[],[f32])).
% 1.47/0.53  fof(f32,plain,(
% 1.47/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | ~sP0(X1,X0,X2)))),
% 1.47/0.53    inference(flattening,[],[f31])).
% 1.47/0.53  fof(f31,plain,(
% 1.47/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | ~sP0(X1,X0,X2)))),
% 1.47/0.53    inference(nnf_transformation,[],[f21])).
% 1.47/0.53  fof(f129,plain,(
% 1.47/0.53    ( ! [X2,X3,X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~r2_hidden(X1,X2) | ~m1_subset_1(sK6(X3,sK3,X2),u1_struct_0(sK3)) | r1_lattices(sK3,sK6(X3,sK3,X2),X1) | sP0(X3,sK3,X2) | ~r3_lattice3(sK3,X3,X2)) )),
% 1.47/0.53    inference(resolution,[],[f127,f66])).
% 1.47/0.53  fof(f66,plain,(
% 1.47/0.53    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK6(X0,X1,X2),X2) | sP0(X0,X1,X2) | ~r3_lattice3(X1,X0,X2)) )),
% 1.47/0.53    inference(cnf_transformation,[],[f35])).
% 1.47/0.53  fof(f127,plain,(
% 1.47/0.53    ( ! [X2,X0,X1] : (~r3_lattice3(sK3,X2,X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK3)) | r1_lattices(sK3,X2,X0)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f126,f50])).
% 1.47/0.53  fof(f126,plain,(
% 1.47/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r3_lattice3(sK3,X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK3)) | r1_lattices(sK3,X2,X0) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(resolution,[],[f73,f53])).
% 1.47/0.53  fof(f73,plain,(
% 1.47/0.53    ( ! [X4,X2,X0,X1] : (~l3_lattices(X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattices(X0,X1,X4) | v2_struct_0(X0)) )),
% 1.47/0.53    inference(cnf_transformation,[],[f43])).
% 1.47/0.53  fof(f43,plain,(
% 1.47/0.53    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.47/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f41,f42])).
% 1.47/0.53  fof(f42,plain,(
% 1.47/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))))),
% 1.47/0.53    introduced(choice_axiom,[])).
% 1.47/0.53  fof(f41,plain,(
% 1.47/0.53    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.47/0.53    inference(rectify,[],[f40])).
% 1.47/0.53  fof(f40,plain,(
% 1.47/0.53    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.47/0.53    inference(nnf_transformation,[],[f20])).
% 1.47/0.53  fof(f20,plain,(
% 1.47/0.53    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.47/0.53    inference(flattening,[],[f19])).
% 1.47/0.53  fof(f19,plain,(
% 1.47/0.53    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.47/0.53    inference(ennf_transformation,[],[f2])).
% 1.47/0.53  fof(f2,axiom,(
% 1.47/0.53    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 1.47/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 1.47/0.53  fof(f291,plain,(
% 1.47/0.53    ( ! [X0] : (~r1_lattices(sK3,X0,sK4) | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f290,f50])).
% 1.47/0.53  fof(f290,plain,(
% 1.47/0.53    ( ! [X0] : (~r1_lattices(sK3,X0,sK4) | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f289,f51])).
% 1.47/0.53  fof(f289,plain,(
% 1.47/0.53    ( ! [X0] : (~r1_lattices(sK3,X0,sK4) | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f288,f52])).
% 1.47/0.53  fof(f288,plain,(
% 1.47/0.53    ( ! [X0] : (~r1_lattices(sK3,X0,sK4) | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f287,f53])).
% 1.47/0.53  fof(f287,plain,(
% 1.47/0.53    ( ! [X0] : (~r1_lattices(sK3,X0,sK4) | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | ~l3_lattices(sK3) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f286,f54])).
% 1.47/0.53  fof(f286,plain,(
% 1.47/0.53    ( ! [X0] : (~r1_lattices(sK3,X0,sK4) | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l3_lattices(sK3) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f285,f91])).
% 1.47/0.53  fof(f91,plain,(
% 1.47/0.53    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 1.47/0.53    inference(resolution,[],[f86,f88])).
% 1.47/0.53  fof(f86,plain,(
% 1.47/0.53    ( ! [X4,X2,X1] : (~sP2(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 1.47/0.53    inference(equality_resolution,[],[f79])).
% 1.47/0.53  fof(f79,plain,(
% 1.47/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP2(X0,X1,X2)) )),
% 1.47/0.53    inference(cnf_transformation,[],[f48])).
% 1.47/0.53  fof(f285,plain,(
% 1.47/0.53    ( ! [X0] : (~r1_lattices(sK3,X0,sK4) | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | ~r2_hidden(sK4,k2_tarski(X0,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l3_lattices(sK3) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(duplicate_literal_removal,[],[f283])).
% 1.47/0.53  fof(f283,plain,(
% 1.47/0.53    ( ! [X0] : (~r1_lattices(sK3,X0,sK4) | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | ~r2_hidden(sK4,k2_tarski(X0,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l3_lattices(sK3) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(resolution,[],[f263,f60])).
% 1.47/0.53  fof(f60,plain,(
% 1.47/0.53    ( ! [X2,X0,X1] : (~r4_lattice3(X0,X1,X2) | k15_lattice3(X0,X2) = X1 | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.47/0.53    inference(cnf_transformation,[],[f14])).
% 1.47/0.53  fof(f14,plain,(
% 1.47/0.53    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | ~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.47/0.53    inference(flattening,[],[f13])).
% 1.47/0.53  fof(f13,plain,(
% 1.47/0.53    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | (~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.47/0.53    inference(ennf_transformation,[],[f6])).
% 1.47/0.53  fof(f6,axiom,(
% 1.47/0.53    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 1.47/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).
% 1.47/0.53  fof(f263,plain,(
% 1.47/0.53    ( ! [X7] : (r4_lattice3(sK3,sK4,k2_tarski(X7,sK4)) | ~r1_lattices(sK3,X7,sK4) | sK4 = k15_lattice3(sK3,k2_tarski(X7,sK4))) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f262,f50])).
% 1.47/0.53  fof(f262,plain,(
% 1.47/0.53    ( ! [X7] : (~r1_lattices(sK3,X7,sK4) | r4_lattice3(sK3,sK4,k2_tarski(X7,sK4)) | v2_struct_0(sK3) | sK4 = k15_lattice3(sK3,k2_tarski(X7,sK4))) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f261,f53])).
% 1.47/0.53  fof(f261,plain,(
% 1.47/0.53    ( ! [X7] : (~r1_lattices(sK3,X7,sK4) | r4_lattice3(sK3,sK4,k2_tarski(X7,sK4)) | ~l3_lattices(sK3) | v2_struct_0(sK3) | sK4 = k15_lattice3(sK3,k2_tarski(X7,sK4))) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f255,f54])).
% 1.47/0.53  fof(f255,plain,(
% 1.47/0.53    ( ! [X7] : (~r1_lattices(sK3,X7,sK4) | r4_lattice3(sK3,sK4,k2_tarski(X7,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l3_lattices(sK3) | v2_struct_0(sK3) | sK4 = k15_lattice3(sK3,k2_tarski(X7,sK4))) )),
% 1.47/0.53    inference(superposition,[],[f72,f248])).
% 1.47/0.53  fof(f248,plain,(
% 1.47/0.53    ( ! [X0] : (sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0 | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f247,f50])).
% 1.47/0.53  fof(f247,plain,(
% 1.47/0.53    ( ! [X0] : (sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0 | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f246,f51])).
% 1.47/0.53  fof(f246,plain,(
% 1.47/0.53    ( ! [X0] : (sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0 | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f245,f52])).
% 1.47/0.53  fof(f245,plain,(
% 1.47/0.53    ( ! [X0] : (sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0 | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f244,f53])).
% 1.47/0.53  fof(f244,plain,(
% 1.47/0.53    ( ! [X0] : (sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0 | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | ~l3_lattices(sK3) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f243,f54])).
% 1.47/0.53  fof(f243,plain,(
% 1.47/0.53    ( ! [X0] : (sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0 | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l3_lattices(sK3) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f242,f91])).
% 1.47/0.53  fof(f242,plain,(
% 1.47/0.53    ( ! [X0] : (sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0 | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | ~r2_hidden(sK4,k2_tarski(X0,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l3_lattices(sK3) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(duplicate_literal_removal,[],[f240])).
% 1.47/0.53  fof(f240,plain,(
% 1.47/0.53    ( ! [X0] : (sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0 | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4)) | ~r2_hidden(sK4,k2_tarski(X0,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l3_lattices(sK3) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(resolution,[],[f194,f60])).
% 1.47/0.53  fof(f194,plain,(
% 1.47/0.53    ( ! [X5] : (r4_lattice3(sK3,sK4,k2_tarski(X5,sK4)) | sK7(sK3,sK4,k2_tarski(X5,sK4)) = X5 | sK4 = k15_lattice3(sK3,k2_tarski(X5,sK4))) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f193,f50])).
% 1.47/0.53  fof(f193,plain,(
% 1.47/0.53    ( ! [X5] : (r4_lattice3(sK3,sK4,k2_tarski(X5,sK4)) | v2_struct_0(sK3) | sK7(sK3,sK4,k2_tarski(X5,sK4)) = X5 | sK4 = k15_lattice3(sK3,k2_tarski(X5,sK4))) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f192,f53])).
% 1.47/0.53  fof(f192,plain,(
% 1.47/0.53    ( ! [X5] : (r4_lattice3(sK3,sK4,k2_tarski(X5,sK4)) | ~l3_lattices(sK3) | v2_struct_0(sK3) | sK7(sK3,sK4,k2_tarski(X5,sK4)) = X5 | sK4 = k15_lattice3(sK3,k2_tarski(X5,sK4))) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f191,f54])).
% 1.47/0.53  fof(f191,plain,(
% 1.47/0.53    ( ! [X5] : (r4_lattice3(sK3,sK4,k2_tarski(X5,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l3_lattices(sK3) | v2_struct_0(sK3) | sK7(sK3,sK4,k2_tarski(X5,sK4)) = X5 | sK4 = k15_lattice3(sK3,k2_tarski(X5,sK4))) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f181,f136])).
% 1.47/0.53  fof(f136,plain,(
% 1.47/0.53    r1_lattices(sK3,sK4,sK4)),
% 1.47/0.53    inference(subsumption_resolution,[],[f132,f55])).
% 1.47/0.53  fof(f132,plain,(
% 1.47/0.53    ~r2_hidden(sK4,sK5) | r1_lattices(sK3,sK4,sK4)),
% 1.47/0.53    inference(resolution,[],[f130,f54])).
% 1.47/0.53  fof(f130,plain,(
% 1.47/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,sK5) | r1_lattices(sK3,sK4,X0)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f128,f54])).
% 1.47/0.53  fof(f128,plain,(
% 1.47/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,sK5) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | r1_lattices(sK3,sK4,X0)) )),
% 1.47/0.53    inference(resolution,[],[f127,f56])).
% 1.47/0.53  fof(f181,plain,(
% 1.47/0.53    ( ! [X5] : (~r1_lattices(sK3,sK4,sK4) | r4_lattice3(sK3,sK4,k2_tarski(X5,sK4)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l3_lattices(sK3) | v2_struct_0(sK3) | sK7(sK3,sK4,k2_tarski(X5,sK4)) = X5 | sK4 = k15_lattice3(sK3,k2_tarski(X5,sK4))) )),
% 1.47/0.53    inference(superposition,[],[f72,f173])).
% 1.47/0.53  fof(f173,plain,(
% 1.47/0.53    ( ! [X0] : (sK4 = sK7(sK3,sK4,k2_tarski(X0,sK4)) | sK7(sK3,sK4,k2_tarski(X0,sK4)) = X0 | sK4 = k15_lattice3(sK3,k2_tarski(X0,sK4))) )),
% 1.47/0.53    inference(resolution,[],[f165,f91])).
% 1.47/0.53  fof(f165,plain,(
% 1.47/0.53    ( ! [X0,X1] : (~r2_hidden(sK4,k2_tarski(X0,X1)) | sK7(sK3,sK4,k2_tarski(X0,X1)) = X1 | sK4 = k15_lattice3(sK3,k2_tarski(X0,X1)) | sK7(sK3,sK4,k2_tarski(X0,X1)) = X0) )),
% 1.47/0.53    inference(resolution,[],[f159,f54])).
% 1.47/0.53  fof(f159,plain,(
% 1.47/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | sK7(sK3,X0,k2_tarski(X1,X2)) = X1 | sK7(sK3,X0,k2_tarski(X1,X2)) = X2 | k15_lattice3(sK3,k2_tarski(X1,X2)) = X0 | ~r2_hidden(X0,k2_tarski(X1,X2))) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f158,f50])).
% 1.47/0.53  fof(f158,plain,(
% 1.47/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | sK7(sK3,X0,k2_tarski(X1,X2)) = X1 | sK7(sK3,X0,k2_tarski(X1,X2)) = X2 | k15_lattice3(sK3,k2_tarski(X1,X2)) = X0 | ~r2_hidden(X0,k2_tarski(X1,X2)) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f157,f51])).
% 1.47/0.53  fof(f157,plain,(
% 1.47/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | sK7(sK3,X0,k2_tarski(X1,X2)) = X1 | sK7(sK3,X0,k2_tarski(X1,X2)) = X2 | k15_lattice3(sK3,k2_tarski(X1,X2)) = X0 | ~r2_hidden(X0,k2_tarski(X1,X2)) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f156,f52])).
% 1.47/0.53  fof(f156,plain,(
% 1.47/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | sK7(sK3,X0,k2_tarski(X1,X2)) = X1 | sK7(sK3,X0,k2_tarski(X1,X2)) = X2 | k15_lattice3(sK3,k2_tarski(X1,X2)) = X0 | ~r2_hidden(X0,k2_tarski(X1,X2)) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f155,f53])).
% 1.47/0.53  fof(f155,plain,(
% 1.47/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | sK7(sK3,X0,k2_tarski(X1,X2)) = X1 | sK7(sK3,X0,k2_tarski(X1,X2)) = X2 | k15_lattice3(sK3,k2_tarski(X1,X2)) = X0 | ~r2_hidden(X0,k2_tarski(X1,X2)) | ~l3_lattices(sK3) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(duplicate_literal_removal,[],[f152])).
% 1.47/0.53  fof(f152,plain,(
% 1.47/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | sK7(sK3,X0,k2_tarski(X1,X2)) = X1 | sK7(sK3,X0,k2_tarski(X1,X2)) = X2 | k15_lattice3(sK3,k2_tarski(X1,X2)) = X0 | ~r2_hidden(X0,k2_tarski(X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~l3_lattices(sK3) | ~v4_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(resolution,[],[f107,f60])).
% 1.47/0.53  fof(f107,plain,(
% 1.47/0.53    ( ! [X2,X0,X1] : (r4_lattice3(sK3,X0,k2_tarski(X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | sK7(sK3,X0,k2_tarski(X1,X2)) = X1 | sK7(sK3,X0,k2_tarski(X1,X2)) = X2) )),
% 1.47/0.53    inference(resolution,[],[f106,f94])).
% 1.47/0.53  fof(f94,plain,(
% 1.47/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X2)) | X0 = X1 | X1 = X2) )),
% 1.47/0.53    inference(resolution,[],[f77,f88])).
% 1.47/0.53  fof(f77,plain,(
% 1.47/0.53    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 1.47/0.53    inference(cnf_transformation,[],[f48])).
% 1.47/0.53  fof(f106,plain,(
% 1.47/0.53    ( ! [X0,X1] : (r2_hidden(sK7(sK3,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | r4_lattice3(sK3,X0,X1)) )),
% 1.47/0.53    inference(subsumption_resolution,[],[f105,f50])).
% 1.47/0.53  fof(f105,plain,(
% 1.47/0.53    ( ! [X0,X1] : (r2_hidden(sK7(sK3,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | r4_lattice3(sK3,X0,X1) | v2_struct_0(sK3)) )),
% 1.47/0.53    inference(resolution,[],[f71,f53])).
% 1.47/0.53  fof(f71,plain,(
% 1.47/0.53    ( ! [X2,X0,X1] : (~l3_lattices(X0) | r2_hidden(sK7(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r4_lattice3(X0,X1,X2) | v2_struct_0(X0)) )),
% 1.47/0.53    inference(cnf_transformation,[],[f39])).
% 1.47/0.53  fof(f39,plain,(
% 1.47/0.53    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X2) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.47/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).
% 1.47/0.53  fof(f38,plain,(
% 1.47/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X2) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 1.47/0.53    introduced(choice_axiom,[])).
% 1.47/0.53  fof(f37,plain,(
% 1.47/0.53    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.47/0.53    inference(rectify,[],[f36])).
% 1.47/0.53  fof(f36,plain,(
% 1.47/0.53    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.47/0.53    inference(nnf_transformation,[],[f18])).
% 1.47/0.53  fof(f18,plain,(
% 1.47/0.53    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.47/0.53    inference(flattening,[],[f17])).
% 1.47/0.54  fof(f17,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.47/0.54    inference(ennf_transformation,[],[f3])).
% 1.47/0.54  fof(f3,axiom,(
% 1.47/0.54    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 1.47/0.54  fof(f72,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (~r1_lattices(X0,sK7(X0,X1,X2),X1) | r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f39])).
% 1.47/0.54  fof(f124,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~r3_lattice3(sK3,k15_lattice3(sK3,X0),X1) | sP0(k15_lattice3(sK3,X0),sK3,X1) | ~r2_hidden(sK6(k15_lattice3(sK3,X0),sK3,X1),X0)) )),
% 1.47/0.54    inference(subsumption_resolution,[],[f123,f65])).
% 1.47/0.54  fof(f123,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_subset_1(sK6(k15_lattice3(sK3,X0),sK3,X1),u1_struct_0(sK3)) | ~r2_hidden(sK6(k15_lattice3(sK3,X0),sK3,X1),X0) | sP0(k15_lattice3(sK3,X0),sK3,X1) | ~r3_lattice3(sK3,k15_lattice3(sK3,X0),X1)) )),
% 1.47/0.54    inference(resolution,[],[f122,f67])).
% 1.47/0.54  fof(f67,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (~r3_lattices(X1,sK6(X0,X1,X2),X0) | sP0(X0,X1,X2) | ~r3_lattice3(X1,X0,X2)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f35])).
% 1.47/0.54  fof(f122,plain,(
% 1.47/0.54    ( ! [X0,X1] : (r3_lattices(sK3,X0,k15_lattice3(sK3,X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,X1)) )),
% 1.47/0.54    inference(subsumption_resolution,[],[f121,f50])).
% 1.47/0.54  fof(f121,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | r3_lattices(sK3,X0,k15_lattice3(sK3,X1)) | v2_struct_0(sK3)) )),
% 1.47/0.54    inference(subsumption_resolution,[],[f120,f51])).
% 1.47/0.54  fof(f120,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | r3_lattices(sK3,X0,k15_lattice3(sK3,X1)) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.54    inference(subsumption_resolution,[],[f119,f53])).
% 1.47/0.54  fof(f119,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~l3_lattices(sK3) | r3_lattices(sK3,X0,k15_lattice3(sK3,X1)) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 1.47/0.54    inference(resolution,[],[f58,f52])).
% 1.47/0.54  fof(f58,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,k15_lattice3(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f12])).
% 1.47/0.54  fof(f12,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.47/0.54    inference(flattening,[],[f11])).
% 1.47/0.54  fof(f11,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.47/0.54    inference(ennf_transformation,[],[f5])).
% 1.47/0.54  fof(f5,axiom,(
% 1.47/0.54    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).
% 1.47/0.54  % SZS output end Proof for theBenchmark
% 1.47/0.54  % (23218)------------------------------
% 1.47/0.54  % (23218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.54  % (23218)Termination reason: Refutation
% 1.47/0.54  
% 1.47/0.54  % (23218)Memory used [KB]: 6524
% 1.47/0.54  % (23218)Time elapsed: 0.121 s
% 1.47/0.54  % (23218)------------------------------
% 1.47/0.54  % (23218)------------------------------
% 1.47/0.54  % (23214)Success in time 0.202 s
%------------------------------------------------------------------------------
