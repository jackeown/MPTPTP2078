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
% DateTime   : Thu Dec  3 13:15:47 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 746 expanded)
%              Number of leaves         :   22 ( 271 expanded)
%              Depth                    :   34
%              Number of atoms          :  985 (6374 expanded)
%              Number of equality atoms :   55 (  91 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f944,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f342,f350,f573,f587,f716,f926])).

fof(f926,plain,
    ( ~ spl9_9
    | spl9_10
    | ~ spl9_26 ),
    inference(avatar_contradiction_clause,[],[f925])).

fof(f925,plain,
    ( $false
    | ~ spl9_9
    | spl9_10
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f924,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    & ! [X3] :
        ( ( r2_hidden(sK3(X3),sK2)
          & r3_lattices(sK0,X3,sK3(X3))
          & m1_subset_1(sK3(X3),u1_struct_0(sK0)) )
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
            & ! [X3] :
                ( ? [X4] :
                    ( r2_hidden(X4,X2)
                    & r3_lattices(X0,X3,X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ~ r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(sK0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(sK0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2,X1] :
        ( ~ r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2))
        & ! [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(sK0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) )
   => ( ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
      & ! [X3] :
          ( ? [X4] :
              ( r2_hidden(X4,sK2)
              & r3_lattices(sK0,X3,X4)
              & m1_subset_1(X4,u1_struct_0(sK0)) )
          | ~ r2_hidden(X3,sK1)
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X3] :
      ( ? [X4] :
          ( r2_hidden(X4,sK2)
          & r3_lattices(sK0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(sK0)) )
     => ( r2_hidden(sK3(X3),sK2)
        & r3_lattices(sK0,X3,sK3(X3))
        & m1_subset_1(sK3(X3),u1_struct_0(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ~ ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( r2_hidden(X4,X2)
                            & r3_lattices(X0,X3,X4) ) )
                    & r2_hidden(X3,X1) ) )
           => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ~ ( r2_hidden(X4,X2)
                          & r3_lattices(X0,X3,X4) ) )
                  & r2_hidden(X3,X1) ) )
         => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

fof(f924,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_9
    | spl9_10
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f923,f52])).

fof(f52,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f923,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_9
    | spl9_10
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f922,f53])).

fof(f53,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f922,plain,
    ( ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_9
    | spl9_10
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f921,f54])).

fof(f54,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f921,plain,
    ( ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_9
    | spl9_10
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f920,f336])).

fof(f336,plain,
    ( m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl9_9
  <=> m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f920,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_9
    | spl9_10
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f917,f341])).

fof(f341,plain,
    ( ~ r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1))
    | spl9_10 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl9_10
  <=> r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f917,plain,
    ( r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_9
    | ~ spl9_26 ),
    inference(resolution,[],[f905,f86])).

fof(f86,plain,(
    ! [X2,X3,X1] :
      ( ~ r4_lattice3(X1,X3,X2)
      | r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r4_lattice3(X1,sK6(X0,X1,X2),X2)
            & sK6(X0,X1,X2) = X0
            & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK6(X0,X1,X2),X2)
        & sK6(X0,X1,X2) = X0
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

% (23715)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f42,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f905,plain,
    ( r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)
    | ~ spl9_9
    | ~ spl9_26 ),
    inference(resolution,[],[f894,f702])).

fof(f702,plain,
    ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f701])).

fof(f701,plain,
    ( spl9_26
  <=> r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f894,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2))
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f893,f370])).

fof(f370,plain,
    ( ! [X1] :
        ( r4_lattice3(sK0,k15_lattice3(sK0,sK2),X1)
        | m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0)) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f369,f51])).

fof(f369,plain,
    ( ! [X1] :
        ( m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0))
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X1)
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f359,f54])).

fof(f359,plain,
    ( ! [X1] :
        ( m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0))
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X1)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(resolution,[],[f336,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r4_lattice3(X0,X1,X2)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
                  & r2_hidden(sK5(X0,X1,X2),X2)
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),X2)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f893,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2))
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f892,f51])).

fof(f892,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2))
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0)
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f891,f54])).

fof(f891,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2))
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f890,f336])).

fof(f890,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2))
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0)
        | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(resolution,[],[f796,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f796,plain,
    ( ! [X1] :
        ( r1_lattices(sK0,X1,k15_lattice3(sK0,sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_5_lattice3(sK0,sK2)) )
    | ~ spl9_9 ),
    inference(resolution,[],[f295,f336])).

fof(f295,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,X2,k15_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f294,f51])).

fof(f294,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,X2,k15_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f288,f54])).

fof(f288,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,X2,k15_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f284])).

fof(f284,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,X2,k15_lattice3(sK0,X1))
      | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f196,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r4_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattices(X0,X4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f196,plain,(
    ! [X1] :
      ( r4_lattice3(sK0,k15_lattice3(sK0,X1),a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f195,f51])).

fof(f195,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | r4_lattice3(sK0,k15_lattice3(sK0,X1),a_2_5_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f194,f52])).

fof(f194,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | r4_lattice3(sK0,k15_lattice3(sK0,X1),a_2_5_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f193,f53])).

fof(f193,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | r4_lattice3(sK0,k15_lattice3(sK0,X1),a_2_5_lattice3(sK0,X1))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f190,f54])).

fof(f190,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | r4_lattice3(sK0,k15_lattice3(sK0,X1),a_2_5_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f92,f98])).

fof(f98,plain,(
    ! [X0] : k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) ),
    inference(global_subsumption,[],[f54,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f96,f51])).

fof(f96,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f93,f52])).

fof(f93,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f53,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
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
     => ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X2,X1)
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
                & r4_lattice3(X0,sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
        & r4_lattice3(X0,sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

fof(f716,plain,
    ( ~ spl9_9
    | spl9_10
    | ~ spl9_15
    | ~ spl9_16
    | spl9_26 ),
    inference(avatar_contradiction_clause,[],[f715])).

fof(f715,plain,
    ( $false
    | ~ spl9_9
    | spl9_10
    | ~ spl9_15
    | ~ spl9_16
    | spl9_26 ),
    inference(subsumption_resolution,[],[f714,f566])).

fof(f566,plain,
    ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f565])).

fof(f565,plain,
    ( spl9_15
  <=> r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f714,plain,
    ( ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl9_9
    | spl9_10
    | ~ spl9_16
    | spl9_26 ),
    inference(subsumption_resolution,[],[f713,f572])).

fof(f572,plain,
    ( r2_hidden(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f570])).

fof(f570,plain,
    ( spl9_16
  <=> r2_hidden(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f713,plain,
    ( ~ r2_hidden(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)
    | ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl9_9
    | spl9_10
    | spl9_26 ),
    inference(subsumption_resolution,[],[f712,f545])).

fof(f545,plain,
    ( m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ spl9_9
    | spl9_10 ),
    inference(resolution,[],[f498,f341])).

fof(f498,plain,
    ( ! [X1] :
        ( r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1))
        | m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0)) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f497,f51])).

fof(f497,plain,
    ( ! [X1] :
        ( m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0))
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1))
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f496,f52])).

fof(f496,plain,
    ( ! [X1] :
        ( m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0))
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f495,f53])).

fof(f495,plain,
    ( ! [X1] :
        ( m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0))
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1))
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f494,f54])).

fof(f494,plain,
    ( ! [X1] :
        ( m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0))
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f490,f336])).

fof(f490,plain,
    ( ! [X1] :
        ( m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0))
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1))
        | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(resolution,[],[f370,f86])).

fof(f712,plain,
    ( ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)
    | ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | spl9_26 ),
    inference(resolution,[],[f703,f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X0),X1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f187,f55])).

fof(f55,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK1)
      | m1_subset_1(sK3(X3),u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X0),X1)
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f186,f51])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X0),X1)
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f185,f52])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X0),X1)
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f53])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X0),X1)
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f183,f54])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X0),X1)
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK3(X0),X1)
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f56,f87])).

fof(f87,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r3_lattices(X1,X3,X4)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X3,a_2_5_lattice3(X1,X2))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r3_lattices(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X2)
            & r3_lattices(X1,sK7(X0,X1,X2),sK8(X0,X1,X2))
            & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
            & sK7(X0,X1,X2) = X0
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f47,f49,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r3_lattices(X1,X5,X6)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r3_lattices(X1,sK7(X0,X1,X2),X6)
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK7(X0,X1,X2) = X0
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r3_lattices(X1,sK7(X0,X1,X2),X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK8(X0,X1,X2),X2)
        & r3_lattices(X1,sK7(X0,X1,X2),sK8(X0,X1,X2))
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r3_lattices(X1,X5,X6)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

fof(f56,plain,(
    ! [X3] :
      ( r3_lattices(sK0,X3,sK3(X3))
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f703,plain,
    ( ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2))
    | spl9_26 ),
    inference(avatar_component_clause,[],[f701])).

fof(f587,plain,
    ( ~ spl9_9
    | spl9_10
    | spl9_15 ),
    inference(avatar_contradiction_clause,[],[f586])).

fof(f586,plain,
    ( $false
    | ~ spl9_9
    | spl9_10
    | spl9_15 ),
    inference(subsumption_resolution,[],[f585,f341])).

fof(f585,plain,
    ( r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1))
    | ~ spl9_9
    | spl9_15 ),
    inference(resolution,[],[f567,f464])).

fof(f464,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X1),X1)
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1)) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f463,f51])).

fof(f463,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X1),X1)
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1))
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f462,f52])).

fof(f462,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X1),X1)
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f461,f53])).

fof(f461,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X1),X1)
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1))
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f460,f54])).

fof(f460,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X1),X1)
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f456,f336])).

fof(f456,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X1),X1)
        | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1))
        | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(resolution,[],[f372,f86])).

fof(f372,plain,
    ( ! [X2] :
        ( r4_lattice3(sK0,k15_lattice3(sK0,sK2),X2)
        | r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X2),X2) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f371,f51])).

fof(f371,plain,
    ( ! [X2] :
        ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X2),X2)
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X2)
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f360,f54])).

fof(f360,plain,
    ( ! [X2] :
        ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X2),X2)
        | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X2)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(resolution,[],[f336,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X2),X2)
      | r4_lattice3(X0,X1,X2)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f567,plain,
    ( ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | spl9_15 ),
    inference(avatar_component_clause,[],[f565])).

fof(f573,plain,
    ( spl9_16
    | ~ spl9_15
    | ~ spl9_9
    | spl9_10 ),
    inference(avatar_split_clause,[],[f557,f339,f335,f565,f570])).

fof(f557,plain,
    ( ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | r2_hidden(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)
    | ~ spl9_9
    | spl9_10 ),
    inference(resolution,[],[f545,f57])).

fof(f57,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(sK3(X3),sK2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f350,plain,(
    spl9_9 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | spl9_9 ),
    inference(subsumption_resolution,[],[f348,f51])).

fof(f348,plain,
    ( v2_struct_0(sK0)
    | spl9_9 ),
    inference(subsumption_resolution,[],[f347,f54])).

fof(f347,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_9 ),
    inference(resolution,[],[f337,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f337,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | spl9_9 ),
    inference(avatar_component_clause,[],[f335])).

fof(f342,plain,
    ( ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f330,f339,f335])).

fof(f330,plain,
    ( ~ r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f214,f58])).

fof(f58,plain,(
    ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f214,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f213,f51])).

fof(f213,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f212,f52])).

fof(f212,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f211,f53])).

fof(f211,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f210,f54])).

fof(f210,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f63,f104])).

fof(f104,plain,(
    ! [X2] : k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2)) ),
    inference(global_subsumption,[],[f54,f103])).

fof(f103,plain,(
    ! [X2] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f102,f51])).

fof(f102,plain,(
    ! [X2] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f95,f52])).

fof(f95,plain,(
    ! [X2] :
      ( ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f53,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
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
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:52:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (23730)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.49  % (23722)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (23716)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (23711)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (23710)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (23709)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (23724)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (23717)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (23726)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (23714)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (23718)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.27/0.53  % (23729)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.27/0.53  % (23721)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.27/0.53  % (23725)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.27/0.53  % (23721)Refutation not found, incomplete strategy% (23721)------------------------------
% 1.27/0.53  % (23721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (23721)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (23721)Memory used [KB]: 6140
% 1.27/0.53  % (23721)Time elapsed: 0.083 s
% 1.27/0.53  % (23721)------------------------------
% 1.27/0.53  % (23721)------------------------------
% 1.27/0.53  % (23719)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.27/0.53  % (23713)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.27/0.54  % (23719)Refutation not found, incomplete strategy% (23719)------------------------------
% 1.27/0.54  % (23719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (23719)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (23719)Memory used [KB]: 10618
% 1.27/0.54  % (23719)Time elapsed: 0.131 s
% 1.27/0.54  % (23719)------------------------------
% 1.27/0.54  % (23719)------------------------------
% 1.27/0.54  % (23712)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.27/0.54  % (23713)Refutation not found, incomplete strategy% (23713)------------------------------
% 1.27/0.54  % (23713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (23713)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (23713)Memory used [KB]: 6140
% 1.27/0.54  % (23713)Time elapsed: 0.097 s
% 1.27/0.54  % (23713)------------------------------
% 1.27/0.54  % (23713)------------------------------
% 1.27/0.54  % (23732)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.42/0.54  % (23714)Refutation not found, incomplete strategy% (23714)------------------------------
% 1.42/0.54  % (23714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (23714)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (23714)Memory used [KB]: 10618
% 1.42/0.54  % (23714)Time elapsed: 0.128 s
% 1.42/0.54  % (23714)------------------------------
% 1.42/0.54  % (23714)------------------------------
% 1.42/0.54  % (23728)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.42/0.54  % (23727)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.42/0.55  % (23720)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.42/0.55  % (23708)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.42/0.56  % (23731)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.42/0.56  % (23733)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.42/0.56  % (23709)Refutation found. Thanks to Tanya!
% 1.42/0.56  % SZS status Theorem for theBenchmark
% 1.42/0.56  % SZS output start Proof for theBenchmark
% 1.42/0.56  fof(f944,plain,(
% 1.42/0.56    $false),
% 1.42/0.56    inference(avatar_sat_refutation,[],[f342,f350,f573,f587,f716,f926])).
% 1.42/0.56  fof(f926,plain,(
% 1.42/0.56    ~spl9_9 | spl9_10 | ~spl9_26),
% 1.42/0.56    inference(avatar_contradiction_clause,[],[f925])).
% 1.42/0.56  fof(f925,plain,(
% 1.42/0.56    $false | (~spl9_9 | spl9_10 | ~spl9_26)),
% 1.42/0.56    inference(subsumption_resolution,[],[f924,f51])).
% 1.42/0.56  fof(f51,plain,(
% 1.42/0.56    ~v2_struct_0(sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f32])).
% 1.42/0.56  fof(f32,plain,(
% 1.42/0.56    (~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) & ! [X3] : ((r2_hidden(sK3(X3),sK2) & r3_lattices(sK0,X3,sK3(X3)) & m1_subset_1(sK3(X3),u1_struct_0(sK0))) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)))) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f31,f30,f29])).
% 1.42/0.56  fof(f29,plain,(
% 1.42/0.56    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X2,X1] : (~r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(sK0,X3,X4) & m1_subset_1(X4,u1_struct_0(sK0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(sK0)))) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f30,plain,(
% 1.42/0.56    ? [X2,X1] : (~r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(sK0,X3,X4) & m1_subset_1(X4,u1_struct_0(sK0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(sK0)))) => (~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) & ! [X3] : (? [X4] : (r2_hidden(X4,sK2) & r3_lattices(sK0,X3,X4) & m1_subset_1(X4,u1_struct_0(sK0))) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0))))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f31,plain,(
% 1.42/0.56    ! [X3] : (? [X4] : (r2_hidden(X4,sK2) & r3_lattices(sK0,X3,X4) & m1_subset_1(X4,u1_struct_0(sK0))) => (r2_hidden(sK3(X3),sK2) & r3_lattices(sK0,X3,sK3(X3)) & m1_subset_1(sK3(X3),u1_struct_0(sK0))))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f12,plain,(
% 1.42/0.56    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.42/0.56    inference(flattening,[],[f11])).
% 1.42/0.56  fof(f11,plain,(
% 1.42/0.56    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : ((? [X4] : ((r2_hidden(X4,X2) & r3_lattices(X0,X3,X4)) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f10])).
% 1.42/0.56  fof(f10,negated_conjecture,(
% 1.42/0.56    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 1.42/0.56    inference(negated_conjecture,[],[f9])).
% 1.42/0.56  fof(f9,conjecture,(
% 1.42/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).
% 1.42/0.56  fof(f924,plain,(
% 1.42/0.56    v2_struct_0(sK0) | (~spl9_9 | spl9_10 | ~spl9_26)),
% 1.42/0.56    inference(subsumption_resolution,[],[f923,f52])).
% 1.42/0.56  fof(f52,plain,(
% 1.42/0.56    v10_lattices(sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f32])).
% 1.42/0.56  fof(f923,plain,(
% 1.42/0.56    ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_9 | spl9_10 | ~spl9_26)),
% 1.42/0.56    inference(subsumption_resolution,[],[f922,f53])).
% 1.42/0.56  fof(f53,plain,(
% 1.42/0.56    v4_lattice3(sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f32])).
% 1.42/0.56  fof(f922,plain,(
% 1.42/0.56    ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_9 | spl9_10 | ~spl9_26)),
% 1.42/0.56    inference(subsumption_resolution,[],[f921,f54])).
% 1.42/0.56  fof(f54,plain,(
% 1.42/0.56    l3_lattices(sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f32])).
% 1.42/0.56  fof(f921,plain,(
% 1.42/0.56    ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_9 | spl9_10 | ~spl9_26)),
% 1.42/0.56    inference(subsumption_resolution,[],[f920,f336])).
% 1.42/0.56  fof(f336,plain,(
% 1.42/0.56    m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~spl9_9),
% 1.42/0.56    inference(avatar_component_clause,[],[f335])).
% 1.42/0.56  fof(f335,plain,(
% 1.42/0.56    spl9_9 <=> m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))),
% 1.42/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.42/0.56  fof(f920,plain,(
% 1.42/0.56    ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_9 | spl9_10 | ~spl9_26)),
% 1.42/0.56    inference(subsumption_resolution,[],[f917,f341])).
% 1.42/0.56  fof(f341,plain,(
% 1.42/0.56    ~r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1)) | spl9_10),
% 1.42/0.56    inference(avatar_component_clause,[],[f339])).
% 1.42/0.56  fof(f339,plain,(
% 1.42/0.56    spl9_10 <=> r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1))),
% 1.42/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.42/0.56  fof(f917,plain,(
% 1.42/0.56    r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl9_9 | ~spl9_26)),
% 1.42/0.56    inference(resolution,[],[f905,f86])).
% 1.42/0.56  fof(f86,plain,(
% 1.42/0.56    ( ! [X2,X3,X1] : (~r4_lattice3(X1,X3,X2) | r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.42/0.56    inference(equality_resolution,[],[f77])).
% 1.42/0.56  fof(f77,plain,(
% 1.42/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f45])).
% 1.42/0.56  fof(f45,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK6(X0,X1,X2),X2) & sK6(X0,X1,X2) = X0 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 1.42/0.56  fof(f44,plain,(
% 1.42/0.56    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK6(X0,X1,X2),X2) & sK6(X0,X1,X2) = X0 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f43,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.42/0.56    inference(rectify,[],[f42])).
% 1.42/0.56  % (23715)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.42/0.56  fof(f42,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.42/0.56    inference(nnf_transformation,[],[f26])).
% 1.42/0.56  fof(f26,plain,(
% 1.42/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.42/0.56    inference(flattening,[],[f25])).
% 1.42/0.56  fof(f25,plain,(
% 1.42/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 1.42/0.56    inference(ennf_transformation,[],[f4])).
% 1.42/0.56  fof(f4,axiom,(
% 1.42/0.56    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 1.42/0.56  fof(f905,plain,(
% 1.42/0.56    r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1) | (~spl9_9 | ~spl9_26)),
% 1.42/0.56    inference(resolution,[],[f894,f702])).
% 1.42/0.56  fof(f702,plain,(
% 1.42/0.56    r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2)) | ~spl9_26),
% 1.42/0.56    inference(avatar_component_clause,[],[f701])).
% 1.42/0.56  fof(f701,plain,(
% 1.42/0.56    spl9_26 <=> r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2))),
% 1.42/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 1.42/0.56  fof(f894,plain,(
% 1.42/0.56    ( ! [X0] : (~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2)) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0)) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f893,f370])).
% 1.42/0.56  fof(f370,plain,(
% 1.42/0.56    ( ! [X1] : (r4_lattice3(sK0,k15_lattice3(sK0,sK2),X1) | m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0))) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f369,f51])).
% 1.42/0.56  fof(f369,plain,(
% 1.42/0.56    ( ! [X1] : (m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0)) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X1) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f359,f54])).
% 1.42/0.56  fof(f359,plain,(
% 1.42/0.56    ( ! [X1] : (m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0)) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X1) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(resolution,[],[f336,f70])).
% 1.42/0.56  fof(f70,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r4_lattice3(X0,X1,X2) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f41])).
% 1.42/0.56  fof(f41,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).
% 1.42/0.56  fof(f40,plain,(
% 1.42/0.56    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f39,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(rectify,[],[f38])).
% 1.42/0.56  fof(f38,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(nnf_transformation,[],[f22])).
% 1.42/0.56  fof(f22,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(flattening,[],[f21])).
% 1.42/0.56  fof(f21,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f1])).
% 1.42/0.56  fof(f1,axiom,(
% 1.42/0.56    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 1.42/0.56  fof(f893,plain,(
% 1.42/0.56    ( ! [X0] : (~m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) | ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2)) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0)) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f892,f51])).
% 1.42/0.56  fof(f892,plain,(
% 1.42/0.56    ( ! [X0] : (~m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) | ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2)) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f891,f54])).
% 1.42/0.56  fof(f891,plain,(
% 1.42/0.56    ( ! [X0] : (~m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) | ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2)) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f890,f336])).
% 1.42/0.56  fof(f890,plain,(
% 1.42/0.56    ( ! [X0] : (~m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X0),u1_struct_0(sK0)) | ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X0),a_2_5_lattice3(sK0,sK2)) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X0) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(resolution,[],[f796,f72])).
% 1.42/0.56  fof(f72,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~r1_lattices(X0,sK5(X0,X1,X2),X1) | r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f41])).
% 1.42/0.56  fof(f796,plain,(
% 1.42/0.56    ( ! [X1] : (r1_lattices(sK0,X1,k15_lattice3(sK0,sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,a_2_5_lattice3(sK0,sK2))) ) | ~spl9_9),
% 1.42/0.56    inference(resolution,[],[f295,f336])).
% 1.42/0.56  fof(f295,plain,(
% 1.42/0.56    ( ! [X2,X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,X2,k15_lattice3(sK0,X1))) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f294,f51])).
% 1.42/0.56  fof(f294,plain,(
% 1.42/0.56    ( ! [X2,X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,X2,k15_lattice3(sK0,X1)) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f288,f54])).
% 1.42/0.56  fof(f288,plain,(
% 1.42/0.56    ( ! [X2,X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,X2,k15_lattice3(sK0,X1)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(duplicate_literal_removal,[],[f284])).
% 1.42/0.56  fof(f284,plain,(
% 1.42/0.56    ( ! [X2,X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,X2,k15_lattice3(sK0,X1)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(resolution,[],[f196,f69])).
% 1.42/0.56  fof(f69,plain,(
% 1.42/0.56    ( ! [X4,X2,X0,X1] : (~r4_lattice3(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_lattices(X0,X4,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f41])).
% 1.42/0.56  fof(f196,plain,(
% 1.42/0.56    ( ! [X1] : (r4_lattice3(sK0,k15_lattice3(sK0,X1),a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f195,f51])).
% 1.42/0.56  fof(f195,plain,(
% 1.42/0.56    ( ! [X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | r4_lattice3(sK0,k15_lattice3(sK0,X1),a_2_5_lattice3(sK0,X1)) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f194,f52])).
% 1.42/0.56  fof(f194,plain,(
% 1.42/0.56    ( ! [X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | r4_lattice3(sK0,k15_lattice3(sK0,X1),a_2_5_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f193,f53])).
% 1.42/0.56  fof(f193,plain,(
% 1.42/0.56    ( ! [X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | r4_lattice3(sK0,k15_lattice3(sK0,X1),a_2_5_lattice3(sK0,X1)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f190,f54])).
% 1.42/0.56  fof(f190,plain,(
% 1.42/0.56    ( ! [X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | r4_lattice3(sK0,k15_lattice3(sK0,X1),a_2_5_lattice3(sK0,X1)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(superposition,[],[f92,f98])).
% 1.42/0.56  fof(f98,plain,(
% 1.42/0.56    ( ! [X0] : (k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))) )),
% 1.42/0.56    inference(global_subsumption,[],[f54,f97])).
% 1.42/0.56  fof(f97,plain,(
% 1.42/0.56    ( ! [X0] : (~l3_lattices(sK0) | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f96,f51])).
% 1.42/0.56  fof(f96,plain,(
% 1.42/0.56    ( ! [X0] : (~l3_lattices(sK0) | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f93,f52])).
% 1.42/0.56  fof(f93,plain,(
% 1.42/0.56    ( ! [X0] : (~l3_lattices(sK0) | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(resolution,[],[f53,f60])).
% 1.42/0.56  fof(f60,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~v4_lattice3(X0) | ~l3_lattices(X0) | k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f16])).
% 1.42/0.56  fof(f16,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(flattening,[],[f15])).
% 1.42/0.56  fof(f15,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f8])).
% 1.42/0.56  fof(f8,axiom,(
% 1.42/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).
% 1.42/0.56  fof(f92,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.56    inference(duplicate_literal_removal,[],[f85])).
% 1.42/0.56  fof(f85,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.56    inference(equality_resolution,[],[f64])).
% 1.42/0.56  fof(f64,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f37])).
% 1.42/0.56  fof(f37,plain,(
% 1.42/0.56    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK4(X0,X1,X2)) & r4_lattice3(X0,sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 1.42/0.56  fof(f36,plain,(
% 1.42/0.56    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK4(X0,X1,X2)) & r4_lattice3(X0,sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f35,plain,(
% 1.42/0.56    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(rectify,[],[f34])).
% 1.42/0.56  fof(f34,plain,(
% 1.42/0.56    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(flattening,[],[f33])).
% 1.42/0.56  fof(f33,plain,(
% 1.42/0.56    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(nnf_transformation,[],[f20])).
% 1.42/0.56  fof(f20,plain,(
% 1.42/0.56    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(flattening,[],[f19])).
% 1.42/0.56  fof(f19,plain,(
% 1.42/0.56    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f2])).
% 1.42/0.56  fof(f2,axiom,(
% 1.42/0.56    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 1.42/0.56  fof(f716,plain,(
% 1.42/0.56    ~spl9_9 | spl9_10 | ~spl9_15 | ~spl9_16 | spl9_26),
% 1.42/0.56    inference(avatar_contradiction_clause,[],[f715])).
% 1.42/0.56  fof(f715,plain,(
% 1.42/0.56    $false | (~spl9_9 | spl9_10 | ~spl9_15 | ~spl9_16 | spl9_26)),
% 1.42/0.56    inference(subsumption_resolution,[],[f714,f566])).
% 1.42/0.56  fof(f566,plain,(
% 1.42/0.56    r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | ~spl9_15),
% 1.42/0.56    inference(avatar_component_clause,[],[f565])).
% 1.42/0.56  fof(f565,plain,(
% 1.42/0.56    spl9_15 <=> r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)),
% 1.42/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.42/0.56  fof(f714,plain,(
% 1.42/0.56    ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | (~spl9_9 | spl9_10 | ~spl9_16 | spl9_26)),
% 1.42/0.56    inference(subsumption_resolution,[],[f713,f572])).
% 1.42/0.56  fof(f572,plain,(
% 1.42/0.56    r2_hidden(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) | ~spl9_16),
% 1.42/0.56    inference(avatar_component_clause,[],[f570])).
% 1.42/0.56  fof(f570,plain,(
% 1.42/0.56    spl9_16 <=> r2_hidden(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)),
% 1.42/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 1.42/0.56  fof(f713,plain,(
% 1.42/0.56    ~r2_hidden(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) | ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | (~spl9_9 | spl9_10 | spl9_26)),
% 1.42/0.56    inference(subsumption_resolution,[],[f712,f545])).
% 1.42/0.56  fof(f545,plain,(
% 1.42/0.56    m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | (~spl9_9 | spl9_10)),
% 1.42/0.56    inference(resolution,[],[f498,f341])).
% 1.42/0.56  fof(f498,plain,(
% 1.42/0.56    ( ! [X1] : (r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1)) | m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0))) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f497,f51])).
% 1.42/0.56  fof(f497,plain,(
% 1.42/0.56    ( ! [X1] : (m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0)) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1)) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f496,f52])).
% 1.42/0.56  fof(f496,plain,(
% 1.42/0.56    ( ! [X1] : (m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0)) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f495,f53])).
% 1.42/0.56  fof(f495,plain,(
% 1.42/0.56    ( ! [X1] : (m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0)) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f494,f54])).
% 1.42/0.56  fof(f494,plain,(
% 1.42/0.56    ( ! [X1] : (m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0)) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f490,f336])).
% 1.42/0.56  fof(f490,plain,(
% 1.42/0.56    ( ! [X1] : (m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),X1),u1_struct_0(sK0)) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(resolution,[],[f370,f86])).
% 1.42/0.56  fof(f712,plain,(
% 1.42/0.56    ~m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | ~r2_hidden(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) | ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | spl9_26),
% 1.42/0.56    inference(resolution,[],[f703,f188])).
% 1.42/0.56  fof(f188,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK3(X0),X1) | ~r2_hidden(X0,sK1)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f187,f55])).
% 1.42/0.56  fof(f55,plain,(
% 1.42/0.56    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1) | m1_subset_1(sK3(X3),u1_struct_0(sK0))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f32])).
% 1.42/0.56  fof(f187,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK3(X0),X1) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0))) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f186,f51])).
% 1.42/0.56  fof(f186,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK3(X0),X1) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f185,f52])).
% 1.42/0.56  fof(f185,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK3(X0),X1) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f184,f53])).
% 1.42/0.56  fof(f184,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK3(X0),X1) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f183,f54])).
% 1.42/0.56  fof(f183,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK3(X0),X1) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(duplicate_literal_removal,[],[f182])).
% 1.42/0.56  fof(f182,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK3(X0),X1) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(resolution,[],[f56,f87])).
% 1.42/0.56  fof(f87,plain,(
% 1.42/0.56    ( ! [X4,X2,X3,X1] : (~r3_lattices(X1,X3,X4) | ~r2_hidden(X4,X2) | r2_hidden(X3,a_2_5_lattice3(X1,X2)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.42/0.56    inference(equality_resolution,[],[f83])).
% 1.42/0.56  fof(f83,plain,(
% 1.42/0.56    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f50])).
% 1.42/0.56  fof(f50,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (((r2_hidden(sK8(X0,X1,X2),X2) & r3_lattices(X1,sK7(X0,X1,X2),sK8(X0,X1,X2)) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))) & sK7(X0,X1,X2) = X0 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f47,f49,f48])).
% 1.42/0.56  fof(f48,plain,(
% 1.42/0.56    ! [X2,X1,X0] : (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,sK7(X0,X1,X2),X6) & m1_subset_1(X6,u1_struct_0(X1))) & sK7(X0,X1,X2) = X0 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f49,plain,(
% 1.42/0.56    ! [X2,X1,X0] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,sK7(X0,X1,X2),X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(sK8(X0,X1,X2),X2) & r3_lattices(X1,sK7(X0,X1,X2),sK8(X0,X1,X2)) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f47,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.42/0.56    inference(rectify,[],[f46])).
% 1.42/0.56  fof(f46,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.42/0.56    inference(nnf_transformation,[],[f28])).
% 1.42/0.56  fof(f28,plain,(
% 1.42/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.42/0.56    inference(flattening,[],[f27])).
% 1.42/0.56  fof(f27,plain,(
% 1.42/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 1.42/0.56    inference(ennf_transformation,[],[f5])).
% 1.42/0.56  fof(f5,axiom,(
% 1.42/0.56    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).
% 1.42/0.56  fof(f56,plain,(
% 1.42/0.56    ( ! [X3] : (r3_lattices(sK0,X3,sK3(X3)) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f32])).
% 1.42/0.56  fof(f703,plain,(
% 1.42/0.56    ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2)) | spl9_26),
% 1.42/0.56    inference(avatar_component_clause,[],[f701])).
% 1.42/0.56  fof(f587,plain,(
% 1.42/0.56    ~spl9_9 | spl9_10 | spl9_15),
% 1.42/0.56    inference(avatar_contradiction_clause,[],[f586])).
% 1.42/0.56  fof(f586,plain,(
% 1.42/0.56    $false | (~spl9_9 | spl9_10 | spl9_15)),
% 1.42/0.56    inference(subsumption_resolution,[],[f585,f341])).
% 1.42/0.56  fof(f585,plain,(
% 1.42/0.56    r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1)) | (~spl9_9 | spl9_15)),
% 1.42/0.56    inference(resolution,[],[f567,f464])).
% 1.42/0.56  fof(f464,plain,(
% 1.42/0.56    ( ! [X1] : (r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X1),X1) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1))) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f463,f51])).
% 1.42/0.56  fof(f463,plain,(
% 1.42/0.56    ( ! [X1] : (r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X1),X1) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1)) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f462,f52])).
% 1.42/0.56  fof(f462,plain,(
% 1.42/0.56    ( ! [X1] : (r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X1),X1) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f461,f53])).
% 1.42/0.56  fof(f461,plain,(
% 1.42/0.56    ( ! [X1] : (r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X1),X1) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f460,f54])).
% 1.42/0.56  fof(f460,plain,(
% 1.42/0.56    ( ! [X1] : (r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X1),X1) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f456,f336])).
% 1.42/0.56  fof(f456,plain,(
% 1.42/0.56    ( ! [X1] : (r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X1),X1) | r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,X1)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(resolution,[],[f372,f86])).
% 1.42/0.56  fof(f372,plain,(
% 1.42/0.56    ( ! [X2] : (r4_lattice3(sK0,k15_lattice3(sK0,sK2),X2) | r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X2),X2)) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f371,f51])).
% 1.42/0.56  fof(f371,plain,(
% 1.42/0.56    ( ! [X2] : (r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X2),X2) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X2) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f360,f54])).
% 1.42/0.56  fof(f360,plain,(
% 1.42/0.56    ( ! [X2] : (r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),X2),X2) | r4_lattice3(sK0,k15_lattice3(sK0,sK2),X2) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl9_9),
% 1.42/0.56    inference(resolution,[],[f336,f71])).
% 1.42/0.56  fof(f71,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(sK5(X0,X1,X2),X2) | r4_lattice3(X0,X1,X2) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f41])).
% 1.42/0.56  fof(f567,plain,(
% 1.42/0.56    ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | spl9_15),
% 1.42/0.56    inference(avatar_component_clause,[],[f565])).
% 1.42/0.56  fof(f573,plain,(
% 1.42/0.56    spl9_16 | ~spl9_15 | ~spl9_9 | spl9_10),
% 1.42/0.56    inference(avatar_split_clause,[],[f557,f339,f335,f565,f570])).
% 1.42/0.56  fof(f557,plain,(
% 1.42/0.56    ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | r2_hidden(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) | (~spl9_9 | spl9_10)),
% 1.42/0.56    inference(resolution,[],[f545,f57])).
% 1.42/0.56  fof(f57,plain,(
% 1.42/0.56    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1) | r2_hidden(sK3(X3),sK2)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f32])).
% 1.42/0.56  fof(f350,plain,(
% 1.42/0.56    spl9_9),
% 1.42/0.56    inference(avatar_contradiction_clause,[],[f349])).
% 1.42/0.56  fof(f349,plain,(
% 1.42/0.56    $false | spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f348,f51])).
% 1.42/0.56  fof(f348,plain,(
% 1.42/0.56    v2_struct_0(sK0) | spl9_9),
% 1.42/0.56    inference(subsumption_resolution,[],[f347,f54])).
% 1.42/0.56  fof(f347,plain,(
% 1.42/0.56    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl9_9),
% 1.42/0.56    inference(resolution,[],[f337,f73])).
% 1.42/0.56  fof(f73,plain,(
% 1.42/0.56    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f24])).
% 1.42/0.56  fof(f24,plain,(
% 1.42/0.56    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(flattening,[],[f23])).
% 1.42/0.56  fof(f23,plain,(
% 1.42/0.56    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f3])).
% 1.42/0.56  fof(f3,axiom,(
% 1.42/0.56    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 1.42/0.56  fof(f337,plain,(
% 1.42/0.56    ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | spl9_9),
% 1.42/0.56    inference(avatar_component_clause,[],[f335])).
% 1.42/0.56  fof(f342,plain,(
% 1.42/0.56    ~spl9_9 | ~spl9_10),
% 1.42/0.56    inference(avatar_split_clause,[],[f330,f339,f335])).
% 1.42/0.56  fof(f330,plain,(
% 1.42/0.56    ~r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))),
% 1.42/0.56    inference(resolution,[],[f214,f58])).
% 1.42/0.56  fof(f58,plain,(
% 1.42/0.56    ~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))),
% 1.42/0.56    inference(cnf_transformation,[],[f32])).
% 1.42/0.56  fof(f214,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r3_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f213,f51])).
% 1.42/0.56  fof(f213,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r3_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f212,f52])).
% 1.42/0.56  fof(f212,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r3_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f211,f53])).
% 1.42/0.56  fof(f211,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r3_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f210,f54])).
% 1.42/0.56  fof(f210,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r3_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(superposition,[],[f63,f104])).
% 1.42/0.56  fof(f104,plain,(
% 1.42/0.56    ( ! [X2] : (k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2))) )),
% 1.42/0.56    inference(global_subsumption,[],[f54,f103])).
% 1.42/0.56  fof(f103,plain,(
% 1.42/0.56    ( ! [X2] : (~l3_lattices(sK0) | k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2))) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f102,f51])).
% 1.42/0.56  fof(f102,plain,(
% 1.42/0.56    ( ! [X2] : (~l3_lattices(sK0) | k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2)) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f95,f52])).
% 1.42/0.56  fof(f95,plain,(
% 1.42/0.56    ( ! [X2] : (~l3_lattices(sK0) | k15_lattice3(sK0,X2) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X2)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.42/0.56    inference(resolution,[],[f53,f59])).
% 1.42/0.56  fof(f59,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~v4_lattice3(X0) | ~l3_lattices(X0) | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f14])).
% 1.42/0.56  fof(f14,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(flattening,[],[f13])).
% 1.42/0.56  fof(f13,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f6])).
% 1.42/0.56  fof(f6,axiom,(
% 1.42/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).
% 1.42/0.56  fof(f63,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f18])).
% 1.42/0.56  fof(f18,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.42/0.56    inference(flattening,[],[f17])).
% 1.42/0.56  fof(f17,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f7])).
% 1.42/0.56  fof(f7,axiom,(
% 1.42/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).
% 1.42/0.56  % SZS output end Proof for theBenchmark
% 1.42/0.56  % (23709)------------------------------
% 1.42/0.56  % (23709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (23709)Termination reason: Refutation
% 1.42/0.56  
% 1.42/0.56  % (23709)Memory used [KB]: 11001
% 1.42/0.56  % (23709)Time elapsed: 0.147 s
% 1.42/0.56  % (23709)------------------------------
% 1.42/0.56  % (23709)------------------------------
% 1.42/0.56  % (23707)Success in time 0.199 s
%------------------------------------------------------------------------------
