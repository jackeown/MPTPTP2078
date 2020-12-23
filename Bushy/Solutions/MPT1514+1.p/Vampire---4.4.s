%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattice3__t48_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:55 EDT 2019

% Result     : Theorem 0.96s
% Output     : Refutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :  174 (1222 expanded)
%              Number of leaves         :   26 ( 407 expanded)
%              Depth                    :   27
%              Number of atoms          : 1001 (10460 expanded)
%              Number of equality atoms :   12 (  60 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3463,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1750,f1787,f2920,f3054,f3060,f3085,f3454,f3462])).

fof(f3462,plain,
    ( ~ spl13_18
    | ~ spl13_92
    | ~ spl13_98
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f3461])).

fof(f3461,plain,
    ( $false
    | ~ spl13_18
    | ~ spl13_92
    | ~ spl13_98
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f3460,f1892])).

fof(f1892,plain,
    ( ~ r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)
    | ~ spl13_92
    | ~ spl13_98 ),
    inference(subsumption_resolution,[],[f1891,f1725])).

fof(f1725,plain,
    ( m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_92 ),
    inference(avatar_component_clause,[],[f1724])).

fof(f1724,plain,
    ( spl13_92
  <=> m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_92])])).

fof(f1891,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)
    | ~ spl13_98 ),
    inference(subsumption_resolution,[],[f1890,f1774])).

fof(f1774,plain,
    ( m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl13_98 ),
    inference(avatar_component_clause,[],[f1773])).

fof(f1773,plain,
    ( spl13_98
  <=> m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_98])])).

fof(f1890,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1) ),
    inference(resolution,[],[f1684,f104])).

fof(f104,plain,(
    ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f68,f67,f66])).

fof(f66,plain,
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

fof(f67,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
     => ( ~ r3_lattices(X0,k15_lattice3(X0,sK1),k15_lattice3(X0,sK2))
        & ! [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,sK2)
                & r3_lattices(X0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_hidden(X3,sK1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,X2)
          & r3_lattices(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r2_hidden(sK3(X3),X2)
        & r3_lattices(X0,X3,sK3(X3))
        & m1_subset_1(sK3(X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',t48_lattice3)).

fof(f1684,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f1681])).

fof(f1681,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
      | r3_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X1,X0) ) ),
    inference(resolution,[],[f434,f454])).

fof(f454,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f453,f97])).

fof(f97,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f453,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f452,f98])).

fof(f98,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f452,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f451,f100])).

fof(f100,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f451,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f450,f99])).

fof(f99,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f450,plain,(
    ! [X4,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f156,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',dt_k15_lattice3)).

fof(f156,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X2,X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f72,f73])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
        & r4_lattice3(X0,sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
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
    inference(rectify,[],[f71])).

fof(f71,plain,(
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
    inference(flattening,[],[f70])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',d21_lattice3)).

fof(f434,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f433,f97])).

fof(f433,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f432,f100])).

fof(f432,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r3_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f421,f98])).

fof(f421,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f420,f116])).

fof(f116,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',cc1_lattices)).

fof(f420,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f419,f114])).

fof(f114,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f419,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f418])).

fof(f418,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f142,f117])).

fof(f117,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
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
    inference(nnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',redefinition_r3_lattices)).

fof(f3460,plain,
    ( r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)
    | ~ spl13_18
    | ~ spl13_92
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f3459,f2919])).

fof(f2919,plain,
    ( m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ spl13_138 ),
    inference(avatar_component_clause,[],[f2918])).

fof(f2918,plain,
    ( spl13_138
  <=> m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_138])])).

fof(f3459,plain,
    ( ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)
    | ~ spl13_18
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f3458,f1725])).

fof(f3458,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)
    | ~ spl13_18 ),
    inference(resolution,[],[f465,f1680])).

fof(f1680,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,sK5(sK0,X0,X1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
      | r4_lattice3(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f1679,f97])).

fof(f1679,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,sK5(sK0,X0,X1),X0)
      | r4_lattice3(sK0,X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1678,f100])).

fof(f1678,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,sK5(sK0,X0,X1),X0)
      | r4_lattice3(sK0,X0,X1)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1677])).

fof(f1677,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,sK5(sK0,X0,X1),X0)
      | r4_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f424,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f76,f77])).

fof(f77,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),X2)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
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
    inference(rectify,[],[f75])).

fof(f75,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',d17_lattice3)).

fof(f424,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f423,f97])).

fof(f423,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f422,f100])).

fof(f422,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f417,f98])).

fof(f417,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f416,f116])).

fof(f416,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f415,f114])).

fof(f415,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f414])).

fof(f414,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f141,f117])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f465,plain,
    ( r3_lattices(sK0,sK5(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2))
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f464])).

fof(f464,plain,
    ( spl13_18
  <=> r3_lattices(sK0,sK5(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f3454,plain,
    ( spl13_19
    | ~ spl13_92
    | ~ spl13_98
    | ~ spl13_134
    | ~ spl13_138
    | ~ spl13_146 ),
    inference(avatar_contradiction_clause,[],[f3453])).

fof(f3453,plain,
    ( $false
    | ~ spl13_19
    | ~ spl13_92
    | ~ spl13_98
    | ~ spl13_134
    | ~ spl13_138
    | ~ spl13_146 ),
    inference(subsumption_resolution,[],[f3452,f2919])).

fof(f3452,plain,
    ( ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ spl13_19
    | ~ spl13_92
    | ~ spl13_98
    | ~ spl13_134
    | ~ spl13_138
    | ~ spl13_146 ),
    inference(subsumption_resolution,[],[f3451,f1900])).

fof(f1900,plain,
    ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ spl13_92
    | ~ spl13_98 ),
    inference(subsumption_resolution,[],[f1899,f97])).

fof(f1899,plain,
    ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | v2_struct_0(sK0)
    | ~ spl13_92
    | ~ spl13_98 ),
    inference(subsumption_resolution,[],[f1898,f100])).

fof(f1898,plain,
    ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_92
    | ~ spl13_98 ),
    inference(subsumption_resolution,[],[f1894,f1725])).

fof(f1894,plain,
    ( r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_92
    | ~ spl13_98 ),
    inference(resolution,[],[f1892,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f3451,plain,
    ( ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ spl13_19
    | ~ spl13_92
    | ~ spl13_134
    | ~ spl13_138
    | ~ spl13_146 ),
    inference(subsumption_resolution,[],[f3450,f3050])).

fof(f3050,plain,
    ( m1_subset_1(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),u1_struct_0(sK0))
    | ~ spl13_146 ),
    inference(avatar_component_clause,[],[f3049])).

fof(f3049,plain,
    ( spl13_146
  <=> m1_subset_1(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_146])])).

fof(f3450,plain,
    ( ~ m1_subset_1(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ spl13_19
    | ~ spl13_92
    | ~ spl13_134
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f3442,f2876])).

fof(f2876,plain,
    ( r3_lattices(sK0,sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),k15_lattice3(sK0,sK2))
    | ~ spl13_134 ),
    inference(avatar_component_clause,[],[f2875])).

fof(f2875,plain,
    ( spl13_134
  <=> r3_lattices(sK0,sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_134])])).

fof(f3442,plain,
    ( ~ r3_lattices(sK0,sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),k15_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ spl13_19
    | ~ spl13_92
    | ~ spl13_138 ),
    inference(resolution,[],[f3257,f102])).

fof(f102,plain,(
    ! [X3] :
      ( r3_lattices(sK0,X3,sK3(X3))
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f3257,plain,
    ( ! [X1] :
        ( ~ r3_lattices(sK0,sK5(sK0,k15_lattice3(sK0,sK2),sK1),X1)
        | ~ r3_lattices(sK0,X1,k15_lattice3(sK0,sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_19
    | ~ spl13_92
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f3256,f2919])).

fof(f3256,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,k15_lattice3(sK0,sK2))
        | ~ r3_lattices(sK0,sK5(sK0,k15_lattice3(sK0,sK2),sK1),X1) )
    | ~ spl13_19
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f3249,f1725])).

fof(f3249,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,k15_lattice3(sK0,sK2))
        | ~ r3_lattices(sK0,sK5(sK0,k15_lattice3(sK0,sK2),sK1),X1) )
    | ~ spl13_19 ),
    inference(resolution,[],[f3243,f468])).

fof(f468,plain,
    ( ~ r3_lattices(sK0,sK5(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2))
    | ~ spl13_19 ),
    inference(avatar_component_clause,[],[f467])).

fof(f467,plain,
    ( spl13_19
  <=> ~ r3_lattices(sK0,sK5(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f3243,plain,(
    ! [X12,X13,X11] :
      ( r3_lattices(sK0,X11,X13)
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X12,X13)
      | ~ r3_lattices(sK0,X11,X12) ) ),
    inference(duplicate_literal_removal,[],[f3242])).

fof(f3242,plain,(
    ! [X12,X13,X11] :
      ( ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | r3_lattices(sK0,X11,X13)
      | ~ r3_lattices(sK0,X12,X13)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X11,X12) ) ),
    inference(resolution,[],[f3235,f424])).

fof(f3235,plain,(
    ! [X12,X13,X11] :
      ( ~ r1_lattices(sK0,X12,X11)
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | r3_lattices(sK0,X12,X13)
      | ~ r3_lattices(sK0,X11,X13) ) ),
    inference(duplicate_literal_removal,[],[f3234])).

fof(f3234,plain,(
    ! [X12,X13,X11] :
      ( ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ r1_lattices(sK0,X12,X11)
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | r3_lattices(sK0,X12,X13)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X11,X13) ) ),
    inference(resolution,[],[f3227,f424])).

fof(f3227,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_lattices(sK0,X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_lattices(sK0,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f3222])).

fof(f3222,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_lattices(sK0,X2,X1)
      | ~ r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r3_lattices(sK0,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f780,f434])).

fof(f780,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(sK0,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattices(sK0,X0,X1)
      | ~ r1_lattices(sK0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f779,f100])).

fof(f779,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X2)
      | ~ r1_lattices(sK0,X1,X2)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f778,f97])).

fof(f778,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X2)
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X2)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f666,f98])).

fof(f666,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v10_lattices(X0)
      | ~ r1_lattices(X0,X3,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_lattices(X0,X3,X2)
      | v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ l3_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f665,f110])).

fof(f110,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',dt_l3_lattices)).

fof(f665,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X3,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | r1_lattices(X0,X3,X2)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f664])).

fof(f664,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X3,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | r1_lattices(X0,X3,X2)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f118,f113])).

fof(f113,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_lattices(X0)
      | ~ r1_lattices(X0,X2,X3)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | r1_lattices(X0,X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r1_lattices(X0,X2,X3)
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r1_lattices(X0,X2,X3)
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_lattices(X0,X2,X3)
                      & r1_lattices(X0,X1,X2) )
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',t25_lattices)).

fof(f3085,plain,
    ( ~ spl13_92
    | ~ spl13_98
    | ~ spl13_138
    | spl13_147 ),
    inference(avatar_contradiction_clause,[],[f3084])).

fof(f3084,plain,
    ( $false
    | ~ spl13_92
    | ~ spl13_98
    | ~ spl13_138
    | ~ spl13_147 ),
    inference(subsumption_resolution,[],[f3083,f2919])).

fof(f3083,plain,
    ( ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ spl13_92
    | ~ spl13_98
    | ~ spl13_147 ),
    inference(subsumption_resolution,[],[f3081,f1900])).

fof(f3081,plain,
    ( ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ spl13_147 ),
    inference(resolution,[],[f3053,f101])).

fof(f101,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(X3),u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f3053,plain,
    ( ~ m1_subset_1(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),u1_struct_0(sK0))
    | ~ spl13_147 ),
    inference(avatar_component_clause,[],[f3052])).

fof(f3052,plain,
    ( spl13_147
  <=> ~ m1_subset_1(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_147])])).

fof(f3060,plain,
    ( ~ spl13_92
    | ~ spl13_98
    | ~ spl13_138
    | spl13_145 ),
    inference(avatar_contradiction_clause,[],[f3059])).

fof(f3059,plain,
    ( $false
    | ~ spl13_92
    | ~ spl13_98
    | ~ spl13_138
    | ~ spl13_145 ),
    inference(subsumption_resolution,[],[f3058,f2919])).

fof(f3058,plain,
    ( ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ spl13_92
    | ~ spl13_98
    | ~ spl13_145 ),
    inference(subsumption_resolution,[],[f3055,f1900])).

fof(f3055,plain,
    ( ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ spl13_145 ),
    inference(resolution,[],[f3047,f103])).

fof(f103,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f3047,plain,
    ( ~ r2_hidden(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)
    | ~ spl13_145 ),
    inference(avatar_component_clause,[],[f3046])).

fof(f3046,plain,
    ( spl13_145
  <=> ~ r2_hidden(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_145])])).

fof(f3054,plain,
    ( ~ spl13_145
    | ~ spl13_147
    | spl13_135 ),
    inference(avatar_split_clause,[],[f3041,f2878,f3052,f3046])).

fof(f2878,plain,
    ( spl13_135
  <=> ~ r3_lattices(sK0,sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_135])])).

fof(f3041,plain,
    ( ~ m1_subset_1(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),u1_struct_0(sK0))
    | ~ r2_hidden(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)
    | ~ spl13_135 ),
    inference(resolution,[],[f385,f2879])).

fof(f2879,plain,
    ( ~ r3_lattices(sK0,sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),k15_lattice3(sK0,sK2))
    | ~ spl13_135 ),
    inference(avatar_component_clause,[],[f2878])).

fof(f385,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f384,f97])).

fof(f384,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f383,f98])).

fof(f383,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f382,f100])).

fof(f382,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r3_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f119,f99])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattice3__t48_lattice3.p',t38_lattice3)).

fof(f2920,plain,
    ( ~ spl13_93
    | spl13_138
    | ~ spl13_92
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f2470,f1773,f1724,f2918,f1727])).

fof(f1727,plain,
    ( spl13_93
  <=> ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_93])])).

fof(f2470,plain,
    ( m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_92
    | ~ spl13_98 ),
    inference(subsumption_resolution,[],[f2469,f97])).

fof(f2469,plain,
    ( m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl13_92
    | ~ spl13_98 ),
    inference(subsumption_resolution,[],[f2467,f100])).

fof(f2467,plain,
    ( m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_92
    | ~ spl13_98 ),
    inference(resolution,[],[f1892,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f1787,plain,(
    spl13_99 ),
    inference(avatar_contradiction_clause,[],[f1786])).

fof(f1786,plain,
    ( $false
    | ~ spl13_99 ),
    inference(subsumption_resolution,[],[f1785,f97])).

fof(f1785,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_99 ),
    inference(subsumption_resolution,[],[f1782,f100])).

fof(f1782,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_99 ),
    inference(resolution,[],[f1777,f134])).

fof(f1777,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl13_99 ),
    inference(avatar_component_clause,[],[f1776])).

fof(f1776,plain,
    ( spl13_99
  <=> ~ m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_99])])).

fof(f1750,plain,(
    spl13_93 ),
    inference(avatar_contradiction_clause,[],[f1749])).

fof(f1749,plain,
    ( $false
    | ~ spl13_93 ),
    inference(subsumption_resolution,[],[f1748,f97])).

fof(f1748,plain,
    ( v2_struct_0(sK0)
    | ~ spl13_93 ),
    inference(subsumption_resolution,[],[f1745,f100])).

fof(f1745,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_93 ),
    inference(resolution,[],[f1728,f134])).

fof(f1728,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_93 ),
    inference(avatar_component_clause,[],[f1727])).
%------------------------------------------------------------------------------
