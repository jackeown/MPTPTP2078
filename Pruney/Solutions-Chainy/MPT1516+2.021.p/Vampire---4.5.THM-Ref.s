%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  236 ( 675 expanded)
%              Number of leaves         :   41 ( 185 expanded)
%              Depth                    :   29
%              Number of atoms          : 1185 (4719 expanded)
%              Number of equality atoms :  160 ( 558 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f471,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f158,f162,f272,f331,f336,f341,f360,f365,f391,f401,f432,f442,f464,f470])).

fof(f470,plain,(
    ~ spl11_1 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f141,f82])).

fof(f82,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f49])).

% (7023)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (7007)Refutation not found, incomplete strategy% (7007)------------------------------
% (7007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7007)Termination reason: Refutation not found, incomplete strategy

% (7007)Memory used [KB]: 10618
% (7007)Time elapsed: 0.005 s
% (7007)------------------------------
% (7007)------------------------------
fof(f49,plain,
    ( ? [X0] :
        ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
          | ~ l3_lattices(X0)
          | ~ v13_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
        | ~ l3_lattices(sK0)
        | ~ v13_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
          & l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(f141,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl11_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f464,plain,
    ( spl11_5
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_18 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | spl11_5
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f462,f351])).

fof(f351,plain,
    ( m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl11_13
  <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f462,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl11_5
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f461,f424])).

fof(f424,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl11_17
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f461,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl11_5
    | ~ spl11_15
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f452,f157])).

fof(f157,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl11_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f452,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl11_15
    | ~ spl11_18 ),
    inference(superposition,[],[f359,f428])).

fof(f428,plain,
    ( ! [X1] :
        ( k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f427])).

fof(f427,plain,
    ( spl11_18
  <=> ! [X1] :
        ( k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f359,plain,
    ( ! [X1] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl11_15
  <=> ! [X1] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f442,plain,
    ( ~ spl11_8
    | spl11_17 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | ~ spl11_8
    | spl11_17 ),
    inference(subsumption_resolution,[],[f440,f82])).

fof(f440,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_8
    | spl11_17 ),
    inference(subsumption_resolution,[],[f438,f253])).

fof(f253,plain,
    ( l1_lattices(sK0)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl11_8
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f438,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl11_17 ),
    inference(resolution,[],[f425,f100])).

fof(f100,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f425,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl11_17 ),
    inference(avatar_component_clause,[],[f423])).

fof(f432,plain,
    ( ~ spl11_17
    | spl11_18
    | ~ spl11_3
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f418,f252,f147,f427,f423])).

fof(f147,plain,
    ( spl11_3
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f418,plain,
    ( ! [X1] :
        ( k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) )
    | ~ spl11_3
    | ~ spl11_8 ),
    inference(duplicate_literal_removal,[],[f417])).

fof(f417,plain,
    ( ! [X1] :
        ( k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_3
    | ~ spl11_8 ),
    inference(superposition,[],[f237,f407])).

fof(f407,plain,
    ( ! [X0] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_3
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f406,f253])).

fof(f406,plain,
    ( ! [X0] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_lattices(sK0) )
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f402,f82])).

fof(f402,plain,
    ( ! [X0] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_lattices(sK0) )
    | ~ spl11_3 ),
    inference(resolution,[],[f148,f160])).

fof(f160,plain,(
    ! [X0,X3] :
      ( ~ v13_lattices(X0)
      | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_lattices(X0) ) ),
    inference(global_subsumption,[],[f100,f136])).

fof(f136,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(f148,plain,
    ( v13_lattices(sK0)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f147])).

fof(f237,plain,(
    ! [X0,X1] :
      ( k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f236,f85])).

fof(f85,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f235,f82])).

fof(f235,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f234,f83])).

fof(f83,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f222,f93])).

fof(f93,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f110,f88])).

fof(f88,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f110,plain,(
    ! [X4,X0,X3] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f62,f64,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

fof(f401,plain,(
    spl11_4 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | spl11_4 ),
    inference(subsumption_resolution,[],[f153,f85])).

fof(f153,plain,
    ( ~ l3_lattices(sK0)
    | spl11_4 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl11_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f391,plain,
    ( spl11_3
    | ~ spl11_8
    | ~ spl11_13
    | ~ spl11_15 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | spl11_3
    | ~ spl11_8
    | ~ spl11_13
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f389,f82])).

fof(f389,plain,
    ( v2_struct_0(sK0)
    | spl11_3
    | ~ spl11_8
    | ~ spl11_13
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f388,f253])).

fof(f388,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl11_3
    | ~ spl11_8
    | ~ spl11_13
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f387,f351])).

fof(f387,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl11_3
    | ~ spl11_8
    | ~ spl11_13
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f385,f149])).

fof(f149,plain,
    ( ~ v13_lattices(sK0)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f147])).

fof(f385,plain,
    ( v13_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl11_3
    | ~ spl11_8
    | ~ spl11_13
    | ~ spl11_15 ),
    inference(resolution,[],[f384,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( ! [X4] :
                ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
                  & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f57,f59,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( k2_lattices(X0,X4,X3) = X3
                & k2_lattices(X0,X3,X4) = X3 )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
              & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( ( k2_lattices(X0,X4,X3) = X3
                    & k2_lattices(X0,X3,X4) = X3 )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

fof(f384,plain,
    ( ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl11_3
    | ~ spl11_8
    | ~ spl11_13
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f375,f351])).

fof(f375,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl11_3
    | ~ spl11_8
    | ~ spl11_15 ),
    inference(trivial_inequality_removal,[],[f374])).

fof(f374,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl11_3
    | ~ spl11_8
    | ~ spl11_15 ),
    inference(superposition,[],[f304,f359])).

fof(f304,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl11_3
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f303,f82])).

fof(f303,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | v2_struct_0(sK0) )
    | spl11_3
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f302,f253])).

fof(f302,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl11_3
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f301,f149])).

fof(f301,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl11_3
    | ~ spl11_8 ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | v13_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl11_3
    | ~ spl11_8 ),
    inference(resolution,[],[f297,f108])).

fof(f297,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,sK2(sK0,X1)) != X1 )
    | spl11_3
    | ~ spl11_8 ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,
    ( ! [X1] :
        ( k2_lattices(sK0,X1,sK2(sK0,X1)) != X1
        | k2_lattices(sK0,X1,sK2(sK0,X1)) != X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,X1),u1_struct_0(sK0)) )
    | spl11_3
    | ~ spl11_8 ),
    inference(superposition,[],[f294,f237])).

fof(f294,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,sK2(sK0,X0),X0) != X0
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl11_3
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f293,f149])).

fof(f293,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,sK2(sK0,X0),X0) != X0
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v13_lattices(sK0) )
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f292,f253])).

fof(f292,plain,(
    ! [X0] :
      ( k2_lattices(sK0,sK2(sK0,X0),X0) != X0
      | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v13_lattices(sK0) ) ),
    inference(resolution,[],[f109,f82])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | k2_lattices(X0,sK2(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f365,plain,(
    spl11_13 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | spl11_13 ),
    inference(subsumption_resolution,[],[f363,f82])).

fof(f363,plain,
    ( v2_struct_0(sK0)
    | spl11_13 ),
    inference(subsumption_resolution,[],[f361,f85])).

fof(f361,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl11_13 ),
    inference(resolution,[],[f352,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f352,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl11_13 ),
    inference(avatar_component_clause,[],[f350])).

fof(f360,plain,
    ( ~ spl11_13
    | spl11_15
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f348,f329,f358,f350])).

fof(f329,plain,
    ( spl11_12
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = X0
        | ~ r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f348,plain,
    ( ! [X1] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)
        | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_12 ),
    inference(duplicate_literal_removal,[],[f345])).

fof(f345,plain,
    ( ! [X1] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)
        | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_12 ),
    inference(resolution,[],[f330,f217])).

fof(f217,plain,(
    ! [X1] :
      ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f215,f181])).

fof(f181,plain,(
    ! [X0] :
      ( k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f180,f82])).

fof(f180,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f179,f83])).

fof(f179,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f178,f85])).

fof(f178,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f116,f84])).

fof(f84,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).

fof(f215,plain,(
    ! [X2] : r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X2)) ),
    inference(resolution,[],[f213,f196])).

fof(f196,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f188,f191])).

fof(f191,plain,(
    k1_xboole_0 = a_2_5_lattice3(sK0,k1_xboole_0) ),
    inference(resolution,[],[f188,f166])).

fof(f166,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f164,f122])).

fof(f122,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK7(X0),X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f69,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f164,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f163,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f163,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f125,f121])).

fof(f121,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f73,f74])).

fof(f74,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f188,plain,(
    ! [X0] : ~ r2_hidden(X0,a_2_5_lattice3(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f187,f87])).

fof(f87,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,a_2_5_lattice3(sK0,X1)) ) ),
    inference(resolution,[],[f186,f121])).

fof(f186,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,sK0,X1),X1)
      | ~ r2_hidden(X0,a_2_5_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f185,f82])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | r2_hidden(sK10(X0,sK0,X1),X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f83])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | r2_hidden(sK10(X0,sK0,X1),X1)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f183,f85])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | r2_hidden(sK10(X0,sK0,X1),X1)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f133,f84])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X1)
      | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | r2_hidden(sK10(X0,X1,X2),X2)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK10(X0,X1,X2),X2)
            & r3_lattices(X1,sK9(X0,X1,X2),sK10(X0,X1,X2))
            & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))
            & sK9(X0,X1,X2) = X0
            & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f78,f80,f79])).

fof(f79,plain,(
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
            & r3_lattices(X1,sK9(X0,X1,X2),X6)
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK9(X0,X1,X2) = X0
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r3_lattices(X1,sK9(X0,X1,X2),X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK10(X0,X1,X2),X2)
        & r3_lattices(X1,sK9(X0,X1,X2),sK10(X0,X1,X2))
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
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
    inference(rectify,[],[f77])).

fof(f77,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f213,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK0,X0,X1),X0)
      | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f212,f82])).

fof(f212,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK0,X0,X1),X0)
      | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f211,f83])).

fof(f211,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK0,X0,X1),X0)
      | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f210,f85])).

fof(f210,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK0,X0,X1),X0)
      | ~ l3_lattices(sK0)
      | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f119,f84])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ l3_lattices(X0)
      | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ( ! [X4] :
                ( ~ r2_hidden(X4,X2)
                | ~ r3_lattices(X0,sK6(X0,X1,X2),X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(sK6(X0,X1,X2),X1)
            & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X4,X2)
              | ~ r3_lattices(X0,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r2_hidden(X4,X2)
            | ~ r3_lattices(X0,sK6(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f330,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,X0,X1)
        | k2_lattices(sK0,X0,X1) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f329])).

fof(f341,plain,(
    spl11_11 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | spl11_11 ),
    inference(subsumption_resolution,[],[f339,f85])).

fof(f339,plain,
    ( ~ l3_lattices(sK0)
    | spl11_11 ),
    inference(subsumption_resolution,[],[f338,f82])).

fof(f338,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl11_11 ),
    inference(subsumption_resolution,[],[f337,f83])).

fof(f337,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl11_11 ),
    inference(resolution,[],[f327,f96])).

fof(f96,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f327,plain,
    ( ~ v9_lattices(sK0)
    | spl11_11 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl11_11
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f336,plain,(
    spl11_10 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl11_10 ),
    inference(subsumption_resolution,[],[f334,f85])).

fof(f334,plain,
    ( ~ l3_lattices(sK0)
    | spl11_10 ),
    inference(subsumption_resolution,[],[f333,f82])).

fof(f333,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl11_10 ),
    inference(subsumption_resolution,[],[f332,f83])).

fof(f332,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl11_10 ),
    inference(resolution,[],[f323,f95])).

fof(f95,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f323,plain,
    ( ~ v8_lattices(sK0)
    | spl11_10 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl11_10
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f331,plain,
    ( ~ spl11_10
    | ~ spl11_11
    | spl11_12 ),
    inference(avatar_split_clause,[],[f319,f329,f325,f321])).

fof(f319,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X0,X1)
      | k2_lattices(sK0,X0,X1) = X0
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f318,f82])).

fof(f318,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X0,X1)
      | k2_lattices(sK0,X0,X1) = X0
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f317,f85])).

fof(f317,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X0,X1)
      | k2_lattices(sK0,X0,X1) = X0
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f316])).

fof(f316,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X0,X1)
      | k2_lattices(sK0,X0,X1) = X0
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f315,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(f315,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f314,f82])).

fof(f314,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f313,f85])).

fof(f313,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f312,f83])).

fof(f312,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f311,f95])).

fof(f311,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f310,f93])).

fof(f310,plain,(
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
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,(
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
    inference(resolution,[],[f127,f96])).

fof(f127,plain,(
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
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f272,plain,(
    spl11_8 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | spl11_8 ),
    inference(subsumption_resolution,[],[f270,f85])).

fof(f270,plain,
    ( ~ l3_lattices(sK0)
    | spl11_8 ),
    inference(resolution,[],[f254,f88])).

fof(f254,plain,
    ( ~ l1_lattices(sK0)
    | spl11_8 ),
    inference(avatar_component_clause,[],[f252])).

fof(f162,plain,(
    spl11_2 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl11_2 ),
    inference(subsumption_resolution,[],[f145,f83])).

fof(f145,plain,
    ( ~ v10_lattices(sK0)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl11_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f158,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f86,f155,f151,f147,f143,f139])).

fof(f86,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:55:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (7005)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.50  % (7004)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.50  % (7011)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (7003)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (7020)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (7006)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (6998)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (6998)Refutation not found, incomplete strategy% (6998)------------------------------
% 0.22/0.51  % (6998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (6998)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (6998)Memory used [KB]: 1663
% 0.22/0.51  % (6998)Time elapsed: 0.001 s
% 0.22/0.51  % (6998)------------------------------
% 0.22/0.51  % (6998)------------------------------
% 0.22/0.51  % (7013)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (7008)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (7012)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (7008)Refutation not found, incomplete strategy% (7008)------------------------------
% 0.22/0.51  % (7008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7008)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (7008)Memory used [KB]: 10746
% 0.22/0.51  % (7008)Time elapsed: 0.081 s
% 0.22/0.51  % (7008)------------------------------
% 0.22/0.51  % (7008)------------------------------
% 0.22/0.51  % (7002)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (7001)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (7027)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (7016)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (7024)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (7019)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (7014)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (7017)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (7018)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (7007)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (7021)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (6999)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (7020)Refutation not found, incomplete strategy% (7020)------------------------------
% 0.22/0.53  % (7020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7000)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (7020)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7020)Memory used [KB]: 10746
% 0.22/0.53  % (7020)Time elapsed: 0.118 s
% 0.22/0.53  % (7020)------------------------------
% 0.22/0.53  % (7020)------------------------------
% 0.22/0.53  % (7022)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (7010)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (7015)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (7015)Refutation not found, incomplete strategy% (7015)------------------------------
% 0.22/0.53  % (7015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7015)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7015)Memory used [KB]: 10618
% 0.22/0.53  % (7015)Time elapsed: 0.130 s
% 0.22/0.53  % (7015)------------------------------
% 0.22/0.53  % (7015)------------------------------
% 0.22/0.53  % (7025)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (7026)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (7009)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (7009)Refutation not found, incomplete strategy% (7009)------------------------------
% 0.22/0.54  % (7009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7009)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (7009)Memory used [KB]: 10746
% 0.22/0.54  % (7009)Time elapsed: 0.135 s
% 0.22/0.54  % (7009)------------------------------
% 0.22/0.54  % (7009)------------------------------
% 0.22/0.54  % (7001)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f471,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f158,f162,f272,f331,f336,f341,f360,f365,f391,f401,f432,f442,f464,f470])).
% 0.22/0.54  fof(f470,plain,(
% 0.22/0.54    ~spl11_1),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f469])).
% 0.22/0.54  fof(f469,plain,(
% 0.22/0.54    $false | ~spl11_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f141,f82])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ~v2_struct_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f49])).
% 0.22/0.54  % (7023)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (7007)Refutation not found, incomplete strategy% (7007)------------------------------
% 0.22/0.54  % (7007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (7007)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (7007)Memory used [KB]: 10618
% 1.46/0.56  % (7007)Time elapsed: 0.005 s
% 1.46/0.56  % (7007)------------------------------
% 1.46/0.56  % (7007)------------------------------
% 1.46/0.56  fof(f49,plain,(
% 1.46/0.56    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f21,plain,(
% 1.46/0.56    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f20])).
% 1.46/0.56  fof(f20,plain,(
% 1.46/0.56    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f19])).
% 1.46/0.56  fof(f19,negated_conjecture,(
% 1.46/0.56    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.46/0.56    inference(negated_conjecture,[],[f18])).
% 1.46/0.56  fof(f18,conjecture,(
% 1.46/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).
% 1.46/0.56  fof(f141,plain,(
% 1.46/0.56    v2_struct_0(sK0) | ~spl11_1),
% 1.46/0.56    inference(avatar_component_clause,[],[f139])).
% 1.46/0.56  fof(f139,plain,(
% 1.46/0.56    spl11_1 <=> v2_struct_0(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.46/0.56  fof(f464,plain,(
% 1.46/0.56    spl11_5 | ~spl11_13 | ~spl11_15 | ~spl11_17 | ~spl11_18),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f463])).
% 1.46/0.56  fof(f463,plain,(
% 1.46/0.56    $false | (spl11_5 | ~spl11_13 | ~spl11_15 | ~spl11_17 | ~spl11_18)),
% 1.46/0.56    inference(subsumption_resolution,[],[f462,f351])).
% 1.46/0.56  fof(f351,plain,(
% 1.46/0.56    m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~spl11_13),
% 1.46/0.56    inference(avatar_component_clause,[],[f350])).
% 1.46/0.56  fof(f350,plain,(
% 1.46/0.56    spl11_13 <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 1.46/0.56  fof(f462,plain,(
% 1.46/0.56    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl11_5 | ~spl11_15 | ~spl11_17 | ~spl11_18)),
% 1.46/0.56    inference(subsumption_resolution,[],[f461,f424])).
% 1.46/0.56  fof(f424,plain,(
% 1.46/0.56    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl11_17),
% 1.46/0.56    inference(avatar_component_clause,[],[f423])).
% 1.46/0.56  fof(f423,plain,(
% 1.46/0.56    spl11_17 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 1.46/0.56  fof(f461,plain,(
% 1.46/0.56    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl11_5 | ~spl11_15 | ~spl11_18)),
% 1.46/0.56    inference(subsumption_resolution,[],[f452,f157])).
% 1.46/0.56  fof(f157,plain,(
% 1.46/0.56    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl11_5),
% 1.46/0.56    inference(avatar_component_clause,[],[f155])).
% 1.46/0.56  fof(f155,plain,(
% 1.46/0.56    spl11_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.46/0.56  fof(f452,plain,(
% 1.46/0.56    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (~spl11_15 | ~spl11_18)),
% 1.46/0.56    inference(superposition,[],[f359,f428])).
% 1.46/0.56  fof(f428,plain,(
% 1.46/0.56    ( ! [X1] : (k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl11_18),
% 1.46/0.56    inference(avatar_component_clause,[],[f427])).
% 1.46/0.56  fof(f427,plain,(
% 1.46/0.56    spl11_18 <=> ! [X1] : (k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 1.46/0.56  fof(f359,plain,(
% 1.46/0.56    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl11_15),
% 1.46/0.56    inference(avatar_component_clause,[],[f358])).
% 1.46/0.56  fof(f358,plain,(
% 1.46/0.56    spl11_15 <=> ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 1.46/0.56  fof(f442,plain,(
% 1.46/0.56    ~spl11_8 | spl11_17),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f441])).
% 1.46/0.56  fof(f441,plain,(
% 1.46/0.56    $false | (~spl11_8 | spl11_17)),
% 1.46/0.56    inference(subsumption_resolution,[],[f440,f82])).
% 1.46/0.56  fof(f440,plain,(
% 1.46/0.56    v2_struct_0(sK0) | (~spl11_8 | spl11_17)),
% 1.46/0.56    inference(subsumption_resolution,[],[f438,f253])).
% 1.46/0.56  fof(f253,plain,(
% 1.46/0.56    l1_lattices(sK0) | ~spl11_8),
% 1.46/0.56    inference(avatar_component_clause,[],[f252])).
% 1.46/0.56  fof(f252,plain,(
% 1.46/0.56    spl11_8 <=> l1_lattices(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 1.46/0.56  fof(f438,plain,(
% 1.46/0.56    ~l1_lattices(sK0) | v2_struct_0(sK0) | spl11_17),
% 1.46/0.56    inference(resolution,[],[f425,f100])).
% 1.46/0.56  fof(f100,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f29])).
% 1.46/0.56  fof(f29,plain,(
% 1.46/0.56    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f28])).
% 1.46/0.56  fof(f28,plain,(
% 1.46/0.56    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f7])).
% 1.46/0.56  fof(f7,axiom,(
% 1.46/0.56    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 1.46/0.56  fof(f425,plain,(
% 1.46/0.56    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | spl11_17),
% 1.46/0.56    inference(avatar_component_clause,[],[f423])).
% 1.46/0.56  fof(f432,plain,(
% 1.46/0.56    ~spl11_17 | spl11_18 | ~spl11_3 | ~spl11_8),
% 1.46/0.56    inference(avatar_split_clause,[],[f418,f252,f147,f427,f423])).
% 1.46/0.56  fof(f147,plain,(
% 1.46/0.56    spl11_3 <=> v13_lattices(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.46/0.56  fof(f418,plain,(
% 1.46/0.56    ( ! [X1] : (k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))) ) | (~spl11_3 | ~spl11_8)),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f417])).
% 1.46/0.56  fof(f417,plain,(
% 1.46/0.56    ( ! [X1] : (k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl11_3 | ~spl11_8)),
% 1.46/0.56    inference(superposition,[],[f237,f407])).
% 1.46/0.56  fof(f407,plain,(
% 1.46/0.56    ( ! [X0] : (k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl11_3 | ~spl11_8)),
% 1.46/0.56    inference(subsumption_resolution,[],[f406,f253])).
% 1.46/0.56  fof(f406,plain,(
% 1.46/0.56    ( ! [X0] : (k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_lattices(sK0)) ) | ~spl11_3),
% 1.46/0.56    inference(subsumption_resolution,[],[f402,f82])).
% 1.46/0.56  fof(f402,plain,(
% 1.46/0.56    ( ! [X0] : (k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_lattices(sK0)) ) | ~spl11_3),
% 1.46/0.56    inference(resolution,[],[f148,f160])).
% 1.46/0.56  fof(f160,plain,(
% 1.46/0.56    ( ! [X0,X3] : (~v13_lattices(X0) | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_lattices(X0)) )),
% 1.46/0.56    inference(global_subsumption,[],[f100,f136])).
% 1.46/0.56  fof(f136,plain,(
% 1.46/0.56    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(equality_resolution,[],[f101])).
% 1.46/0.56  fof(f101,plain,(
% 1.46/0.56    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f55])).
% 1.46/0.56  fof(f55,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).
% 1.46/0.56  fof(f54,plain,(
% 1.46/0.56    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f53,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(rectify,[],[f52])).
% 1.46/0.56  fof(f52,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(nnf_transformation,[],[f31])).
% 1.46/0.56  fof(f31,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f30])).
% 1.46/0.56  fof(f30,plain,(
% 1.46/0.56    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f6])).
% 1.46/0.56  fof(f6,axiom,(
% 1.46/0.56    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 1.46/0.56  fof(f148,plain,(
% 1.46/0.56    v13_lattices(sK0) | ~spl11_3),
% 1.46/0.56    inference(avatar_component_clause,[],[f147])).
% 1.46/0.56  fof(f237,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f236,f85])).
% 1.46/0.56  fof(f85,plain,(
% 1.46/0.56    l3_lattices(sK0)),
% 1.46/0.56    inference(cnf_transformation,[],[f50])).
% 1.46/0.56  fof(f236,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | ~l3_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f235,f82])).
% 1.46/0.56  fof(f235,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.46/0.56    inference(resolution,[],[f234,f83])).
% 1.46/0.56  fof(f83,plain,(
% 1.46/0.56    v10_lattices(sK0)),
% 1.46/0.56    inference(cnf_transformation,[],[f50])).
% 1.46/0.56  fof(f234,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f233])).
% 1.46/0.56  fof(f233,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 1.46/0.56    inference(resolution,[],[f222,f93])).
% 1.46/0.56  fof(f93,plain,(
% 1.46/0.56    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f24])).
% 1.46/0.56  fof(f24,plain,(
% 1.46/0.56    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.46/0.56    inference(flattening,[],[f23])).
% 1.46/0.56  fof(f23,plain,(
% 1.46/0.56    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f5])).
% 1.46/0.56  fof(f5,axiom,(
% 1.46/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 1.46/0.56  fof(f222,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~v6_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 1.46/0.56    inference(resolution,[],[f110,f88])).
% 1.46/0.56  fof(f88,plain,(
% 1.46/0.56    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f22])).
% 1.46/0.56  fof(f22,plain,(
% 1.46/0.56    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f8])).
% 1.46/0.56  fof(f8,axiom,(
% 1.46/0.56    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.46/0.56  fof(f110,plain,(
% 1.46/0.56    ( ! [X4,X0,X3] : (~l1_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f65])).
% 1.46/0.56  fof(f65,plain,(
% 1.46/0.56    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f62,f64,f63])).
% 1.46/0.56  fof(f63,plain,(
% 1.46/0.56    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f64,plain,(
% 1.46/0.56    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f62,plain,(
% 1.46/0.56    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(rectify,[],[f61])).
% 1.46/0.56  fof(f61,plain,(
% 1.46/0.56    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(nnf_transformation,[],[f35])).
% 1.46/0.56  fof(f35,plain,(
% 1.46/0.56    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f34])).
% 1.46/0.56  fof(f34,plain,(
% 1.46/0.56    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f12])).
% 1.46/0.56  fof(f12,axiom,(
% 1.46/0.56    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).
% 1.46/0.56  fof(f401,plain,(
% 1.46/0.56    spl11_4),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f400])).
% 1.46/0.56  fof(f400,plain,(
% 1.46/0.56    $false | spl11_4),
% 1.46/0.56    inference(subsumption_resolution,[],[f153,f85])).
% 1.46/0.56  fof(f153,plain,(
% 1.46/0.56    ~l3_lattices(sK0) | spl11_4),
% 1.46/0.56    inference(avatar_component_clause,[],[f151])).
% 1.46/0.56  fof(f151,plain,(
% 1.46/0.56    spl11_4 <=> l3_lattices(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.46/0.56  fof(f391,plain,(
% 1.46/0.56    spl11_3 | ~spl11_8 | ~spl11_13 | ~spl11_15),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f390])).
% 1.46/0.56  fof(f390,plain,(
% 1.46/0.56    $false | (spl11_3 | ~spl11_8 | ~spl11_13 | ~spl11_15)),
% 1.46/0.56    inference(subsumption_resolution,[],[f389,f82])).
% 1.46/0.56  fof(f389,plain,(
% 1.46/0.56    v2_struct_0(sK0) | (spl11_3 | ~spl11_8 | ~spl11_13 | ~spl11_15)),
% 1.46/0.56    inference(subsumption_resolution,[],[f388,f253])).
% 1.46/0.56  fof(f388,plain,(
% 1.46/0.56    ~l1_lattices(sK0) | v2_struct_0(sK0) | (spl11_3 | ~spl11_8 | ~spl11_13 | ~spl11_15)),
% 1.46/0.56    inference(subsumption_resolution,[],[f387,f351])).
% 1.46/0.56  fof(f387,plain,(
% 1.46/0.56    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (spl11_3 | ~spl11_8 | ~spl11_13 | ~spl11_15)),
% 1.46/0.56    inference(subsumption_resolution,[],[f385,f149])).
% 1.46/0.56  fof(f149,plain,(
% 1.46/0.56    ~v13_lattices(sK0) | spl11_3),
% 1.46/0.56    inference(avatar_component_clause,[],[f147])).
% 1.46/0.56  fof(f385,plain,(
% 1.46/0.56    v13_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (spl11_3 | ~spl11_8 | ~spl11_13 | ~spl11_15)),
% 1.46/0.56    inference(resolution,[],[f384,f108])).
% 1.46/0.56  fof(f108,plain,(
% 1.46/0.56    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f60])).
% 1.46/0.56  fof(f60,plain,(
% 1.46/0.56    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f57,f59,f58])).
% 1.46/0.56  fof(f58,plain,(
% 1.46/0.56    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f59,plain,(
% 1.46/0.56    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f57,plain,(
% 1.46/0.56    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(rectify,[],[f56])).
% 1.46/0.56  fof(f56,plain,(
% 1.46/0.56    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(nnf_transformation,[],[f33])).
% 1.46/0.56  fof(f33,plain,(
% 1.46/0.56    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f32])).
% 1.46/0.56  fof(f32,plain,(
% 1.46/0.56    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f11])).
% 1.46/0.56  fof(f11,axiom,(
% 1.46/0.56    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).
% 1.46/0.56  fof(f384,plain,(
% 1.46/0.56    ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl11_3 | ~spl11_8 | ~spl11_13 | ~spl11_15)),
% 1.46/0.56    inference(subsumption_resolution,[],[f375,f351])).
% 1.46/0.56  fof(f375,plain,(
% 1.46/0.56    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl11_3 | ~spl11_8 | ~spl11_15)),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f374])).
% 1.46/0.56  fof(f374,plain,(
% 1.46/0.56    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl11_3 | ~spl11_8 | ~spl11_15)),
% 1.46/0.56    inference(superposition,[],[f304,f359])).
% 1.46/0.56  fof(f304,plain,(
% 1.46/0.56    ( ! [X0] : (k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl11_3 | ~spl11_8)),
% 1.46/0.56    inference(subsumption_resolution,[],[f303,f82])).
% 1.46/0.56  fof(f303,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | v2_struct_0(sK0)) ) | (spl11_3 | ~spl11_8)),
% 1.46/0.56    inference(subsumption_resolution,[],[f302,f253])).
% 1.46/0.56  fof(f302,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl11_3 | ~spl11_8)),
% 1.46/0.56    inference(subsumption_resolution,[],[f301,f149])).
% 1.46/0.56  fof(f301,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl11_3 | ~spl11_8)),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f299])).
% 1.46/0.56  fof(f299,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | v13_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl11_3 | ~spl11_8)),
% 1.46/0.56    inference(resolution,[],[f297,f108])).
% 1.46/0.56  fof(f297,plain,(
% 1.46/0.56    ( ! [X1] : (~m1_subset_1(sK2(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,sK2(sK0,X1)) != X1) ) | (spl11_3 | ~spl11_8)),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f296])).
% 1.46/0.56  fof(f296,plain,(
% 1.46/0.56    ( ! [X1] : (k2_lattices(sK0,X1,sK2(sK0,X1)) != X1 | k2_lattices(sK0,X1,sK2(sK0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK2(sK0,X1),u1_struct_0(sK0))) ) | (spl11_3 | ~spl11_8)),
% 1.46/0.56    inference(superposition,[],[f294,f237])).
% 1.46/0.56  fof(f294,plain,(
% 1.46/0.56    ( ! [X0] : (k2_lattices(sK0,sK2(sK0,X0),X0) != X0 | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl11_3 | ~spl11_8)),
% 1.46/0.56    inference(subsumption_resolution,[],[f293,f149])).
% 1.46/0.56  fof(f293,plain,(
% 1.46/0.56    ( ! [X0] : (k2_lattices(sK0,sK2(sK0,X0),X0) != X0 | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v13_lattices(sK0)) ) | ~spl11_8),
% 1.46/0.56    inference(subsumption_resolution,[],[f292,f253])).
% 1.46/0.56  fof(f292,plain,(
% 1.46/0.56    ( ! [X0] : (k2_lattices(sK0,sK2(sK0,X0),X0) != X0 | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v13_lattices(sK0)) )),
% 1.46/0.56    inference(resolution,[],[f109,f82])).
% 1.46/0.56  fof(f109,plain,(
% 1.46/0.56    ( ! [X0,X1] : (v2_struct_0(X0) | k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v13_lattices(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f60])).
% 1.46/0.56  fof(f365,plain,(
% 1.46/0.56    spl11_13),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f364])).
% 1.46/0.56  fof(f364,plain,(
% 1.46/0.56    $false | spl11_13),
% 1.46/0.56    inference(subsumption_resolution,[],[f363,f82])).
% 1.46/0.56  fof(f363,plain,(
% 1.46/0.56    v2_struct_0(sK0) | spl11_13),
% 1.46/0.56    inference(subsumption_resolution,[],[f361,f85])).
% 1.46/0.56  fof(f361,plain,(
% 1.46/0.56    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl11_13),
% 1.46/0.56    inference(resolution,[],[f352,f123])).
% 1.46/0.56  fof(f123,plain,(
% 1.46/0.56    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f43])).
% 1.46/0.56  fof(f43,plain,(
% 1.46/0.56    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f42])).
% 1.46/0.56  fof(f42,plain,(
% 1.46/0.56    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f13])).
% 1.46/0.56  fof(f13,axiom,(
% 1.46/0.56    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 1.46/0.56  fof(f352,plain,(
% 1.46/0.56    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | spl11_13),
% 1.46/0.56    inference(avatar_component_clause,[],[f350])).
% 1.46/0.56  fof(f360,plain,(
% 1.46/0.56    ~spl11_13 | spl11_15 | ~spl11_12),
% 1.46/0.56    inference(avatar_split_clause,[],[f348,f329,f358,f350])).
% 1.46/0.56  fof(f329,plain,(
% 1.46/0.56    spl11_12 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0 | ~r3_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 1.46/0.56  fof(f348,plain,(
% 1.46/0.56    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl11_12),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f345])).
% 1.46/0.56  fof(f345,plain,(
% 1.46/0.56    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl11_12),
% 1.46/0.56    inference(resolution,[],[f330,f217])).
% 1.46/0.56  fof(f217,plain,(
% 1.46/0.56    ( ! [X1] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.46/0.56    inference(superposition,[],[f215,f181])).
% 1.46/0.56  fof(f181,plain,(
% 1.46/0.56    ( ! [X0] : (k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f180,f82])).
% 1.46/0.56  fof(f180,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f179,f83])).
% 1.46/0.56  fof(f179,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f178,f85])).
% 1.46/0.56  fof(f178,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(resolution,[],[f116,f84])).
% 1.46/0.56  fof(f84,plain,(
% 1.46/0.56    v4_lattice3(sK0)),
% 1.46/0.56    inference(cnf_transformation,[],[f50])).
% 1.46/0.56  fof(f116,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~v4_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f39])).
% 1.46/0.56  fof(f39,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f38])).
% 1.46/0.56  fof(f38,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f15])).
% 1.46/0.56  fof(f15,axiom,(
% 1.46/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).
% 1.46/0.56  fof(f215,plain,(
% 1.46/0.56    ( ! [X2] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X2))) )),
% 1.46/0.56    inference(resolution,[],[f213,f196])).
% 1.46/0.56  fof(f196,plain,(
% 1.46/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.46/0.56    inference(backward_demodulation,[],[f188,f191])).
% 1.46/0.56  fof(f191,plain,(
% 1.46/0.56    k1_xboole_0 = a_2_5_lattice3(sK0,k1_xboole_0)),
% 1.46/0.56    inference(resolution,[],[f188,f166])).
% 1.46/0.56  fof(f166,plain,(
% 1.46/0.56    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 1.46/0.56    inference(resolution,[],[f164,f122])).
% 1.46/0.56  fof(f122,plain,(
% 1.46/0.56    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f71])).
% 1.46/0.56  fof(f71,plain,(
% 1.46/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f69,f70])).
% 1.46/0.56  fof(f70,plain,(
% 1.46/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f69,plain,(
% 1.46/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.46/0.56    inference(rectify,[],[f68])).
% 1.46/0.56  fof(f68,plain,(
% 1.46/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.46/0.56    inference(nnf_transformation,[],[f1])).
% 1.46/0.56  fof(f1,axiom,(
% 1.46/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.46/0.56  fof(f164,plain,(
% 1.46/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.46/0.56    inference(resolution,[],[f163,f97])).
% 1.46/0.56  fof(f97,plain,(
% 1.46/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.46/0.56    inference(cnf_transformation,[],[f25])).
% 1.46/0.56  fof(f25,plain,(
% 1.46/0.56    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.46/0.56    inference(ennf_transformation,[],[f4])).
% 1.46/0.56  fof(f4,axiom,(
% 1.46/0.56    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.46/0.56  fof(f163,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.46/0.56    inference(resolution,[],[f125,f121])).
% 1.46/0.56  fof(f121,plain,(
% 1.46/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f71])).
% 1.46/0.56  fof(f125,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f75])).
% 1.46/0.56  fof(f75,plain,(
% 1.46/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f73,f74])).
% 1.46/0.56  fof(f74,plain,(
% 1.46/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f73,plain,(
% 1.46/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.46/0.56    inference(rectify,[],[f72])).
% 1.46/0.56  fof(f72,plain,(
% 1.46/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.46/0.56    inference(nnf_transformation,[],[f44])).
% 1.46/0.56  fof(f44,plain,(
% 1.46/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f2])).
% 1.46/0.56  fof(f2,axiom,(
% 1.46/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.46/0.56  fof(f188,plain,(
% 1.46/0.56    ( ! [X0] : (~r2_hidden(X0,a_2_5_lattice3(sK0,k1_xboole_0))) )),
% 1.46/0.56    inference(resolution,[],[f187,f87])).
% 1.46/0.56  fof(f87,plain,(
% 1.46/0.56    v1_xboole_0(k1_xboole_0)),
% 1.46/0.56    inference(cnf_transformation,[],[f3])).
% 1.46/0.56  fof(f3,axiom,(
% 1.46/0.56    v1_xboole_0(k1_xboole_0)),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.46/0.56  fof(f187,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,a_2_5_lattice3(sK0,X1))) )),
% 1.46/0.56    inference(resolution,[],[f186,f121])).
% 1.46/0.56  fof(f186,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r2_hidden(sK10(X0,sK0,X1),X1) | ~r2_hidden(X0,a_2_5_lattice3(sK0,X1))) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f185,f82])).
% 1.46/0.56  fof(f185,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | r2_hidden(sK10(X0,sK0,X1),X1) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f184,f83])).
% 1.46/0.56  fof(f184,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | r2_hidden(sK10(X0,sK0,X1),X1) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f183,f85])).
% 1.46/0.56  fof(f183,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~l3_lattices(sK0) | r2_hidden(sK10(X0,sK0,X1),X1) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(resolution,[],[f133,f84])).
% 1.46/0.56  fof(f133,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~v4_lattice3(X1) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ~l3_lattices(X1) | r2_hidden(sK10(X0,X1,X2),X2) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f81])).
% 1.46/0.56  fof(f81,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (((r2_hidden(sK10(X0,X1,X2),X2) & r3_lattices(X1,sK9(X0,X1,X2),sK10(X0,X1,X2)) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))) & sK9(X0,X1,X2) = X0 & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f78,f80,f79])).
% 1.46/0.56  fof(f79,plain,(
% 1.46/0.56    ! [X2,X1,X0] : (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,sK9(X0,X1,X2),X6) & m1_subset_1(X6,u1_struct_0(X1))) & sK9(X0,X1,X2) = X0 & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f80,plain,(
% 1.46/0.56    ! [X2,X1,X0] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,sK9(X0,X1,X2),X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(sK10(X0,X1,X2),X2) & r3_lattices(X1,sK9(X0,X1,X2),sK10(X0,X1,X2)) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f78,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.46/0.56    inference(rectify,[],[f77])).
% 1.46/0.56  fof(f77,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.46/0.56    inference(nnf_transformation,[],[f48])).
% 1.46/0.56  fof(f48,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.46/0.56    inference(flattening,[],[f47])).
% 1.46/0.56  fof(f47,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 1.46/0.56    inference(ennf_transformation,[],[f14])).
% 1.46/0.56  fof(f14,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).
% 1.46/0.56  fof(f213,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X0,X1),X0) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f212,f82])).
% 1.46/0.56  fof(f212,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X0,X1),X0) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f211,f83])).
% 1.46/0.56  fof(f211,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X0,X1),X0) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f210,f85])).
% 1.46/0.56  fof(f210,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X0,X1),X0) | ~l3_lattices(sK0) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(resolution,[],[f119,f84])).
% 1.46/0.56  fof(f119,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | r2_hidden(sK6(X0,X1,X2),X1) | ~l3_lattices(X0) | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f67])).
% 1.46/0.56  fof(f67,plain,(
% 1.46/0.56    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK6(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f66])).
% 1.46/0.56  fof(f66,plain,(
% 1.46/0.56    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK6(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f41,plain,(
% 1.46/0.56    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f40])).
% 1.46/0.56  fof(f40,plain,(
% 1.46/0.56    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f17])).
% 1.46/0.56  fof(f17,axiom,(
% 1.46/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).
% 1.46/0.56  fof(f330,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~r3_lattices(sK0,X0,X1) | k2_lattices(sK0,X0,X1) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl11_12),
% 1.46/0.56    inference(avatar_component_clause,[],[f329])).
% 1.46/0.56  fof(f341,plain,(
% 1.46/0.56    spl11_11),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f340])).
% 1.46/0.56  fof(f340,plain,(
% 1.46/0.56    $false | spl11_11),
% 1.46/0.56    inference(subsumption_resolution,[],[f339,f85])).
% 1.46/0.56  fof(f339,plain,(
% 1.46/0.56    ~l3_lattices(sK0) | spl11_11),
% 1.46/0.56    inference(subsumption_resolution,[],[f338,f82])).
% 1.46/0.56  fof(f338,plain,(
% 1.46/0.56    v2_struct_0(sK0) | ~l3_lattices(sK0) | spl11_11),
% 1.46/0.56    inference(subsumption_resolution,[],[f337,f83])).
% 1.46/0.56  fof(f337,plain,(
% 1.46/0.56    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl11_11),
% 1.46/0.56    inference(resolution,[],[f327,f96])).
% 1.46/0.56  fof(f96,plain,(
% 1.46/0.56    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f24])).
% 1.46/0.56  fof(f327,plain,(
% 1.46/0.56    ~v9_lattices(sK0) | spl11_11),
% 1.46/0.56    inference(avatar_component_clause,[],[f325])).
% 1.46/0.56  fof(f325,plain,(
% 1.46/0.56    spl11_11 <=> v9_lattices(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 1.46/0.56  fof(f336,plain,(
% 1.46/0.56    spl11_10),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f335])).
% 1.46/0.56  fof(f335,plain,(
% 1.46/0.56    $false | spl11_10),
% 1.46/0.56    inference(subsumption_resolution,[],[f334,f85])).
% 1.46/0.56  fof(f334,plain,(
% 1.46/0.56    ~l3_lattices(sK0) | spl11_10),
% 1.46/0.56    inference(subsumption_resolution,[],[f333,f82])).
% 1.46/0.56  fof(f333,plain,(
% 1.46/0.56    v2_struct_0(sK0) | ~l3_lattices(sK0) | spl11_10),
% 1.46/0.56    inference(subsumption_resolution,[],[f332,f83])).
% 1.46/0.56  fof(f332,plain,(
% 1.46/0.56    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl11_10),
% 1.46/0.56    inference(resolution,[],[f323,f95])).
% 1.46/0.56  fof(f95,plain,(
% 1.46/0.56    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f24])).
% 1.46/0.56  fof(f323,plain,(
% 1.46/0.56    ~v8_lattices(sK0) | spl11_10),
% 1.46/0.56    inference(avatar_component_clause,[],[f321])).
% 1.46/0.56  fof(f321,plain,(
% 1.46/0.56    spl11_10 <=> v8_lattices(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 1.46/0.56  fof(f331,plain,(
% 1.46/0.56    ~spl11_10 | ~spl11_11 | spl11_12),
% 1.46/0.56    inference(avatar_split_clause,[],[f319,f329,f325,f321])).
% 1.46/0.56  fof(f319,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | k2_lattices(sK0,X0,X1) = X0 | ~v9_lattices(sK0) | ~v8_lattices(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f318,f82])).
% 1.46/0.56  fof(f318,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | k2_lattices(sK0,X0,X1) = X0 | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f317,f85])).
% 1.46/0.56  fof(f317,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | k2_lattices(sK0,X0,X1) = X0 | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f316])).
% 1.46/0.56  fof(f316,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | k2_lattices(sK0,X0,X1) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.46/0.56    inference(resolution,[],[f315,f98])).
% 1.46/0.56  fof(f98,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) = X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f51])).
% 1.46/0.56  fof(f51,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(nnf_transformation,[],[f27])).
% 1.46/0.56  fof(f27,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f26])).
% 1.46/0.56  fof(f26,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f10])).
% 1.46/0.56  fof(f10,axiom,(
% 1.46/0.56    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 1.46/0.56  fof(f315,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r1_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,X1,X0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f314,f82])).
% 1.46/0.56  fof(f314,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r3_lattices(sK0,X1,X0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f313,f85])).
% 1.46/0.56  fof(f313,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r3_lattices(sK0,X1,X0)) )),
% 1.46/0.56    inference(resolution,[],[f312,f83])).
% 1.46/0.56  fof(f312,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | v2_struct_0(X0) | ~r3_lattices(X0,X1,X2)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f311,f95])).
% 1.46/0.56  fof(f311,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 1.46/0.56    inference(subsumption_resolution,[],[f310,f93])).
% 1.46/0.56  fof(f310,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f309])).
% 1.46/0.56  fof(f309,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.46/0.56    inference(resolution,[],[f127,f96])).
% 1.46/0.56  fof(f127,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f76])).
% 1.46/0.56  fof(f76,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(nnf_transformation,[],[f46])).
% 1.46/0.56  fof(f46,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f45])).
% 1.46/0.56  fof(f45,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f9])).
% 1.46/0.56  fof(f9,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 1.46/0.56  fof(f272,plain,(
% 1.46/0.56    spl11_8),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f271])).
% 1.46/0.56  fof(f271,plain,(
% 1.46/0.56    $false | spl11_8),
% 1.46/0.56    inference(subsumption_resolution,[],[f270,f85])).
% 1.46/0.56  fof(f270,plain,(
% 1.46/0.56    ~l3_lattices(sK0) | spl11_8),
% 1.46/0.56    inference(resolution,[],[f254,f88])).
% 1.46/0.56  fof(f254,plain,(
% 1.46/0.56    ~l1_lattices(sK0) | spl11_8),
% 1.46/0.56    inference(avatar_component_clause,[],[f252])).
% 1.46/0.56  fof(f162,plain,(
% 1.46/0.56    spl11_2),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f161])).
% 1.46/0.56  fof(f161,plain,(
% 1.46/0.56    $false | spl11_2),
% 1.46/0.56    inference(subsumption_resolution,[],[f145,f83])).
% 1.46/0.56  fof(f145,plain,(
% 1.46/0.56    ~v10_lattices(sK0) | spl11_2),
% 1.46/0.56    inference(avatar_component_clause,[],[f143])).
% 1.46/0.56  fof(f143,plain,(
% 1.46/0.56    spl11_2 <=> v10_lattices(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.46/0.56  fof(f158,plain,(
% 1.46/0.56    spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_5),
% 1.46/0.56    inference(avatar_split_clause,[],[f86,f155,f151,f147,f143,f139])).
% 1.46/0.56  fof(f86,plain,(
% 1.46/0.56    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 1.46/0.56    inference(cnf_transformation,[],[f50])).
% 1.46/0.56  % SZS output end Proof for theBenchmark
% 1.46/0.56  % (7001)------------------------------
% 1.46/0.56  % (7001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (7001)Termination reason: Refutation
% 1.46/0.56  
% 1.46/0.56  % (7001)Memory used [KB]: 11001
% 1.46/0.56  % (7001)Time elapsed: 0.141 s
% 1.46/0.56  % (7001)------------------------------
% 1.46/0.56  % (7001)------------------------------
% 1.46/0.57  % (6997)Success in time 0.198 s
%------------------------------------------------------------------------------
