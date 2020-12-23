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
% DateTime   : Thu Dec  3 13:15:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 408 expanded)
%              Number of leaves         :   26 ( 121 expanded)
%              Depth                    :   27
%              Number of atoms          :  910 (1891 expanded)
%              Number of equality atoms :   84 ( 146 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f470,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f92,f97,f102,f125,f150,f155,f158,f181,f186,f305,f365,f378,f467])).

fof(f467,plain,
    ( spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f466])).

fof(f466,plain,
    ( $false
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f465,f126])).

fof(f126,plain,
    ( ! [X14] : m1_subset_1(k15_lattice3(sK0,X14),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f110,f101])).

fof(f101,plain,
    ( l3_lattices(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl8_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f110,plain,
    ( ! [X14] :
        ( ~ l3_lattices(sK0)
        | m1_subset_1(k15_lattice3(sK0,X14),u1_struct_0(sK0)) )
    | spl8_1 ),
    inference(resolution,[],[f86,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f86,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl8_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f465,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_5
    | spl8_6
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f454,f124])).

fof(f124,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_6
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f454,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_5
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_14 ),
    inference(superposition,[],[f304,f399])).

fof(f399,plain,
    ( ! [X4] :
        ( k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | spl8_1
    | ~ spl8_5
    | ~ spl8_9
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f398,f349])).

fof(f349,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl8_14
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f398,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0)) )
    | spl8_1
    | ~ spl8_5
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f397,f86])).

fof(f397,plain,
    ( ! [X4] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0)) )
    | ~ spl8_5
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f387,f148])).

fof(f148,plain,
    ( l1_lattices(sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl8_9
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f387,plain,
    ( ! [X4] :
        ( ~ l1_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0)) )
    | ~ spl8_5 ),
    inference(resolution,[],[f119,f78])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X2,X1) = X1
      | k5_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

fof(f119,plain,
    ( v13_lattices(sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_5
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f304,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl8_13
  <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f378,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | spl8_5
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | spl8_5
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f376,f126])).

fof(f376,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | spl8_5
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(trivial_inequality_removal,[],[f375])).

fof(f375,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | spl8_5
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(duplicate_literal_removal,[],[f374])).

fof(f374,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | spl8_5
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(superposition,[],[f208,f271])).

fof(f271,plain,
    ( ! [X2] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | spl8_5
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f270,f120])).

fof(f120,plain,
    ( ~ v13_lattices(sK0)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f270,plain,
    ( ! [X2] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v13_lattices(sK0) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f269,f86])).

fof(f269,plain,
    ( ! [X2] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f262,f148])).

fof(f262,plain,
    ( ! [X2] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X2))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(resolution,[],[f251,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).

fof(f251,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(resolution,[],[f228,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f228,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(X4,sK7(sK0,X3,X4))
        | k15_lattice3(sK0,X4) = k2_lattices(sK0,k15_lattice3(sK0,X4),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(resolution,[],[f218,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f218,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK7(sK0,X4,X3),X3)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k15_lattice3(sK0,X3) = k2_lattices(sK0,k15_lattice3(sK0,X3),X4) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,
    ( ! [X4,X3] :
        ( k15_lattice3(sK0,X3) = k2_lattices(sK0,k15_lattice3(sK0,X3),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_hidden(sK7(sK0,X4,X3),X3)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(resolution,[],[f196,f137])).

fof(f137,plain,
    ( ! [X10,X11] :
        ( r4_lattice3(sK0,X10,X11)
        | r2_hidden(sK7(sK0,X10,X11),X11)
        | ~ m1_subset_1(X10,u1_struct_0(sK0)) )
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f108,f101])).

fof(f108,plain,
    ( ! [X10,X11] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | r2_hidden(sK7(sK0,X10,X11),X11)
        | r4_lattice3(sK0,X10,X11) )
    | spl8_1 ),
    inference(resolution,[],[f86,f74])).

% (21110)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK7(X0,X1,X2),X2)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f195,f126])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(resolution,[],[f191,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f131,f86])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f130,f101])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f129,f96])).

fof(f96,plain,
    ( v4_lattice3(sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl8_3
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f127,f91])).

fof(f91,plain,
    ( v10_lattices(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl8_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f126,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | r1_lattices(X0,k15_lattice3(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | r1_lattices(X0,X2,X3)
      | k15_lattice3(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

fof(f191,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattices(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_lattices(sK0,X2,X3) = X2
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl8_1
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f190,f101])).

fof(f190,plain,
    ( ! [X2,X3] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_lattices(sK0,X2,X3) = X2
        | ~ r1_lattices(sK0,X2,X3) )
    | spl8_1
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f189,f170])).

fof(f170,plain,
    ( v9_lattices(sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl8_11
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f189,plain,
    ( ! [X2,X3] :
        ( ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_lattices(sK0,X2,X3) = X2
        | ~ r1_lattices(sK0,X2,X3) )
    | spl8_1
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f104,f174])).

fof(f174,plain,
    ( v8_lattices(sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl8_12
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f104,plain,
    ( ! [X2,X3] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_lattices(sK0,X2,X3) = X2
        | ~ r1_lattices(sK0,X2,X3) )
    | spl8_1 ),
    inference(resolution,[],[f86,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

fof(f208,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl8_1
    | spl8_5
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f207,f120])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | v13_lattices(sK0) )
    | spl8_1
    | spl8_5
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f206,f86])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | spl8_1
    | spl8_5
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f205,f148])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | spl8_1
    | spl8_5
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | spl8_1
    | spl8_5
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(resolution,[],[f201,f61])).

fof(f201,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,sK3(sK0,X1)) != X1 )
    | spl8_1
    | spl8_5
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,
    ( ! [X1] :
        ( k2_lattices(sK0,X1,sK3(sK0,X1)) != X1
        | k2_lattices(sK0,X1,sK3(sK0,X1)) != X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl8_1
    | spl8_5
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(superposition,[],[f198,f145])).

fof(f145,plain,
    ( ! [X6,X5] :
        ( k2_lattices(sK0,X5,X6) = k2_lattices(sK0,X6,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl8_8
  <=> ! [X5,X6] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k2_lattices(sK0,X5,X6) = k2_lattices(sK0,X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f198,plain,
    ( ! [X4] :
        ( k2_lattices(sK0,sK3(sK0,X4),X4) != X4
        | k2_lattices(sK0,X4,sK3(sK0,X4)) != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | spl8_1
    | spl8_5
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f197,f120])).

fof(f197,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k2_lattices(sK0,X4,sK3(sK0,X4)) != X4
        | k2_lattices(sK0,sK3(sK0,X4),X4) != X4
        | v13_lattices(sK0) )
    | spl8_1
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f105,f148])).

fof(f105,plain,
    ( ! [X4] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k2_lattices(sK0,X4,sK3(sK0,X4)) != X4
        | k2_lattices(sK0,sK3(sK0,X4),X4) != X4
        | v13_lattices(sK0) )
    | spl8_1 ),
    inference(resolution,[],[f86,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_lattices(X0,X1,sK3(X0,X1)) != X1
      | k2_lattices(X0,sK3(X0,X1),X1) != X1
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f365,plain,
    ( spl8_1
    | ~ spl8_9
    | spl8_14 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | spl8_1
    | ~ spl8_9
    | spl8_14 ),
    inference(subsumption_resolution,[],[f363,f86])).

fof(f363,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_9
    | spl8_14 ),
    inference(subsumption_resolution,[],[f362,f148])).

fof(f362,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_14 ),
    inference(resolution,[],[f350,f53])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f350,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl8_14 ),
    inference(avatar_component_clause,[],[f348])).

fof(f305,plain,
    ( spl8_13
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f268,f173,f169,f147,f99,f94,f89,f84,f302])).

fof(f268,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f267,f86])).

fof(f267,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f259,f148])).

fof(f259,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12 ),
    inference(resolution,[],[f251,f53])).

fof(f186,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_12 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_12 ),
    inference(subsumption_resolution,[],[f184,f101])).

fof(f184,plain,
    ( ~ l3_lattices(sK0)
    | spl8_1
    | ~ spl8_2
    | spl8_12 ),
    inference(subsumption_resolution,[],[f183,f91])).

fof(f183,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl8_1
    | spl8_12 ),
    inference(subsumption_resolution,[],[f182,f86])).

fof(f182,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl8_12 ),
    inference(resolution,[],[f175,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f175,plain,
    ( ~ v8_lattices(sK0)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f173])).

fof(f181,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_11 ),
    inference(subsumption_resolution,[],[f179,f101])).

fof(f179,plain,
    ( ~ l3_lattices(sK0)
    | spl8_1
    | ~ spl8_2
    | spl8_11 ),
    inference(subsumption_resolution,[],[f178,f91])).

fof(f178,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl8_1
    | spl8_11 ),
    inference(subsumption_resolution,[],[f177,f86])).

fof(f177,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl8_11 ),
    inference(resolution,[],[f171,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f171,plain,
    ( ~ v9_lattices(sK0)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f169])).

fof(f158,plain,
    ( ~ spl8_4
    | spl8_9 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl8_4
    | spl8_9 ),
    inference(subsumption_resolution,[],[f156,f101])).

fof(f156,plain,
    ( ~ l3_lattices(sK0)
    | spl8_9 ),
    inference(resolution,[],[f149,f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f149,plain,
    ( ~ l1_lattices(sK0)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f155,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | spl8_7 ),
    inference(subsumption_resolution,[],[f153,f101])).

fof(f153,plain,
    ( ~ l3_lattices(sK0)
    | spl8_1
    | ~ spl8_2
    | spl8_7 ),
    inference(subsumption_resolution,[],[f152,f91])).

fof(f152,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl8_1
    | spl8_7 ),
    inference(subsumption_resolution,[],[f151,f86])).

fof(f151,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl8_7 ),
    inference(resolution,[],[f142,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f142,plain,
    ( ~ v6_lattices(sK0)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl8_7
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f150,plain,
    ( ~ spl8_7
    | spl8_8
    | ~ spl8_9
    | spl8_1 ),
    inference(avatar_split_clause,[],[f106,f84,f147,f144,f140])).

fof(f106,plain,
    ( ! [X6,X5] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k2_lattices(sK0,X5,X6) = k2_lattices(sK0,X6,X5)
        | ~ v6_lattices(sK0) )
    | spl8_1 ),
    inference(resolution,[],[f86,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
      | ~ v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).

fof(f125,plain,
    ( ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f82,f122,f118])).

fof(f82,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0) ),
    inference(global_subsumption,[],[f41,f39,f38,f37])).

fof(f37,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f102,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f41,f99])).

fof(f97,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f40,f94])).

fof(f40,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f92,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f39,f89])).

fof(f87,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f38,f84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:10:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (21112)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (21120)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (21113)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (21123)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.51  % (21119)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (21126)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.52  % (21115)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.52  % (21112)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f470,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f87,f92,f97,f102,f125,f150,f155,f158,f181,f186,f305,f365,f378,f467])).
% 0.20/0.52  fof(f467,plain,(
% 0.20/0.52    spl8_1 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_13 | ~spl8_14),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f466])).
% 0.20/0.52  fof(f466,plain,(
% 0.20/0.52    $false | (spl8_1 | ~spl8_4 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_13 | ~spl8_14)),
% 0.20/0.52    inference(subsumption_resolution,[],[f465,f126])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    ( ! [X14] : (m1_subset_1(k15_lattice3(sK0,X14),u1_struct_0(sK0))) ) | (spl8_1 | ~spl8_4)),
% 0.20/0.52    inference(subsumption_resolution,[],[f110,f101])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    l3_lattices(sK0) | ~spl8_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f99])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    spl8_4 <=> l3_lattices(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    ( ! [X14] : (~l3_lattices(sK0) | m1_subset_1(k15_lattice3(sK0,X14),u1_struct_0(sK0))) ) | spl8_1),
% 0.20/0.52    inference(resolution,[],[f86,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ~v2_struct_0(sK0) | spl8_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    spl8_1 <=> v2_struct_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.52  fof(f465,plain,(
% 0.20/0.52    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl8_1 | ~spl8_5 | spl8_6 | ~spl8_9 | ~spl8_13 | ~spl8_14)),
% 0.20/0.52    inference(subsumption_resolution,[],[f454,f124])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl8_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f122])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    spl8_6 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.52  fof(f454,plain,(
% 0.20/0.52    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl8_1 | ~spl8_5 | ~spl8_9 | ~spl8_13 | ~spl8_14)),
% 0.20/0.52    inference(superposition,[],[f304,f399])).
% 0.20/0.52  fof(f399,plain,(
% 0.20/0.52    ( ! [X4] : (k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | (spl8_1 | ~spl8_5 | ~spl8_9 | ~spl8_14)),
% 0.20/0.52    inference(subsumption_resolution,[],[f398,f349])).
% 0.20/0.52  fof(f349,plain,(
% 0.20/0.52    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl8_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f348])).
% 0.20/0.52  fof(f348,plain,(
% 0.20/0.52    spl8_14 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.52  fof(f398,plain,(
% 0.20/0.52    ( ! [X4] : (~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0))) ) | (spl8_1 | ~spl8_5 | ~spl8_9)),
% 0.20/0.52    inference(subsumption_resolution,[],[f397,f86])).
% 0.20/0.52  fof(f397,plain,(
% 0.20/0.52    ( ! [X4] : (v2_struct_0(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0))) ) | (~spl8_5 | ~spl8_9)),
% 0.20/0.52    inference(subsumption_resolution,[],[f387,f148])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    l1_lattices(sK0) | ~spl8_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f147])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    spl8_9 <=> l1_lattices(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.52  fof(f387,plain,(
% 0.20/0.52    ( ! [X4] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0))) ) | ~spl8_5),
% 0.20/0.52    inference(resolution,[],[f119,f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0))) )),
% 0.20/0.52    inference(equality_resolution,[],[f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X2,X1) = X1 | k5_lattices(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    v13_lattices(sK0) | ~spl8_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f118])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    spl8_5 <=> v13_lattices(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.52  fof(f304,plain,(
% 0.20/0.52    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~spl8_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f302])).
% 0.20/0.52  fof(f302,plain,(
% 0.20/0.52    spl8_13 <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.52  fof(f378,plain,(
% 0.20/0.52    spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | spl8_5 | ~spl8_8 | ~spl8_9 | ~spl8_11 | ~spl8_12),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f377])).
% 0.20/0.52  fof(f377,plain,(
% 0.20/0.52    $false | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | spl8_5 | ~spl8_8 | ~spl8_9 | ~spl8_11 | ~spl8_12)),
% 0.20/0.52    inference(subsumption_resolution,[],[f376,f126])).
% 0.20/0.52  fof(f376,plain,(
% 0.20/0.52    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | spl8_5 | ~spl8_8 | ~spl8_9 | ~spl8_11 | ~spl8_12)),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f375])).
% 0.20/0.52  fof(f375,plain,(
% 0.20/0.52    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | spl8_5 | ~spl8_8 | ~spl8_9 | ~spl8_11 | ~spl8_12)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f374])).
% 0.20/0.52  fof(f374,plain,(
% 0.20/0.52    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | spl8_5 | ~spl8_8 | ~spl8_9 | ~spl8_11 | ~spl8_12)),
% 0.20/0.52    inference(superposition,[],[f208,f271])).
% 0.20/0.52  fof(f271,plain,(
% 0.20/0.52    ( ! [X2] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | spl8_5 | ~spl8_9 | ~spl8_11 | ~spl8_12)),
% 0.20/0.52    inference(subsumption_resolution,[],[f270,f120])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    ~v13_lattices(sK0) | spl8_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f118])).
% 0.20/0.52  fof(f270,plain,(
% 0.20/0.52    ( ! [X2] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v13_lattices(sK0)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_9 | ~spl8_11 | ~spl8_12)),
% 0.20/0.52    inference(subsumption_resolution,[],[f269,f86])).
% 0.20/0.52  fof(f269,plain,(
% 0.20/0.52    ( ! [X2] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_9 | ~spl8_11 | ~spl8_12)),
% 0.20/0.52    inference(subsumption_resolution,[],[f262,f148])).
% 0.20/0.52  fof(f262,plain,(
% 0.20/0.52    ( ! [X2] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X2)) | ~l1_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_11 | ~spl8_12)),
% 0.20/0.52    inference(resolution,[],[f251,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | v13_lattices(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).
% 0.20/0.52  fof(f251,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_11 | ~spl8_12)),
% 0.20/0.52    inference(resolution,[],[f228,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.52  fof(f228,plain,(
% 0.20/0.52    ( ! [X4,X3] : (~r1_tarski(X4,sK7(sK0,X3,X4)) | k15_lattice3(sK0,X4) = k2_lattices(sK0,k15_lattice3(sK0,X4),X3) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_11 | ~spl8_12)),
% 0.20/0.52    inference(resolution,[],[f218,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.52  fof(f218,plain,(
% 0.20/0.52    ( ! [X4,X3] : (r2_hidden(sK7(sK0,X4,X3),X3) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k15_lattice3(sK0,X3) = k2_lattices(sK0,k15_lattice3(sK0,X3),X4)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_11 | ~spl8_12)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f216])).
% 0.20/0.52  fof(f216,plain,(
% 0.20/0.52    ( ! [X4,X3] : (k15_lattice3(sK0,X3) = k2_lattices(sK0,k15_lattice3(sK0,X3),X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r2_hidden(sK7(sK0,X4,X3),X3) | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_11 | ~spl8_12)),
% 0.20/0.52    inference(resolution,[],[f196,f137])).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    ( ! [X10,X11] : (r4_lattice3(sK0,X10,X11) | r2_hidden(sK7(sK0,X10,X11),X11) | ~m1_subset_1(X10,u1_struct_0(sK0))) ) | (spl8_1 | ~spl8_4)),
% 0.20/0.52    inference(subsumption_resolution,[],[f108,f101])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    ( ! [X10,X11] : (~l3_lattices(sK0) | ~m1_subset_1(X10,u1_struct_0(sK0)) | r2_hidden(sK7(sK0,X10,X11),X11) | r4_lattice3(sK0,X10,X11)) ) | spl8_1),
% 0.20/0.52    inference(resolution,[],[f86,f74])).
% 0.20/0.52  % (21110)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(sK7(X0,X1,X2),X2) | r4_lattice3(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 0.20/0.52  fof(f196,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_11 | ~spl8_12)),
% 0.20/0.52    inference(subsumption_resolution,[],[f195,f126])).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_11 | ~spl8_12)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f192])).
% 0.20/0.52  fof(f192,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_11 | ~spl8_12)),
% 0.20/0.52    inference(resolution,[],[f191,f132])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4)),
% 0.20/0.52    inference(subsumption_resolution,[],[f131,f86])).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f130,f101])).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f129,f96])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    v4_lattice3(sK0) | ~spl8_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f94])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    spl8_3 <=> v4_lattice3(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)) ) | (spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.20/0.53    inference(subsumption_resolution,[],[f127,f91])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    v10_lattices(sK0) | ~spl8_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    spl8_2 <=> v10_lattices(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)) ) | (spl8_1 | ~spl8_4)),
% 0.20/0.53    inference(resolution,[],[f126,f81])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r4_lattice3(X0,X3,X1) | r1_lattices(X0,k15_lattice3(X0,X1),X3)) )),
% 0.20/0.53    inference(equality_resolution,[],[f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r4_lattice3(X0,X3,X1) | r1_lattices(X0,X2,X3) | k15_lattice3(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~r1_lattices(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X2,X3) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (spl8_1 | ~spl8_4 | ~spl8_11 | ~spl8_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f190,f101])).
% 0.20/0.53  fof(f190,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X2,X3) = X2 | ~r1_lattices(sK0,X2,X3)) ) | (spl8_1 | ~spl8_11 | ~spl8_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f189,f170])).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    v9_lattices(sK0) | ~spl8_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f169])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    spl8_11 <=> v9_lattices(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.20/0.53  fof(f189,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X2,X3) = X2 | ~r1_lattices(sK0,X2,X3)) ) | (spl8_1 | ~spl8_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f104,f174])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    v8_lattices(sK0) | ~spl8_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f173])).
% 0.20/0.53  fof(f173,plain,(
% 0.20/0.53    spl8_12 <=> v8_lattices(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X2,X3) = X2 | ~r1_lattices(sK0,X2,X3)) ) | spl8_1),
% 0.20/0.53    inference(resolution,[],[f86,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 0.20/0.53  fof(f208,plain,(
% 0.20/0.53    ( ! [X0] : (k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl8_1 | spl8_5 | ~spl8_8 | ~spl8_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f207,f120])).
% 0.20/0.53  fof(f207,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | v13_lattices(sK0)) ) | (spl8_1 | spl8_5 | ~spl8_8 | ~spl8_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f206,f86])).
% 0.20/0.53  fof(f206,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (spl8_1 | spl8_5 | ~spl8_8 | ~spl8_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f205,f148])).
% 0.20/0.53  fof(f205,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~l1_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (spl8_1 | spl8_5 | ~spl8_8 | ~spl8_9)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f204])).
% 0.20/0.53  fof(f204,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~l1_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (spl8_1 | spl8_5 | ~spl8_8 | ~spl8_9)),
% 0.20/0.53    inference(resolution,[],[f201,f61])).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    ( ! [X1] : (~m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,sK3(sK0,X1)) != X1) ) | (spl8_1 | spl8_5 | ~spl8_8 | ~spl8_9)),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f200])).
% 0.20/0.53  fof(f200,plain,(
% 0.20/0.53    ( ! [X1] : (k2_lattices(sK0,X1,sK3(sK0,X1)) != X1 | k2_lattices(sK0,X1,sK3(sK0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl8_1 | spl8_5 | ~spl8_8 | ~spl8_9)),
% 0.20/0.53    inference(superposition,[],[f198,f145])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    ( ! [X6,X5] : (k2_lattices(sK0,X5,X6) = k2_lattices(sK0,X6,X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0))) ) | ~spl8_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f144])).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    spl8_8 <=> ! [X5,X6] : (~m1_subset_1(X5,u1_struct_0(sK0)) | k2_lattices(sK0,X5,X6) = k2_lattices(sK0,X6,X5) | ~m1_subset_1(X6,u1_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.53  fof(f198,plain,(
% 0.20/0.53    ( ! [X4] : (k2_lattices(sK0,sK3(sK0,X4),X4) != X4 | k2_lattices(sK0,X4,sK3(sK0,X4)) != X4 | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | (spl8_1 | spl8_5 | ~spl8_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f197,f120])).
% 0.20/0.53  fof(f197,plain,(
% 0.20/0.53    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,X4,sK3(sK0,X4)) != X4 | k2_lattices(sK0,sK3(sK0,X4),X4) != X4 | v13_lattices(sK0)) ) | (spl8_1 | ~spl8_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f105,f148])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    ( ! [X4] : (~l1_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,X4,sK3(sK0,X4)) != X4 | k2_lattices(sK0,sK3(sK0,X4),X4) != X4 | v13_lattices(sK0)) ) | spl8_1),
% 0.20/0.53    inference(resolution,[],[f86,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k2_lattices(X0,X1,sK3(X0,X1)) != X1 | k2_lattices(X0,sK3(X0,X1),X1) != X1 | v13_lattices(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f365,plain,(
% 0.20/0.53    spl8_1 | ~spl8_9 | spl8_14),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f364])).
% 0.20/0.53  fof(f364,plain,(
% 0.20/0.53    $false | (spl8_1 | ~spl8_9 | spl8_14)),
% 0.20/0.53    inference(subsumption_resolution,[],[f363,f86])).
% 0.20/0.53  fof(f363,plain,(
% 0.20/0.53    v2_struct_0(sK0) | (~spl8_9 | spl8_14)),
% 0.20/0.53    inference(subsumption_resolution,[],[f362,f148])).
% 0.20/0.53  fof(f362,plain,(
% 0.20/0.53    ~l1_lattices(sK0) | v2_struct_0(sK0) | spl8_14),
% 0.20/0.53    inference(resolution,[],[f350,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 0.20/0.53  fof(f350,plain,(
% 0.20/0.53    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | spl8_14),
% 0.20/0.53    inference(avatar_component_clause,[],[f348])).
% 0.20/0.53  fof(f305,plain,(
% 0.20/0.53    spl8_13 | spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_9 | ~spl8_11 | ~spl8_12),
% 0.20/0.53    inference(avatar_split_clause,[],[f268,f173,f169,f147,f99,f94,f89,f84,f302])).
% 0.20/0.53  fof(f268,plain,(
% 0.20/0.53    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_9 | ~spl8_11 | ~spl8_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f267,f86])).
% 0.20/0.53  fof(f267,plain,(
% 0.20/0.53    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_9 | ~spl8_11 | ~spl8_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f259,f148])).
% 0.20/0.53  fof(f259,plain,(
% 0.20/0.53    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_11 | ~spl8_12)),
% 0.20/0.53    inference(resolution,[],[f251,f53])).
% 0.20/0.53  fof(f186,plain,(
% 0.20/0.53    spl8_1 | ~spl8_2 | ~spl8_4 | spl8_12),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f185])).
% 0.20/0.53  fof(f185,plain,(
% 0.20/0.53    $false | (spl8_1 | ~spl8_2 | ~spl8_4 | spl8_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f184,f101])).
% 0.20/0.53  fof(f184,plain,(
% 0.20/0.53    ~l3_lattices(sK0) | (spl8_1 | ~spl8_2 | spl8_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f183,f91])).
% 0.20/0.53  fof(f183,plain,(
% 0.20/0.53    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl8_1 | spl8_12)),
% 0.20/0.53    inference(subsumption_resolution,[],[f182,f86])).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl8_12),
% 0.20/0.53    inference(resolution,[],[f175,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    ~v8_lattices(sK0) | spl8_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f173])).
% 0.20/0.53  fof(f181,plain,(
% 0.20/0.53    spl8_1 | ~spl8_2 | ~spl8_4 | spl8_11),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f180])).
% 0.20/0.53  fof(f180,plain,(
% 0.20/0.53    $false | (spl8_1 | ~spl8_2 | ~spl8_4 | spl8_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f179,f101])).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    ~l3_lattices(sK0) | (spl8_1 | ~spl8_2 | spl8_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f178,f91])).
% 0.20/0.53  fof(f178,plain,(
% 0.20/0.53    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl8_1 | spl8_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f177,f86])).
% 0.20/0.53  fof(f177,plain,(
% 0.20/0.53    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl8_11),
% 0.20/0.53    inference(resolution,[],[f171,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0] : (v9_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    ~v9_lattices(sK0) | spl8_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f169])).
% 0.20/0.53  fof(f158,plain,(
% 0.20/0.53    ~spl8_4 | spl8_9),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f157])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    $false | (~spl8_4 | spl8_9)),
% 0.20/0.53    inference(subsumption_resolution,[],[f156,f101])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    ~l3_lattices(sK0) | spl8_9),
% 0.20/0.53    inference(resolution,[],[f149,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.20/0.53  fof(f149,plain,(
% 0.20/0.53    ~l1_lattices(sK0) | spl8_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f147])).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    spl8_1 | ~spl8_2 | ~spl8_4 | spl8_7),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f154])).
% 0.20/0.53  fof(f154,plain,(
% 0.20/0.53    $false | (spl8_1 | ~spl8_2 | ~spl8_4 | spl8_7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f153,f101])).
% 0.20/0.53  fof(f153,plain,(
% 0.20/0.53    ~l3_lattices(sK0) | (spl8_1 | ~spl8_2 | spl8_7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f152,f91])).
% 0.20/0.53  fof(f152,plain,(
% 0.20/0.53    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl8_1 | spl8_7)),
% 0.20/0.53    inference(subsumption_resolution,[],[f151,f86])).
% 0.20/0.53  fof(f151,plain,(
% 0.20/0.53    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl8_7),
% 0.20/0.53    inference(resolution,[],[f142,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    ~v6_lattices(sK0) | spl8_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f140])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    spl8_7 <=> v6_lattices(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.53  fof(f150,plain,(
% 0.20/0.53    ~spl8_7 | spl8_8 | ~spl8_9 | spl8_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f106,f84,f147,f144,f140])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    ( ! [X6,X5] : (~l1_lattices(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | k2_lattices(sK0,X5,X6) = k2_lattices(sK0,X6,X5) | ~v6_lattices(sK0)) ) | spl8_1),
% 0.20/0.53    inference(resolution,[],[f86,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~v6_lattices(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    ~spl8_5 | ~spl8_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f82,f122,f118])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0)),
% 0.20/0.53    inference(global_subsumption,[],[f41,f39,f38,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(negated_conjecture,[],[f13])).
% 0.20/0.53  fof(f13,conjecture,(
% 0.20/0.53    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    v10_lattices(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    l3_lattices(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    spl8_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f41,f99])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    spl8_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f40,f94])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    v4_lattice3(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    spl8_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f39,f89])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ~spl8_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f38,f84])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (21112)------------------------------
% 0.20/0.53  % (21112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (21112)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (21112)Memory used [KB]: 10746
% 0.20/0.53  % (21112)Time elapsed: 0.079 s
% 0.20/0.53  % (21112)------------------------------
% 0.20/0.53  % (21112)------------------------------
% 0.20/0.53  % (21111)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.53  % (21108)Success in time 0.169 s
%------------------------------------------------------------------------------
