%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:51 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 563 expanded)
%              Number of leaves         :   30 ( 178 expanded)
%              Depth                    :   25
%              Number of atoms          : 1106 (3039 expanded)
%              Number of equality atoms :  153 ( 376 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1799,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f139,f144,f149,f154,f160,f169,f191,f202,f1110,f1298,f1786])).

fof(f1786,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(avatar_contradiction_clause,[],[f1785])).

fof(f1785,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f1784,f168])).

fof(f168,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl10_7
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f1784,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f1783,f174])).

fof(f174,plain,
    ( ! [X0] : m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
    | spl10_1
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f138,f153,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f153,plain,
    ( l3_lattices(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl10_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f138,plain,
    ( ~ v2_struct_0(sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl10_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f1783,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f1782,f1326])).

fof(f1326,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK1(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f1297,f512])).

fof(f512,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X5) )
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(duplicate_literal_removal,[],[f505])).

fof(f505,plain,
    ( ! [X5] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(resolution,[],[f354,f235])).

fof(f235,plain,
    ( ! [X16] :
        ( r4_lattice3(sK0,X16,k1_xboole_0)
        | ~ m1_subset_1(X16,u1_struct_0(sK0)) )
    | spl10_1
    | ~ spl10_4 ),
    inference(resolution,[],[f186,f170])).

fof(f170,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f80,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f80,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f186,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK7(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1) )
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f185,f138])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK7(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl10_4 ),
    inference(resolution,[],[f110,f153])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | r2_hidden(sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r4_lattice3(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK7(X0,X1,X2),X1)
        & r2_hidden(sK7(X0,X1,X2),X2)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
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
    inference(rectify,[],[f66])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f354,plain,
    ( ! [X2,X1] :
        ( ~ r4_lattice3(sK0,X1,X2)
        | k15_lattice3(sK0,X2) = k2_lattices(sK0,k15_lattice3(sK0,X2),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f353,f138])).

fof(f353,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k15_lattice3(sK0,X2) = k2_lattices(sK0,k15_lattice3(sK0,X2),X1)
        | ~ r4_lattice3(sK0,X1,X2)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f352,f143])).

fof(f143,plain,
    ( v10_lattices(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl10_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f352,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k15_lattice3(sK0,X2) = k2_lattices(sK0,k15_lattice3(sK0,X2),X1)
        | ~ r4_lattice3(sK0,X1,X2)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f351,f148])).

fof(f148,plain,
    ( v4_lattice3(sK0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl10_3
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f351,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k15_lattice3(sK0,X2) = k2_lattices(sK0,k15_lattice3(sK0,X2),X1)
        | ~ r4_lattice3(sK0,X1,X2)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f350,f153])).

fof(f350,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k15_lattice3(sK0,X2) = k2_lattices(sK0,k15_lattice3(sK0,X2),X1)
        | ~ r4_lattice3(sK0,X1,X2)
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f348,f174])).

fof(f348,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))
        | k15_lattice3(sK0,X2) = k2_lattices(sK0,k15_lattice3(sK0,X2),X1)
        | ~ r4_lattice3(sK0,X1,X2)
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(duplicate_literal_removal,[],[f347])).

fof(f347,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))
        | k15_lattice3(sK0,X2) = k2_lattices(sK0,k15_lattice3(sK0,X2),X1)
        | ~ r4_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(resolution,[],[f213,f134])).

fof(f134,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f126,f112])).

fof(f126,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
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
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
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
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK6(X0,X1,X2))
                & r4_lattice3(X0,sK6(X0,X1,X2),X1)
                & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f63,f64])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK6(X0,X1,X2))
        & r4_lattice3(X0,sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
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
    inference(rectify,[],[f62])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f213,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = X0 )
    | spl10_1
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f212,f138])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = X0
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f211,f190])).

fof(f190,plain,
    ( v8_lattices(sK0)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl10_9
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = X0
        | ~ v8_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f210,f153])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | k2_lattices(sK0,X0,X1) = X0
        | ~ v8_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_10 ),
    inference(resolution,[],[f201,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f201,plain,
    ( v9_lattices(sK0)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl10_10
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f1297,plain,
    ( m1_subset_1(sK1(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f1295])).

fof(f1295,plain,
    ( spl10_12
  <=> m1_subset_1(sK1(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f1782,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK1(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_12 ),
    inference(duplicate_literal_removal,[],[f1779])).

fof(f1779,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK1(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK1(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_12 ),
    inference(superposition,[],[f1172,f1345])).

fof(f1345,plain,
    ( ! [X0] : k2_lattices(sK0,sK1(sK0,k15_lattice3(sK0,k1_xboole_0)),k15_lattice3(sK0,X0)) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK1(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f153,f143,f138,f174,f1297,f194])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f193,f81])).

fof(f81,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | ~ l1_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | ~ l1_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f97,f83])).

fof(f83,plain,(
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
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
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
    inference(pure_predicate_removal,[],[f3])).

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

fof(f97,plain,(
    ! [X4,X0,X3] :
      ( ~ v6_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f57,f59,f58])).

fof(f58,plain,(
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

fof(f59,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f1172,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,sK1(sK0,X0),X0) != X0
        | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = X0 )
    | spl10_1
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f1171,f138])).

fof(f1171,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,sK1(sK0,X0),X0) != X0
        | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = X0
        | v2_struct_0(sK0) )
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f1168,f159])).

fof(f159,plain,
    ( l1_lattices(sK0)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl10_5
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f1168,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,sK1(sK0,X0),X0) != X0
        | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = X0
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_6 ),
    inference(resolution,[],[f163,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v13_lattices(X0)
      | k2_lattices(X0,sK1(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK1(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k5_lattices(X0) = X1
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f163,plain,
    ( v13_lattices(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl10_6
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f1298,plain,
    ( spl10_12
    | spl10_1
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7 ),
    inference(avatar_split_clause,[],[f1182,f166,f162,f157,f151,f136,f1295])).

fof(f1182,plain,
    ( m1_subset_1(sK1(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl10_1
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7 ),
    inference(unit_resulting_resolution,[],[f138,f159,f163,f174,f168,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | k5_lattices(X0) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1110,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(avatar_contradiction_clause,[],[f1109])).

fof(f1109,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f1062,f215])).

fof(f215,plain,
    ( ! [X0] : m1_subset_1(sK2(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))
    | spl10_1
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f138,f159,f164,f174,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f52,f54,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f164,plain,
    ( ~ v13_lattices(sK0)
    | spl10_6 ),
    inference(avatar_component_clause,[],[f162])).

fof(f1062,plain,
    ( ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f153,f138,f143,f174,f391,f553,f197])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f196,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f86,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f553,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f552,f138])).

fof(f552,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f551,f159])).

fof(f551,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f550,f174])).

fof(f550,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(subsumption_resolution,[],[f543,f164])).

fof(f543,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | v13_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(duplicate_literal_removal,[],[f541])).

fof(f541,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | v13_lattices(sK0)
        | k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(superposition,[],[f96,f262])).

fof(f262,plain,
    ( ! [X0,X1] : k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,X0))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f153,f143,f138,f174,f215,f194])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_lattices(X0,sK2(X0,X1),X1) != X1
      | v13_lattices(X0)
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f391,plain,
    ( ! [X0] : r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X0)))
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f138,f143,f148,f153,f215,f258,f134])).

fof(f258,plain,
    ( ! [X0] : r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X0)),k1_xboole_0)
    | spl10_1
    | ~ spl10_4
    | ~ spl10_5
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f138,f153,f170,f215,f110])).

fof(f202,plain,
    ( spl10_10
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f173,f151,f141,f136,f199])).

fof(f173,plain,
    ( v9_lattices(sK0)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f153,f138,f143,f85])).

fof(f191,plain,
    ( spl10_9
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f172,f151,f141,f136,f188])).

fof(f172,plain,
    ( v8_lattices(sK0)
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f153,f138,f143,f84])).

fof(f169,plain,
    ( ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f132,f166,f162])).

fof(f132,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f131,f75])).

fof(f75,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f44])).

fof(f44,plain,
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f131,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f130,f76])).

fof(f76,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f130,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f79,f78])).

fof(f78,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f160,plain,
    ( spl10_5
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f155,f151,f157])).

fof(f155,plain,
    ( l1_lattices(sK0)
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f153,f81])).

fof(f154,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f78,f151])).

fof(f149,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f77,f146])).

fof(f77,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f144,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f76,f141])).

fof(f139,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f75,f136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 10:20:45 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.50  % (14086)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.51  % (14078)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.52  % (14076)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.52  % (14085)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.52  % (14084)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.52  % (14081)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.52  % (14085)Refutation not found, incomplete strategy% (14085)------------------------------
% 0.23/0.52  % (14085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (14085)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (14085)Memory used [KB]: 10490
% 0.23/0.52  % (14085)Time elapsed: 0.004 s
% 0.23/0.52  % (14085)------------------------------
% 0.23/0.52  % (14085)------------------------------
% 0.23/0.52  % (14088)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.53  % (14092)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.53  % (14098)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.53  % (14094)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.53  % (14090)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.23/0.53  % (14077)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.53  % (14089)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.54  % (14075)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.54  % (14080)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.27/0.54  % (14080)Refutation not found, incomplete strategy% (14080)------------------------------
% 1.27/0.54  % (14080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (14080)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (14080)Memory used [KB]: 10490
% 1.27/0.54  % (14080)Time elapsed: 0.002 s
% 1.27/0.54  % (14080)------------------------------
% 1.27/0.54  % (14080)------------------------------
% 1.27/0.54  % (14095)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.27/0.54  % (14097)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.27/0.54  % (14096)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.27/0.54  % (14079)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.27/0.54  % (14099)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.27/0.55  % (14082)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.27/0.55  % (14074)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.27/0.55  % (14074)Refutation not found, incomplete strategy% (14074)------------------------------
% 1.27/0.55  % (14074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (14074)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (14074)Memory used [KB]: 10490
% 1.27/0.55  % (14074)Time elapsed: 0.002 s
% 1.27/0.55  % (14074)------------------------------
% 1.27/0.55  % (14074)------------------------------
% 1.27/0.55  % (14091)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.27/0.55  % (14087)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.27/0.55  % (14087)Refutation not found, incomplete strategy% (14087)------------------------------
% 1.27/0.55  % (14087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (14087)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (14087)Memory used [KB]: 6140
% 1.27/0.55  % (14087)Time elapsed: 0.126 s
% 1.27/0.55  % (14087)------------------------------
% 1.27/0.55  % (14087)------------------------------
% 1.45/0.56  % (14083)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.45/0.57  % (14093)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 2.02/0.63  % (14097)Refutation found. Thanks to Tanya!
% 2.02/0.63  % SZS status Theorem for theBenchmark
% 2.02/0.65  % SZS output start Proof for theBenchmark
% 2.02/0.65  fof(f1799,plain,(
% 2.02/0.65    $false),
% 2.02/0.65    inference(avatar_sat_refutation,[],[f139,f144,f149,f154,f160,f169,f191,f202,f1110,f1298,f1786])).
% 2.02/0.65  fof(f1786,plain,(
% 2.02/0.65    spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_9 | ~spl10_10 | ~spl10_12),
% 2.02/0.65    inference(avatar_contradiction_clause,[],[f1785])).
% 2.02/0.65  fof(f1785,plain,(
% 2.02/0.65    $false | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7 | ~spl10_9 | ~spl10_10 | ~spl10_12)),
% 2.02/0.65    inference(subsumption_resolution,[],[f1784,f168])).
% 2.02/0.65  fof(f168,plain,(
% 2.02/0.65    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl10_7),
% 2.02/0.65    inference(avatar_component_clause,[],[f166])).
% 2.02/0.65  fof(f166,plain,(
% 2.02/0.65    spl10_7 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 2.02/0.65  fof(f1784,plain,(
% 2.02/0.65    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_9 | ~spl10_10 | ~spl10_12)),
% 2.02/0.65    inference(subsumption_resolution,[],[f1783,f174])).
% 2.02/0.65  fof(f174,plain,(
% 2.02/0.65    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl10_1 | ~spl10_4)),
% 2.02/0.65    inference(unit_resulting_resolution,[],[f138,f153,f112])).
% 2.02/0.65  fof(f112,plain,(
% 2.02/0.65    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f40])).
% 2.02/0.65  fof(f40,plain,(
% 2.02/0.65    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(flattening,[],[f39])).
% 2.02/0.65  fof(f39,plain,(
% 2.02/0.65    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.02/0.65    inference(ennf_transformation,[],[f11])).
% 2.02/0.65  fof(f11,axiom,(
% 2.02/0.65    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 2.02/0.65  fof(f153,plain,(
% 2.02/0.65    l3_lattices(sK0) | ~spl10_4),
% 2.02/0.65    inference(avatar_component_clause,[],[f151])).
% 2.02/0.65  fof(f151,plain,(
% 2.02/0.65    spl10_4 <=> l3_lattices(sK0)),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 2.02/0.65  fof(f138,plain,(
% 2.02/0.65    ~v2_struct_0(sK0) | spl10_1),
% 2.02/0.65    inference(avatar_component_clause,[],[f136])).
% 2.02/0.65  fof(f136,plain,(
% 2.02/0.65    spl10_1 <=> v2_struct_0(sK0)),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 2.02/0.65  fof(f1783,plain,(
% 2.02/0.65    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_9 | ~spl10_10 | ~spl10_12)),
% 2.02/0.65    inference(subsumption_resolution,[],[f1782,f1326])).
% 2.02/0.65  fof(f1326,plain,(
% 2.02/0.65    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK1(sK0,k15_lattice3(sK0,k1_xboole_0))) | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_9 | ~spl10_10 | ~spl10_12)),
% 2.02/0.65    inference(unit_resulting_resolution,[],[f1297,f512])).
% 2.02/0.65  fof(f512,plain,(
% 2.02/0.65    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X5)) ) | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_9 | ~spl10_10)),
% 2.02/0.65    inference(duplicate_literal_removal,[],[f505])).
% 2.02/0.65  fof(f505,plain,(
% 2.02/0.65    ( ! [X5] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_9 | ~spl10_10)),
% 2.02/0.65    inference(resolution,[],[f354,f235])).
% 2.02/0.65  fof(f235,plain,(
% 2.02/0.65    ( ! [X16] : (r4_lattice3(sK0,X16,k1_xboole_0) | ~m1_subset_1(X16,u1_struct_0(sK0))) ) | (spl10_1 | ~spl10_4)),
% 2.02/0.65    inference(resolution,[],[f186,f170])).
% 2.02/0.65  fof(f170,plain,(
% 2.02/0.65    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.02/0.65    inference(unit_resulting_resolution,[],[f80,f113])).
% 2.02/0.65  fof(f113,plain,(
% 2.02/0.65    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f41])).
% 2.02/0.65  fof(f41,plain,(
% 2.02/0.65    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.02/0.65    inference(ennf_transformation,[],[f2])).
% 2.02/0.65  fof(f2,axiom,(
% 2.02/0.65    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.02/0.65  fof(f80,plain,(
% 2.02/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f1])).
% 2.02/0.65  fof(f1,axiom,(
% 2.02/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.02/0.65  fof(f186,plain,(
% 2.02/0.65    ( ! [X0,X1] : (r2_hidden(sK7(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1)) ) | (spl10_1 | ~spl10_4)),
% 2.02/0.65    inference(subsumption_resolution,[],[f185,f138])).
% 2.02/0.65  fof(f185,plain,(
% 2.02/0.65    ( ! [X0,X1] : (r2_hidden(sK7(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1) | v2_struct_0(sK0)) ) | ~spl10_4),
% 2.02/0.65    inference(resolution,[],[f110,f153])).
% 2.02/0.65  fof(f110,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (~l3_lattices(X0) | r2_hidden(sK7(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r4_lattice3(X0,X1,X2) | v2_struct_0(X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f69])).
% 2.02/0.65  fof(f69,plain,(
% 2.02/0.65    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X2) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f67,f68])).
% 2.02/0.65  fof(f68,plain,(
% 2.02/0.65    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X2) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 2.02/0.65    introduced(choice_axiom,[])).
% 2.02/0.65  fof(f67,plain,(
% 2.02/0.65    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(rectify,[],[f66])).
% 2.02/0.65  fof(f66,plain,(
% 2.02/0.65    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(nnf_transformation,[],[f38])).
% 2.02/0.65  fof(f38,plain,(
% 2.02/0.65    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(flattening,[],[f37])).
% 2.02/0.65  fof(f37,plain,(
% 2.02/0.65    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.02/0.65    inference(ennf_transformation,[],[f8])).
% 2.02/0.65  fof(f8,axiom,(
% 2.02/0.65    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 2.02/0.65  fof(f354,plain,(
% 2.02/0.65    ( ! [X2,X1] : (~r4_lattice3(sK0,X1,X2) | k15_lattice3(sK0,X2) = k2_lattices(sK0,k15_lattice3(sK0,X2),X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_9 | ~spl10_10)),
% 2.02/0.65    inference(subsumption_resolution,[],[f353,f138])).
% 2.02/0.65  fof(f353,plain,(
% 2.02/0.65    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k15_lattice3(sK0,X2) = k2_lattices(sK0,k15_lattice3(sK0,X2),X1) | ~r4_lattice3(sK0,X1,X2) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_9 | ~spl10_10)),
% 2.02/0.65    inference(subsumption_resolution,[],[f352,f143])).
% 2.02/0.65  fof(f143,plain,(
% 2.02/0.65    v10_lattices(sK0) | ~spl10_2),
% 2.02/0.65    inference(avatar_component_clause,[],[f141])).
% 2.02/0.65  fof(f141,plain,(
% 2.02/0.65    spl10_2 <=> v10_lattices(sK0)),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 2.02/0.65  fof(f352,plain,(
% 2.02/0.65    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k15_lattice3(sK0,X2) = k2_lattices(sK0,k15_lattice3(sK0,X2),X1) | ~r4_lattice3(sK0,X1,X2) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_3 | ~spl10_4 | ~spl10_9 | ~spl10_10)),
% 2.02/0.65    inference(subsumption_resolution,[],[f351,f148])).
% 2.02/0.65  fof(f148,plain,(
% 2.02/0.65    v4_lattice3(sK0) | ~spl10_3),
% 2.02/0.65    inference(avatar_component_clause,[],[f146])).
% 2.02/0.65  fof(f146,plain,(
% 2.02/0.65    spl10_3 <=> v4_lattice3(sK0)),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 2.02/0.65  fof(f351,plain,(
% 2.02/0.65    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k15_lattice3(sK0,X2) = k2_lattices(sK0,k15_lattice3(sK0,X2),X1) | ~r4_lattice3(sK0,X1,X2) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_4 | ~spl10_9 | ~spl10_10)),
% 2.02/0.65    inference(subsumption_resolution,[],[f350,f153])).
% 2.02/0.65  fof(f350,plain,(
% 2.02/0.65    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k15_lattice3(sK0,X2) = k2_lattices(sK0,k15_lattice3(sK0,X2),X1) | ~r4_lattice3(sK0,X1,X2) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_4 | ~spl10_9 | ~spl10_10)),
% 2.02/0.65    inference(subsumption_resolution,[],[f348,f174])).
% 2.02/0.65  fof(f348,plain,(
% 2.02/0.65    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0)) | k15_lattice3(sK0,X2) = k2_lattices(sK0,k15_lattice3(sK0,X2),X1) | ~r4_lattice3(sK0,X1,X2) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_4 | ~spl10_9 | ~spl10_10)),
% 2.02/0.65    inference(duplicate_literal_removal,[],[f347])).
% 2.02/0.65  fof(f347,plain,(
% 2.02/0.65    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0)) | k15_lattice3(sK0,X2) = k2_lattices(sK0,k15_lattice3(sK0,X2),X1) | ~r4_lattice3(sK0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_4 | ~spl10_9 | ~spl10_10)),
% 2.02/0.65    inference(resolution,[],[f213,f134])).
% 2.02/0.65  fof(f134,plain,(
% 2.02/0.65    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.02/0.65    inference(subsumption_resolution,[],[f126,f112])).
% 2.02/0.65  fof(f126,plain,(
% 2.02/0.65    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.02/0.65    inference(duplicate_literal_removal,[],[f122])).
% 2.02/0.65  fof(f122,plain,(
% 2.02/0.65    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.02/0.65    inference(equality_resolution,[],[f104])).
% 2.02/0.65  fof(f104,plain,(
% 2.02/0.65    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f65])).
% 2.02/0.65  fof(f65,plain,(
% 2.02/0.65    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK6(X0,X1,X2)) & r4_lattice3(X0,sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f63,f64])).
% 2.02/0.65  fof(f64,plain,(
% 2.02/0.65    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK6(X0,X1,X2)) & r4_lattice3(X0,sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 2.02/0.65    introduced(choice_axiom,[])).
% 2.02/0.65  fof(f63,plain,(
% 2.02/0.65    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(rectify,[],[f62])).
% 2.02/0.65  fof(f62,plain,(
% 2.02/0.65    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(flattening,[],[f61])).
% 2.02/0.65  fof(f61,plain,(
% 2.02/0.65    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(nnf_transformation,[],[f36])).
% 2.02/0.65  fof(f36,plain,(
% 2.02/0.65    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(flattening,[],[f35])).
% 2.02/0.65  fof(f35,plain,(
% 2.02/0.65    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.02/0.65    inference(ennf_transformation,[],[f9])).
% 2.02/0.65  fof(f9,axiom,(
% 2.02/0.65    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 2.02/0.65  fof(f213,plain,(
% 2.02/0.65    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0) ) | (spl10_1 | ~spl10_4 | ~spl10_9 | ~spl10_10)),
% 2.02/0.65    inference(subsumption_resolution,[],[f212,f138])).
% 2.02/0.65  fof(f212,plain,(
% 2.02/0.65    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0 | v2_struct_0(sK0)) ) | (~spl10_4 | ~spl10_9 | ~spl10_10)),
% 2.02/0.65    inference(subsumption_resolution,[],[f211,f190])).
% 2.02/0.65  fof(f190,plain,(
% 2.02/0.65    v8_lattices(sK0) | ~spl10_9),
% 2.02/0.65    inference(avatar_component_clause,[],[f188])).
% 2.02/0.65  fof(f188,plain,(
% 2.02/0.65    spl10_9 <=> v8_lattices(sK0)),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 2.02/0.65  fof(f211,plain,(
% 2.02/0.65    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0 | ~v8_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl10_4 | ~spl10_10)),
% 2.02/0.65    inference(subsumption_resolution,[],[f210,f153])).
% 2.02/0.65  fof(f210,plain,(
% 2.02/0.65    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k2_lattices(sK0,X0,X1) = X0 | ~v8_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl10_10),
% 2.02/0.65    inference(resolution,[],[f201,f86])).
% 2.02/0.65  fof(f86,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f46])).
% 2.02/0.65  fof(f46,plain,(
% 2.02/0.65    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(nnf_transformation,[],[f26])).
% 2.02/0.65  fof(f26,plain,(
% 2.02/0.65    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(flattening,[],[f25])).
% 2.02/0.65  fof(f25,plain,(
% 2.02/0.65    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 2.02/0.65    inference(ennf_transformation,[],[f6])).
% 2.02/0.65  fof(f6,axiom,(
% 2.02/0.65    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 2.02/0.65  fof(f201,plain,(
% 2.02/0.65    v9_lattices(sK0) | ~spl10_10),
% 2.02/0.65    inference(avatar_component_clause,[],[f199])).
% 2.02/0.65  fof(f199,plain,(
% 2.02/0.65    spl10_10 <=> v9_lattices(sK0)),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 2.02/0.65  fof(f1297,plain,(
% 2.02/0.65    m1_subset_1(sK1(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | ~spl10_12),
% 2.02/0.65    inference(avatar_component_clause,[],[f1295])).
% 2.02/0.65  fof(f1295,plain,(
% 2.02/0.65    spl10_12 <=> m1_subset_1(sK1(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 2.02/0.65  fof(f1782,plain,(
% 2.02/0.65    k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK1(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | (spl10_1 | ~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_12)),
% 2.02/0.65    inference(duplicate_literal_removal,[],[f1779])).
% 2.02/0.65  fof(f1779,plain,(
% 2.02/0.65    k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK1(sK0,k15_lattice3(sK0,k1_xboole_0))) | k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK1(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | (spl10_1 | ~spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_12)),
% 2.02/0.65    inference(superposition,[],[f1172,f1345])).
% 2.02/0.65  fof(f1345,plain,(
% 2.02/0.65    ( ! [X0] : (k2_lattices(sK0,sK1(sK0,k15_lattice3(sK0,k1_xboole_0)),k15_lattice3(sK0,X0)) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK1(sK0,k15_lattice3(sK0,k1_xboole_0)))) ) | (spl10_1 | ~spl10_2 | ~spl10_4 | ~spl10_12)),
% 2.02/0.65    inference(unit_resulting_resolution,[],[f153,f143,f138,f174,f1297,f194])).
% 2.02/0.65  fof(f194,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1)) )),
% 2.02/0.65    inference(subsumption_resolution,[],[f193,f81])).
% 2.02/0.65  fof(f81,plain,(
% 2.02/0.65    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f22])).
% 2.02/0.65  fof(f22,plain,(
% 2.02/0.65    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 2.02/0.65    inference(ennf_transformation,[],[f16])).
% 2.02/0.65  fof(f16,plain,(
% 2.02/0.65    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 2.02/0.65    inference(pure_predicate_removal,[],[f5])).
% 2.02/0.65  fof(f5,axiom,(
% 2.02/0.65    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 2.02/0.65  fof(f193,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | ~l1_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1)) )),
% 2.02/0.65    inference(duplicate_literal_removal,[],[f192])).
% 2.02/0.65  fof(f192,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | ~l1_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 2.02/0.65    inference(resolution,[],[f97,f83])).
% 2.02/0.65  fof(f83,plain,(
% 2.02/0.65    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f24])).
% 2.02/0.65  fof(f24,plain,(
% 2.02/0.65    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.02/0.65    inference(flattening,[],[f23])).
% 2.02/0.65  fof(f23,plain,(
% 2.02/0.65    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.02/0.65    inference(ennf_transformation,[],[f19])).
% 2.02/0.65  fof(f19,plain,(
% 2.02/0.65    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 2.02/0.65    inference(pure_predicate_removal,[],[f18])).
% 2.02/0.65  fof(f18,plain,(
% 2.02/0.65    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.02/0.65    inference(pure_predicate_removal,[],[f17])).
% 2.02/0.65  fof(f17,plain,(
% 2.02/0.65    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.02/0.65    inference(pure_predicate_removal,[],[f3])).
% 2.02/0.65  fof(f3,axiom,(
% 2.02/0.65    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 2.02/0.65  fof(f97,plain,(
% 2.02/0.65    ( ! [X4,X0,X3] : (~v6_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f60])).
% 2.02/0.65  fof(f60,plain,(
% 2.02/0.65    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f57,f59,f58])).
% 2.02/0.65  fof(f58,plain,(
% 2.02/0.65    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 2.02/0.65    introduced(choice_axiom,[])).
% 2.02/0.65  fof(f59,plain,(
% 2.02/0.65    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 2.02/0.65    introduced(choice_axiom,[])).
% 2.02/0.65  fof(f57,plain,(
% 2.02/0.65    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(rectify,[],[f56])).
% 2.02/0.65  fof(f56,plain,(
% 2.02/0.65    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(nnf_transformation,[],[f32])).
% 2.02/0.65  fof(f32,plain,(
% 2.02/0.65    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(flattening,[],[f31])).
% 2.02/0.65  fof(f31,plain,(
% 2.02/0.65    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.02/0.65    inference(ennf_transformation,[],[f10])).
% 2.02/0.65  fof(f10,axiom,(
% 2.02/0.65    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).
% 2.02/0.65  fof(f1172,plain,(
% 2.02/0.65    ( ! [X0] : (k2_lattices(sK0,sK1(sK0,X0),X0) != X0 | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = X0) ) | (spl10_1 | ~spl10_5 | ~spl10_6)),
% 2.02/0.65    inference(subsumption_resolution,[],[f1171,f138])).
% 2.02/0.65  fof(f1171,plain,(
% 2.02/0.65    ( ! [X0] : (k2_lattices(sK0,sK1(sK0,X0),X0) != X0 | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = X0 | v2_struct_0(sK0)) ) | (~spl10_5 | ~spl10_6)),
% 2.02/0.65    inference(subsumption_resolution,[],[f1168,f159])).
% 2.02/0.65  fof(f159,plain,(
% 2.02/0.65    l1_lattices(sK0) | ~spl10_5),
% 2.02/0.65    inference(avatar_component_clause,[],[f157])).
% 2.02/0.65  fof(f157,plain,(
% 2.02/0.65    spl10_5 <=> l1_lattices(sK0)),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 2.02/0.65  fof(f1168,plain,(
% 2.02/0.65    ( ! [X0] : (k2_lattices(sK0,sK1(sK0,X0),X0) != X0 | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = X0 | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl10_6),
% 2.02/0.65    inference(resolution,[],[f163,f91])).
% 2.02/0.65  fof(f91,plain,(
% 2.02/0.65    ( ! [X0,X1] : (~v13_lattices(X0) | k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | k5_lattices(X0) = X1 | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f50])).
% 2.02/0.65  fof(f50,plain,(
% 2.02/0.65    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).
% 2.02/0.65  fof(f49,plain,(
% 2.02/0.65    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 2.02/0.65    introduced(choice_axiom,[])).
% 2.02/0.65  fof(f48,plain,(
% 2.02/0.65    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(rectify,[],[f47])).
% 2.02/0.65  fof(f47,plain,(
% 2.02/0.65    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(nnf_transformation,[],[f28])).
% 2.02/0.65  fof(f28,plain,(
% 2.02/0.65    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(flattening,[],[f27])).
% 2.02/0.65  fof(f27,plain,(
% 2.02/0.65    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.02/0.65    inference(ennf_transformation,[],[f4])).
% 2.02/0.65  fof(f4,axiom,(
% 2.02/0.65    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 2.02/0.65  fof(f163,plain,(
% 2.02/0.65    v13_lattices(sK0) | ~spl10_6),
% 2.02/0.65    inference(avatar_component_clause,[],[f162])).
% 2.02/0.65  fof(f162,plain,(
% 2.02/0.65    spl10_6 <=> v13_lattices(sK0)),
% 2.02/0.65    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 2.02/0.65  fof(f1298,plain,(
% 2.02/0.65    spl10_12 | spl10_1 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7),
% 2.02/0.65    inference(avatar_split_clause,[],[f1182,f166,f162,f157,f151,f136,f1295])).
% 2.02/0.65  fof(f1182,plain,(
% 2.02/0.65    m1_subset_1(sK1(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl10_1 | ~spl10_4 | ~spl10_5 | ~spl10_6 | spl10_7)),
% 2.02/0.65    inference(unit_resulting_resolution,[],[f138,f159,f163,f174,f168,f90])).
% 2.02/0.65  fof(f90,plain,(
% 2.02/0.65    ( ! [X0,X1] : (m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | k5_lattices(X0) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f50])).
% 2.02/0.65  fof(f1110,plain,(
% 2.02/0.65    spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6),
% 2.02/0.65    inference(avatar_contradiction_clause,[],[f1109])).
% 2.02/0.65  fof(f1109,plain,(
% 2.02/0.65    $false | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 2.02/0.65    inference(subsumption_resolution,[],[f1062,f215])).
% 2.02/0.65  fof(f215,plain,(
% 2.02/0.65    ( ! [X0] : (m1_subset_1(sK2(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))) ) | (spl10_1 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 2.02/0.65    inference(unit_resulting_resolution,[],[f138,f159,f164,f174,f95])).
% 2.02/0.65  fof(f95,plain,(
% 2.02/0.65    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f55])).
% 2.02/0.65  fof(f55,plain,(
% 2.02/0.65    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f52,f54,f53])).
% 2.02/0.65  fof(f53,plain,(
% 2.02/0.65    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 2.02/0.65    introduced(choice_axiom,[])).
% 2.02/0.65  fof(f54,plain,(
% 2.02/0.65    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 2.02/0.65    introduced(choice_axiom,[])).
% 2.02/0.65  fof(f52,plain,(
% 2.02/0.65    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(rectify,[],[f51])).
% 2.02/0.65  fof(f51,plain,(
% 2.02/0.65    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(nnf_transformation,[],[f30])).
% 2.02/0.65  fof(f30,plain,(
% 2.02/0.65    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.02/0.65    inference(flattening,[],[f29])).
% 2.02/0.65  fof(f29,plain,(
% 2.02/0.65    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.02/0.65    inference(ennf_transformation,[],[f7])).
% 2.02/0.65  fof(f7,axiom,(
% 2.02/0.65    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).
% 2.02/0.65  fof(f164,plain,(
% 2.02/0.65    ~v13_lattices(sK0) | spl10_6),
% 2.02/0.65    inference(avatar_component_clause,[],[f162])).
% 2.02/0.65  fof(f1062,plain,(
% 2.02/0.65    ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 2.02/0.65    inference(unit_resulting_resolution,[],[f153,f138,f143,f174,f391,f553,f197])).
% 2.02/0.65  fof(f197,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | v2_struct_0(X0) | ~r1_lattices(X0,X1,X2)) )),
% 2.02/0.65    inference(subsumption_resolution,[],[f196,f84])).
% 2.02/0.66  fof(f84,plain,(
% 2.02/0.66    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f24])).
% 2.02/0.66  fof(f196,plain,(
% 2.02/0.66    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 2.02/0.66    inference(duplicate_literal_removal,[],[f195])).
% 2.02/0.66  fof(f195,plain,(
% 2.02/0.66    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.02/0.66    inference(resolution,[],[f86,f85])).
% 2.02/0.66  fof(f85,plain,(
% 2.02/0.66    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f24])).
% 2.02/0.66  fof(f553,plain,(
% 2.02/0.66    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))) ) | (spl10_1 | ~spl10_2 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 2.02/0.66    inference(subsumption_resolution,[],[f552,f138])).
% 2.02/0.66  fof(f552,plain,(
% 2.02/0.66    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_2 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 2.02/0.66    inference(subsumption_resolution,[],[f551,f159])).
% 2.02/0.66  fof(f551,plain,(
% 2.02/0.66    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_2 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 2.02/0.66    inference(subsumption_resolution,[],[f550,f174])).
% 2.02/0.66  fof(f550,plain,(
% 2.02/0.66    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_2 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 2.02/0.66    inference(subsumption_resolution,[],[f543,f164])).
% 2.02/0.66  fof(f543,plain,(
% 2.02/0.66    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | v13_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_2 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 2.02/0.66    inference(duplicate_literal_removal,[],[f541])).
% 2.02/0.66  fof(f541,plain,(
% 2.02/0.66    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | v13_lattices(sK0) | k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl10_1 | ~spl10_2 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 2.02/0.66    inference(superposition,[],[f96,f262])).
% 2.02/0.66  fof(f262,plain,(
% 2.02/0.66    ( ! [X0,X1] : (k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,X0))) ) | (spl10_1 | ~spl10_2 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 2.02/0.66    inference(unit_resulting_resolution,[],[f153,f143,f138,f174,f215,f194])).
% 2.02/0.66  fof(f96,plain,(
% 2.02/0.66    ( ! [X0,X1] : (k2_lattices(X0,sK2(X0,X1),X1) != X1 | v13_lattices(X0) | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f55])).
% 2.02/0.66  fof(f391,plain,(
% 2.02/0.66    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X0)))) ) | (spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 2.02/0.66    inference(unit_resulting_resolution,[],[f138,f143,f148,f153,f215,f258,f134])).
% 2.02/0.66  fof(f258,plain,(
% 2.02/0.66    ( ! [X0] : (r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X0)),k1_xboole_0)) ) | (spl10_1 | ~spl10_4 | ~spl10_5 | spl10_6)),
% 2.02/0.66    inference(unit_resulting_resolution,[],[f138,f153,f170,f215,f110])).
% 2.02/0.66  fof(f202,plain,(
% 2.02/0.66    spl10_10 | spl10_1 | ~spl10_2 | ~spl10_4),
% 2.02/0.66    inference(avatar_split_clause,[],[f173,f151,f141,f136,f199])).
% 2.02/0.66  fof(f173,plain,(
% 2.02/0.66    v9_lattices(sK0) | (spl10_1 | ~spl10_2 | ~spl10_4)),
% 2.02/0.66    inference(unit_resulting_resolution,[],[f153,f138,f143,f85])).
% 2.02/0.66  fof(f191,plain,(
% 2.02/0.66    spl10_9 | spl10_1 | ~spl10_2 | ~spl10_4),
% 2.02/0.66    inference(avatar_split_clause,[],[f172,f151,f141,f136,f188])).
% 2.02/0.66  fof(f172,plain,(
% 2.02/0.66    v8_lattices(sK0) | (spl10_1 | ~spl10_2 | ~spl10_4)),
% 2.02/0.66    inference(unit_resulting_resolution,[],[f153,f138,f143,f84])).
% 2.02/0.66  fof(f169,plain,(
% 2.02/0.66    ~spl10_6 | ~spl10_7),
% 2.02/0.66    inference(avatar_split_clause,[],[f132,f166,f162])).
% 2.02/0.66  fof(f132,plain,(
% 2.02/0.66    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0)),
% 2.02/0.66    inference(subsumption_resolution,[],[f131,f75])).
% 2.02/0.66  fof(f75,plain,(
% 2.02/0.66    ~v2_struct_0(sK0)),
% 2.02/0.66    inference(cnf_transformation,[],[f45])).
% 2.02/0.66  fof(f45,plain,(
% 2.02/0.66    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 2.02/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f44])).
% 2.02/0.66  fof(f44,plain,(
% 2.02/0.66    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 2.02/0.66    introduced(choice_axiom,[])).
% 2.02/0.66  fof(f21,plain,(
% 2.02/0.66    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.02/0.66    inference(flattening,[],[f20])).
% 2.02/0.66  fof(f20,plain,(
% 2.02/0.66    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.02/0.66    inference(ennf_transformation,[],[f15])).
% 2.02/0.66  fof(f15,negated_conjecture,(
% 2.02/0.66    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.02/0.66    inference(negated_conjecture,[],[f14])).
% 2.02/0.66  fof(f14,conjecture,(
% 2.02/0.66    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.02/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).
% 2.02/0.66  fof(f131,plain,(
% 2.02/0.66    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0) | v2_struct_0(sK0)),
% 2.02/0.66    inference(subsumption_resolution,[],[f130,f76])).
% 2.02/0.66  fof(f76,plain,(
% 2.02/0.66    v10_lattices(sK0)),
% 2.02/0.66    inference(cnf_transformation,[],[f45])).
% 2.02/0.66  fof(f130,plain,(
% 2.02/0.66    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 2.02/0.66    inference(subsumption_resolution,[],[f79,f78])).
% 2.02/0.66  fof(f78,plain,(
% 2.02/0.66    l3_lattices(sK0)),
% 2.02/0.66    inference(cnf_transformation,[],[f45])).
% 2.02/0.66  fof(f79,plain,(
% 2.02/0.66    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 2.02/0.66    inference(cnf_transformation,[],[f45])).
% 2.02/0.66  fof(f160,plain,(
% 2.02/0.66    spl10_5 | ~spl10_4),
% 2.02/0.66    inference(avatar_split_clause,[],[f155,f151,f157])).
% 2.02/0.66  fof(f155,plain,(
% 2.02/0.66    l1_lattices(sK0) | ~spl10_4),
% 2.02/0.66    inference(unit_resulting_resolution,[],[f153,f81])).
% 2.02/0.66  fof(f154,plain,(
% 2.02/0.66    spl10_4),
% 2.02/0.66    inference(avatar_split_clause,[],[f78,f151])).
% 2.02/0.66  fof(f149,plain,(
% 2.02/0.66    spl10_3),
% 2.02/0.66    inference(avatar_split_clause,[],[f77,f146])).
% 2.02/0.66  fof(f77,plain,(
% 2.02/0.66    v4_lattice3(sK0)),
% 2.02/0.66    inference(cnf_transformation,[],[f45])).
% 2.02/0.66  fof(f144,plain,(
% 2.02/0.66    spl10_2),
% 2.02/0.66    inference(avatar_split_clause,[],[f76,f141])).
% 2.02/0.66  fof(f139,plain,(
% 2.02/0.66    ~spl10_1),
% 2.02/0.66    inference(avatar_split_clause,[],[f75,f136])).
% 2.02/0.66  % SZS output end Proof for theBenchmark
% 2.02/0.66  % (14097)------------------------------
% 2.02/0.66  % (14097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.66  % (14097)Termination reason: Refutation
% 2.02/0.66  
% 2.02/0.66  % (14097)Memory used [KB]: 11897
% 2.02/0.66  % (14097)Time elapsed: 0.184 s
% 2.02/0.66  % (14097)------------------------------
% 2.02/0.66  % (14097)------------------------------
% 2.02/0.66  % (14083)Refutation not found, incomplete strategy% (14083)------------------------------
% 2.02/0.66  % (14083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.66  % (14083)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.66  
% 2.02/0.66  % (14083)Memory used [KB]: 6140
% 2.02/0.66  % (14083)Time elapsed: 0.224 s
% 2.02/0.66  % (14083)------------------------------
% 2.02/0.66  % (14083)------------------------------
% 2.02/0.66  % (14073)Success in time 0.28 s
%------------------------------------------------------------------------------
