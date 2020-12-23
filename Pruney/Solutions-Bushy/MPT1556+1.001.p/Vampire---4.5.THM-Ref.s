%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1556+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:05 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 215 expanded)
%              Number of leaves         :   18 (  68 expanded)
%              Depth                    :   19
%              Number of atoms          :  369 ( 707 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f75,f80,f91,f114,f171,f178,f193])).

fof(f193,plain,
    ( ~ spl5_1
    | ~ spl5_8
    | spl5_16 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_8
    | spl5_16 ),
    inference(subsumption_resolution,[],[f191,f64])).

fof(f64,plain,
    ( ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f47,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f47,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl5_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f191,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ spl5_1
    | ~ spl5_8
    | spl5_16 ),
    inference(resolution,[],[f169,f182])).

fof(f182,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(resolution,[],[f90,f66])).

fof(f66,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK4(sK0,X5,X4),X5)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r2_lattice3(sK0,X5,X4) )
    | ~ spl5_1 ),
    inference(resolution,[],[f47,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f90,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_8
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f169,plain,
    ( ~ r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl5_16
  <=> r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f178,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | spl5_5
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | spl5_5
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f176,f74])).

fof(f74,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_5
  <=> r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f176,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f175,f57])).

fof(f57,plain,
    ( r1_yellow_0(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl5_3
  <=> r1_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f175,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ spl5_1
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f172,f64])).

fof(f172,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK1)
    | r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ spl5_1
    | ~ spl5_16 ),
    inference(resolution,[],[f170,f94])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f92,f47])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X2,X3)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f170,plain,
    ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f168])).

fof(f171,plain,
    ( spl5_16
    | ~ spl5_1
    | ~ spl5_6
    | spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f166,f111,f85,f77,f45,f168])).

% (32212)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f77,plain,
    ( spl5_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f85,plain,
    ( spl5_7
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f111,plain,
    ( spl5_10
  <=> r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f166,plain,
    ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))
    | ~ spl5_1
    | ~ spl5_6
    | spl5_7
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f165,f64])).

fof(f165,plain,
    ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ spl5_1
    | ~ spl5_6
    | spl5_7
    | ~ spl5_10 ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,
    ( r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))
    | ~ spl5_1
    | ~ spl5_6
    | spl5_7
    | ~ spl5_10 ),
    inference(resolution,[],[f163,f66])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,k1_yellow_0(sK0,sK2)),sK1)
        | r2_lattice3(sK0,X0,k1_yellow_0(sK0,sK2)) )
    | ~ spl5_1
    | ~ spl5_6
    | spl5_7
    | ~ spl5_10 ),
    inference(resolution,[],[f156,f82])).

fof(f82,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,sK2)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl5_6 ),
    inference(resolution,[],[f79,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f79,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,X0,k1_yellow_0(sK0,sK2)),sK2)
        | r2_lattice3(sK0,X0,k1_yellow_0(sK0,sK2)) )
    | ~ spl5_1
    | spl5_7
    | ~ spl5_10 ),
    inference(resolution,[],[f153,f96])).

fof(f96,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,sK2) )
    | spl5_7 ),
    inference(resolution,[],[f87,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f87,plain,
    ( ~ v1_xboole_0(sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,k1_yellow_0(sK0,sK2)),sK2)
        | r2_lattice3(sK0,X0,k1_yellow_0(sK0,sK2)) )
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f152,f47])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,k1_yellow_0(sK0,sK2)),sK2)
        | r2_lattice3(sK0,X0,k1_yellow_0(sK0,sK2))
        | ~ l1_orders_2(sK0) )
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f151,f64])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,k1_yellow_0(sK0,sK2)),sK2)
        | r2_lattice3(sK0,X0,k1_yellow_0(sK0,sK2))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,k1_yellow_0(sK0,sK2)),sK2)
        | r2_lattice3(sK0,X0,k1_yellow_0(sK0,sK2))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_lattice3(sK0,X0,k1_yellow_0(sK0,sK2)) )
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(resolution,[],[f136,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,X0,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(sK0,X0,k1_yellow_0(sK0,sK2)),sK2)
        | r2_lattice3(sK0,X0,k1_yellow_0(sK0,sK2)) )
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f134,f64])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,k1_yellow_0(sK0,sK2)),sK2)
        | ~ m1_subset_1(sK4(sK0,X0,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,k1_yellow_0(sK0,sK2)) )
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(resolution,[],[f120,f67])).

fof(f67,plain,
    ( ! [X6,X7] :
        ( ~ r1_orders_2(sK0,sK4(sK0,X7,X6),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r2_lattice3(sK0,X7,X6) )
    | ~ spl5_1 ),
    inference(resolution,[],[f47,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f120,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,k1_yellow_0(sK0,sK2))
        | ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f117,f64])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | r1_orders_2(sK0,X0,k1_yellow_0(sK0,sK2))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) )
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(resolution,[],[f113,f65])).

fof(f65,plain,
    ( ! [X2,X3,X1] :
        ( ~ r2_lattice3(sK0,X3,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,X3)
        | r1_orders_2(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f47,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f113,plain,
    ( r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f114,plain,
    ( spl5_10
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f98,f60,f45,f111])).

fof(f60,plain,
    ( spl5_4
  <=> r1_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f98,plain,
    ( r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(resolution,[],[f95,f62])).

fof(f62,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f95,plain,
    ( ! [X2] :
        ( ~ r1_yellow_0(sK0,X2)
        | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2)) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f93,f47])).

fof(f93,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X2)
        | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f64,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f91,plain,
    ( ~ spl5_7
    | spl5_8
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f81,f77,f89,f85])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ v1_xboole_0(sK2) )
    | ~ spl5_6 ),
    inference(resolution,[],[f79,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f80,plain,
    ( spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f70,f50,f77])).

fof(f50,plain,
    ( spl5_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f70,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f52,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f75,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f25,f72])).

fof(f25,plain,(
    ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          & r1_yellow_0(X0,X2)
          & r1_yellow_0(X0,X1)
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          & r1_yellow_0(X0,X2)
          & r1_yellow_0(X0,X1)
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1,X2] :
            ( ( r1_yellow_0(X0,X2)
              & r1_yellow_0(X0,X1)
              & r1_tarski(X1,X2) )
           => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

fof(f63,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f24,f60])).

fof(f24,plain,(
    r1_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    r1_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f26,f45])).

fof(f26,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
