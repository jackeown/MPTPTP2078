%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:48 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 656 expanded)
%              Number of leaves         :   29 ( 206 expanded)
%              Depth                    :   23
%              Number of atoms          :  964 (3042 expanded)
%              Number of equality atoms :  142 ( 354 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f192,f193,f194,f195,f1498,f2260])).

fof(f2260,plain,
    ( spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | spl14_5 ),
    inference(avatar_contradiction_clause,[],[f2259])).

fof(f2259,plain,
    ( $false
    | spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | spl14_5 ),
    inference(subsumption_resolution,[],[f2250,f104])).

fof(f104,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2250,plain,
    ( ~ r1_tarski(k1_xboole_0,sK9(sK0,k5_lattices(sK0),k1_xboole_0))
    | spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | spl14_5 ),
    inference(unit_resulting_resolution,[],[f2198,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f2198,plain,
    ( r2_hidden(sK9(sK0,k5_lattices(sK0),k1_xboole_0),k1_xboole_0)
    | spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | spl14_5 ),
    inference(unit_resulting_resolution,[],[f174,f186,f201,f2143,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK9(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK9(X0,X1,X2),X1)
                  & r2_hidden(sK9(X0,X1,X2),X2)
                  & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f81,f82])).

fof(f82,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK9(X0,X1,X2),X1)
        & r2_hidden(sK9(X0,X1,X2),X2)
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
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
    inference(rectify,[],[f80])).

fof(f80,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f2143,plain,
    ( ~ r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0)
    | spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | spl14_5 ),
    inference(unit_resulting_resolution,[],[f174,f178,f101,f186,f201,f200,f2110,f170])).

fof(f170,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,(
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
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f72,f73])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK6(X0,X1,X2))
        & r4_lattice3(X0,sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
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
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f2110,plain,
    ( ~ r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | spl14_5 ),
    inference(unit_resulting_resolution,[],[f191,f1641])).

fof(f1641,plain,
    ( ! [X0] :
        ( ~ r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | k5_lattices(sK0) = k15_lattice3(sK0,X0) )
    | spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4 ),
    inference(backward_demodulation,[],[f460,f1638])).

fof(f1638,plain,
    ( ! [X0] : k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0))
    | spl14_1
    | ~ spl14_3
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f174,f196,f200,f201,f182,f159])).

fof(f159,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f182,plain,
    ( v13_lattices(sK0)
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl14_3
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f196,plain,
    ( l1_lattices(sK0)
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f186,f105])).

fof(f105,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f460,plain,
    ( ! [X0] :
        ( ~ r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0)) )
    | spl14_1
    | ~ spl14_2
    | ~ spl14_4 ),
    inference(forward_demodulation,[],[f459,f214])).

fof(f214,plain,
    ( ! [X0] : k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0)) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
    | spl14_1
    | ~ spl14_2
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f174,f196,f198,f200,f201,f123])).

fof(f123,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f66,f68,f67])).

fof(f67,plain,(
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

fof(f68,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
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
    inference(rectify,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f198,plain,
    ( v6_lattices(sK0)
    | spl14_1
    | ~ spl14_2
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f174,f178,f186,f108])).

fof(f108,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
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

fof(f459,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) )
    | spl14_1
    | ~ spl14_2
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f458,f174])).

fof(f458,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | v2_struct_0(sK0) )
    | spl14_1
    | ~ spl14_2
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f457,f197])).

fof(f197,plain,
    ( l2_lattices(sK0)
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f186,f106])).

fof(f106,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f457,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl14_1
    | ~ spl14_2
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f456,f200])).

fof(f456,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl14_1
    | ~ spl14_2
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f443,f201])).

fof(f443,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl14_1
    | ~ spl14_2
    | ~ spl14_4 ),
    inference(superposition,[],[f218,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

fof(f218,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)))
    | spl14_1
    | ~ spl14_2
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f174,f186,f199,f200,f201,f132])).

fof(f132,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),sK8(X0)))
            & m1_subset_1(sK8(X0),u1_struct_0(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f76,f78,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),sK8(X0)))
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

fof(f199,plain,
    ( v9_lattices(sK0)
    | spl14_1
    | ~ spl14_2
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f174,f178,f186,f109])).

fof(f109,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f191,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl14_5 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl14_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f200,plain,
    ( ! [X0] : m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
    | spl14_1
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f174,f186,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f101,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f53])).

fof(f53,plain,
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f178,plain,
    ( v10_lattices(sK0)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl14_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f201,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl14_1
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f174,f196,f113])).

fof(f113,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f186,plain,
    ( l3_lattices(sK0)
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl14_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f174,plain,
    ( ~ v2_struct_0(sK0)
    | spl14_1 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl14_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f1498,plain,
    ( spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(avatar_contradiction_clause,[],[f1485])).

fof(f1485,plain,
    ( $false
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f104,f1408,f151])).

fof(f1408,plain,
    ( ! [X0] : r2_hidden(sK9(sK0,sK2(sK0,k15_lattice3(sK0,X0)),X0),X0)
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f174,f186,f203,f1308,f138])).

fof(f1308,plain,
    ( ! [X0] : ~ r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X0)),X0)
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f174,f178,f101,f186,f200,f203,f1230,f170])).

fof(f1230,plain,
    ( ! [X0] : ~ r1_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f603,f536])).

fof(f536,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1)))
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) )
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f535,f174])).

fof(f535,plain,
    ( ! [X0,X1] :
        ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1)))
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1)))
        | v2_struct_0(sK0) )
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f534,f197])).

fof(f534,plain,
    ( ! [X0,X1] :
        ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1)))
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1)))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f533,f200])).

fof(f533,plain,
    ( ! [X0,X1] :
        ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1)))
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1)))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f508,f203])).

fof(f508,plain,
    ( ! [X0,X1] :
        ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1)))
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1)))
        | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,X1)),u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(superposition,[],[f236,f111])).

fof(f236,plain,
    ( ! [X0,X1] : k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k1_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))))
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f174,f186,f199,f200,f203,f132])).

fof(f603,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f602,f174])).

fof(f602,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | v2_struct_0(sK0) )
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f601,f196])).

fof(f601,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f600,f200])).

fof(f600,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f575,f183])).

fof(f183,plain,
    ( ~ v13_lattices(sK0)
    | spl14_3 ),
    inference(avatar_component_clause,[],[f181])).

fof(f575,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | v13_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(duplicate_literal_removal,[],[f574])).

fof(f574,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | v13_lattices(sK0)
        | k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(superposition,[],[f122,f230])).

fof(f230,plain,
    ( ! [X0,X1] : k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X0)),k15_lattice3(sK0,X1)) = k2_lattices(sK0,k15_lattice3(sK0,X1),sK2(sK0,k15_lattice3(sK0,X0)))
    | spl14_1
    | ~ spl14_2
    | spl14_3
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f174,f196,f198,f200,f203,f123])).

fof(f122,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK2(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f61,f63,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
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

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f203,plain,
    ( ! [X0] : m1_subset_1(sK2(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))
    | spl14_1
    | spl14_3
    | ~ spl14_4 ),
    inference(unit_resulting_resolution,[],[f174,f196,f183,f200,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f195,plain,(
    ~ spl14_1 ),
    inference(avatar_split_clause,[],[f99,f173])).

fof(f99,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f194,plain,(
    spl14_2 ),
    inference(avatar_split_clause,[],[f100,f177])).

fof(f100,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f193,plain,(
    spl14_4 ),
    inference(avatar_split_clause,[],[f102,f185])).

fof(f102,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f192,plain,
    ( spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f103,f189,f185,f181,f177,f173])).

fof(f103,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:06:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (5060)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (5068)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (5068)Refutation not found, incomplete strategy% (5068)------------------------------
% 0.21/0.51  % (5068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5068)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5068)Memory used [KB]: 10618
% 0.21/0.51  % (5068)Time elapsed: 0.003 s
% 0.21/0.51  % (5068)------------------------------
% 0.21/0.51  % (5068)------------------------------
% 0.21/0.52  % (5061)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (5063)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (5061)Refutation not found, incomplete strategy% (5061)------------------------------
% 0.21/0.52  % (5061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5061)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5061)Memory used [KB]: 10746
% 0.21/0.52  % (5061)Time elapsed: 0.102 s
% 0.21/0.52  % (5061)------------------------------
% 0.21/0.52  % (5061)------------------------------
% 0.21/0.52  % (5084)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (5062)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (5064)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (5065)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (5059)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (5085)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (5086)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (5079)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (5077)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (5067)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (5082)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (5078)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (5072)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (5070)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (5083)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (5069)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (5076)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (5069)Refutation not found, incomplete strategy% (5069)------------------------------
% 0.21/0.55  % (5069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5069)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5069)Memory used [KB]: 10746
% 0.21/0.55  % (5069)Time elapsed: 0.137 s
% 0.21/0.55  % (5069)------------------------------
% 0.21/0.55  % (5069)------------------------------
% 0.21/0.55  % (5059)Refutation not found, incomplete strategy% (5059)------------------------------
% 0.21/0.55  % (5059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5059)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5059)Memory used [KB]: 1663
% 0.21/0.55  % (5059)Time elapsed: 0.003 s
% 0.21/0.55  % (5059)------------------------------
% 0.21/0.55  % (5059)------------------------------
% 0.21/0.55  % (5071)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (5070)Refutation not found, incomplete strategy% (5070)------------------------------
% 0.21/0.55  % (5070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5074)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (5070)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5070)Memory used [KB]: 10746
% 0.21/0.55  % (5070)Time elapsed: 0.130 s
% 0.21/0.55  % (5070)------------------------------
% 0.21/0.55  % (5070)------------------------------
% 0.21/0.55  % (5087)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (5075)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (5088)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (5081)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (5081)Refutation not found, incomplete strategy% (5081)------------------------------
% 0.21/0.56  % (5081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5081)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5081)Memory used [KB]: 10746
% 0.21/0.56  % (5081)Time elapsed: 0.148 s
% 0.21/0.56  % (5081)------------------------------
% 0.21/0.56  % (5081)------------------------------
% 0.21/0.56  % (5066)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (5080)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (5073)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (5076)Refutation not found, incomplete strategy% (5076)------------------------------
% 0.21/0.57  % (5076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (5076)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (5076)Memory used [KB]: 10618
% 0.21/0.57  % (5076)Time elapsed: 0.135 s
% 0.21/0.57  % (5076)------------------------------
% 0.21/0.57  % (5076)------------------------------
% 1.86/0.63  % (5147)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.03/0.66  % (5152)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.03/0.68  % (5174)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.03/0.69  % (5187)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.03/0.70  % (5176)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.03/0.70  % (5186)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.03/0.70  % (5198)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.72/0.72  % (5085)Refutation found. Thanks to Tanya!
% 2.72/0.72  % SZS status Theorem for theBenchmark
% 2.72/0.74  % SZS output start Proof for theBenchmark
% 2.72/0.74  fof(f2267,plain,(
% 2.72/0.74    $false),
% 2.72/0.74    inference(avatar_sat_refutation,[],[f192,f193,f194,f195,f1498,f2260])).
% 2.72/0.74  fof(f2260,plain,(
% 2.72/0.74    spl14_1 | ~spl14_2 | ~spl14_3 | ~spl14_4 | spl14_5),
% 2.72/0.74    inference(avatar_contradiction_clause,[],[f2259])).
% 2.72/0.74  fof(f2259,plain,(
% 2.72/0.74    $false | (spl14_1 | ~spl14_2 | ~spl14_3 | ~spl14_4 | spl14_5)),
% 2.72/0.74    inference(subsumption_resolution,[],[f2250,f104])).
% 2.72/0.74  fof(f104,plain,(
% 2.72/0.74    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f3])).
% 2.72/0.74  fof(f3,axiom,(
% 2.72/0.74    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.72/0.74  fof(f2250,plain,(
% 2.72/0.74    ~r1_tarski(k1_xboole_0,sK9(sK0,k5_lattices(sK0),k1_xboole_0)) | (spl14_1 | ~spl14_2 | ~spl14_3 | ~spl14_4 | spl14_5)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f2198,f151])).
% 2.72/0.74  fof(f151,plain,(
% 2.72/0.74    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f50])).
% 2.72/0.74  fof(f50,plain,(
% 2.72/0.74    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.72/0.74    inference(ennf_transformation,[],[f6])).
% 2.72/0.74  fof(f6,axiom,(
% 2.72/0.74    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.72/0.74  fof(f2198,plain,(
% 2.72/0.74    r2_hidden(sK9(sK0,k5_lattices(sK0),k1_xboole_0),k1_xboole_0) | (spl14_1 | ~spl14_2 | ~spl14_3 | ~spl14_4 | spl14_5)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f174,f186,f201,f2143,f138])).
% 2.72/0.74  fof(f138,plain,(
% 2.72/0.74    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK9(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f83])).
% 2.72/0.74  fof(f83,plain,(
% 2.72/0.74    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f81,f82])).
% 2.72/0.74  fof(f82,plain,(
% 2.72/0.74    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))))),
% 2.72/0.74    introduced(choice_axiom,[])).
% 2.72/0.74  fof(f81,plain,(
% 2.72/0.74    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(rectify,[],[f80])).
% 2.72/0.74  fof(f80,plain,(
% 2.72/0.74    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(nnf_transformation,[],[f46])).
% 2.72/0.74  fof(f46,plain,(
% 2.72/0.74    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(flattening,[],[f45])).
% 2.72/0.74  fof(f45,plain,(
% 2.72/0.74    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.72/0.74    inference(ennf_transformation,[],[f14])).
% 2.72/0.74  fof(f14,axiom,(
% 2.72/0.74    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 2.72/0.74  fof(f2143,plain,(
% 2.72/0.74    ~r4_lattice3(sK0,k5_lattices(sK0),k1_xboole_0) | (spl14_1 | ~spl14_2 | ~spl14_3 | ~spl14_4 | spl14_5)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f174,f178,f101,f186,f201,f200,f2110,f170])).
% 2.72/0.74  fof(f170,plain,(
% 2.72/0.74    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.72/0.74    inference(duplicate_literal_removal,[],[f160])).
% 2.72/0.74  fof(f160,plain,(
% 2.72/0.74    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.72/0.74    inference(equality_resolution,[],[f128])).
% 2.72/0.74  fof(f128,plain,(
% 2.72/0.74    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f74])).
% 2.72/0.74  fof(f74,plain,(
% 2.72/0.74    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK6(X0,X1,X2)) & r4_lattice3(X0,sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f72,f73])).
% 2.72/0.74  fof(f73,plain,(
% 2.72/0.74    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK6(X0,X1,X2)) & r4_lattice3(X0,sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 2.72/0.74    introduced(choice_axiom,[])).
% 2.72/0.74  fof(f72,plain,(
% 2.72/0.74    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(rectify,[],[f71])).
% 2.72/0.74  fof(f71,plain,(
% 2.72/0.74    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(flattening,[],[f70])).
% 2.72/0.74  fof(f70,plain,(
% 2.72/0.74    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(nnf_transformation,[],[f42])).
% 2.72/0.74  fof(f42,plain,(
% 2.72/0.74    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(flattening,[],[f41])).
% 2.72/0.74  fof(f41,plain,(
% 2.72/0.74    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.72/0.74    inference(ennf_transformation,[],[f15])).
% 2.72/0.74  fof(f15,axiom,(
% 2.72/0.74    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 2.72/0.74  fof(f2110,plain,(
% 2.72/0.74    ~r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl14_1 | ~spl14_2 | ~spl14_3 | ~spl14_4 | spl14_5)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f191,f1641])).
% 2.72/0.74  fof(f1641,plain,(
% 2.72/0.74    ( ! [X0] : (~r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | k5_lattices(sK0) = k15_lattice3(sK0,X0)) ) | (spl14_1 | ~spl14_2 | ~spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(backward_demodulation,[],[f460,f1638])).
% 2.72/0.74  fof(f1638,plain,(
% 2.72/0.74    ( ! [X0] : (k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0))) ) | (spl14_1 | ~spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f174,f196,f200,f201,f182,f159])).
% 2.72/0.74  fof(f159,plain,(
% 2.72/0.74    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.72/0.74    inference(equality_resolution,[],[f114])).
% 2.72/0.74  fof(f114,plain,(
% 2.72/0.74    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f59])).
% 2.72/0.74  fof(f59,plain,(
% 2.72/0.74    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f57,f58])).
% 2.72/0.74  fof(f58,plain,(
% 2.72/0.74    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 2.72/0.74    introduced(choice_axiom,[])).
% 2.72/0.74  fof(f57,plain,(
% 2.72/0.74    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(rectify,[],[f56])).
% 2.72/0.74  fof(f56,plain,(
% 2.72/0.74    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(nnf_transformation,[],[f36])).
% 2.72/0.74  fof(f36,plain,(
% 2.72/0.74    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(flattening,[],[f35])).
% 2.72/0.74  fof(f35,plain,(
% 2.72/0.74    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.72/0.74    inference(ennf_transformation,[],[f8])).
% 2.72/0.74  fof(f8,axiom,(
% 2.72/0.74    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 2.72/0.74  fof(f182,plain,(
% 2.72/0.74    v13_lattices(sK0) | ~spl14_3),
% 2.72/0.74    inference(avatar_component_clause,[],[f181])).
% 2.72/0.74  fof(f181,plain,(
% 2.72/0.74    spl14_3 <=> v13_lattices(sK0)),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).
% 2.72/0.74  fof(f196,plain,(
% 2.72/0.74    l1_lattices(sK0) | ~spl14_4),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f186,f105])).
% 2.72/0.74  fof(f105,plain,(
% 2.72/0.74    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f27])).
% 2.72/0.74  fof(f27,plain,(
% 2.72/0.74    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 2.72/0.74    inference(ennf_transformation,[],[f12])).
% 2.72/0.74  fof(f12,axiom,(
% 2.72/0.74    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 2.72/0.74  fof(f460,plain,(
% 2.72/0.74    ( ! [X0] : (~r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0))) ) | (spl14_1 | ~spl14_2 | ~spl14_4)),
% 2.72/0.74    inference(forward_demodulation,[],[f459,f214])).
% 2.72/0.74  fof(f214,plain,(
% 2.72/0.74    ( ! [X0] : (k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0)) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))) ) | (spl14_1 | ~spl14_2 | ~spl14_4)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f174,f196,f198,f200,f201,f123])).
% 2.72/0.74  fof(f123,plain,(
% 2.72/0.74    ( ! [X4,X0,X3] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f69])).
% 2.72/0.74  fof(f69,plain,(
% 2.72/0.74    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f66,f68,f67])).
% 2.72/0.74  fof(f67,plain,(
% 2.72/0.74    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 2.72/0.74    introduced(choice_axiom,[])).
% 2.72/0.74  fof(f68,plain,(
% 2.72/0.74    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 2.72/0.74    introduced(choice_axiom,[])).
% 2.72/0.74  fof(f66,plain,(
% 2.72/0.74    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(rectify,[],[f65])).
% 2.72/0.74  fof(f65,plain,(
% 2.72/0.74    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(nnf_transformation,[],[f40])).
% 2.72/0.74  fof(f40,plain,(
% 2.72/0.74    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(flattening,[],[f39])).
% 2.72/0.74  fof(f39,plain,(
% 2.72/0.74    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.72/0.74    inference(ennf_transformation,[],[f16])).
% 2.72/0.74  fof(f16,axiom,(
% 2.72/0.74    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).
% 2.72/0.74  fof(f198,plain,(
% 2.72/0.74    v6_lattices(sK0) | (spl14_1 | ~spl14_2 | ~spl14_4)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f174,f178,f186,f108])).
% 2.72/0.74  fof(f108,plain,(
% 2.72/0.74    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f29])).
% 2.72/0.74  fof(f29,plain,(
% 2.72/0.74    ! [X0] : ((v9_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.72/0.74    inference(flattening,[],[f28])).
% 2.72/0.74  fof(f28,plain,(
% 2.72/0.74    ! [X0] : (((v9_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.72/0.74    inference(ennf_transformation,[],[f24])).
% 2.72/0.74  fof(f24,plain,(
% 2.72/0.74    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 2.72/0.74    inference(pure_predicate_removal,[],[f23])).
% 2.72/0.74  fof(f23,plain,(
% 2.72/0.74    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.72/0.74    inference(pure_predicate_removal,[],[f22])).
% 2.72/0.74  fof(f22,plain,(
% 2.72/0.74    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.72/0.74    inference(pure_predicate_removal,[],[f21])).
% 2.72/0.74  fof(f21,plain,(
% 2.72/0.74    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.72/0.74    inference(pure_predicate_removal,[],[f7])).
% 2.72/0.74  fof(f7,axiom,(
% 2.72/0.74    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 2.72/0.74  fof(f459,plain,(
% 2.72/0.74    ( ! [X0] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | ~r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))) ) | (spl14_1 | ~spl14_2 | ~spl14_4)),
% 2.72/0.74    inference(subsumption_resolution,[],[f458,f174])).
% 2.72/0.74  fof(f458,plain,(
% 2.72/0.74    ( ! [X0] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | ~r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | v2_struct_0(sK0)) ) | (spl14_1 | ~spl14_2 | ~spl14_4)),
% 2.72/0.74    inference(subsumption_resolution,[],[f457,f197])).
% 2.72/0.74  fof(f197,plain,(
% 2.72/0.74    l2_lattices(sK0) | ~spl14_4),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f186,f106])).
% 2.72/0.74  fof(f106,plain,(
% 2.72/0.74    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f27])).
% 2.72/0.74  fof(f457,plain,(
% 2.72/0.74    ( ! [X0] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | ~r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | (spl14_1 | ~spl14_2 | ~spl14_4)),
% 2.72/0.74    inference(subsumption_resolution,[],[f456,f200])).
% 2.72/0.74  fof(f456,plain,(
% 2.72/0.74    ( ! [X0] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | ~r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | (spl14_1 | ~spl14_2 | ~spl14_4)),
% 2.72/0.74    inference(subsumption_resolution,[],[f443,f201])).
% 2.72/0.74  fof(f443,plain,(
% 2.72/0.74    ( ! [X0] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | ~r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | (spl14_1 | ~spl14_2 | ~spl14_4)),
% 2.72/0.74    inference(superposition,[],[f218,f111])).
% 2.72/0.74  fof(f111,plain,(
% 2.72/0.74    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f55])).
% 2.72/0.74  fof(f55,plain,(
% 2.72/0.74    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(nnf_transformation,[],[f32])).
% 2.72/0.74  fof(f32,plain,(
% 2.72/0.74    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(flattening,[],[f31])).
% 2.72/0.74  fof(f31,plain,(
% 2.72/0.74    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 2.72/0.74    inference(ennf_transformation,[],[f9])).
% 2.72/0.74  fof(f9,axiom,(
% 2.72/0.74    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 2.72/0.74  fof(f218,plain,(
% 2.72/0.74    ( ! [X0] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)))) ) | (spl14_1 | ~spl14_2 | ~spl14_4)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f174,f186,f199,f200,f201,f132])).
% 2.72/0.74  fof(f132,plain,(
% 2.72/0.74    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f79])).
% 2.72/0.74  fof(f79,plain,(
% 2.72/0.74    ! [X0] : (((v9_lattices(X0) | ((sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),sK8(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f76,f78,f77])).
% 2.72/0.74  fof(f77,plain,(
% 2.72/0.74    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 2.72/0.74    introduced(choice_axiom,[])).
% 2.72/0.74  fof(f78,plain,(
% 2.72/0.74    ! [X0] : (? [X2] : (sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),sK8(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 2.72/0.74    introduced(choice_axiom,[])).
% 2.72/0.74  fof(f76,plain,(
% 2.72/0.74    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(rectify,[],[f75])).
% 2.72/0.74  fof(f75,plain,(
% 2.72/0.74    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(nnf_transformation,[],[f44])).
% 2.72/0.74  fof(f44,plain,(
% 2.72/0.74    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(flattening,[],[f43])).
% 2.72/0.74  fof(f43,plain,(
% 2.72/0.74    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.72/0.74    inference(ennf_transformation,[],[f10])).
% 2.72/0.74  fof(f10,axiom,(
% 2.72/0.74    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).
% 2.72/0.74  fof(f199,plain,(
% 2.72/0.74    v9_lattices(sK0) | (spl14_1 | ~spl14_2 | ~spl14_4)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f174,f178,f186,f109])).
% 2.72/0.74  fof(f109,plain,(
% 2.72/0.74    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f29])).
% 2.72/0.74  fof(f191,plain,(
% 2.72/0.74    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl14_5),
% 2.72/0.74    inference(avatar_component_clause,[],[f189])).
% 2.72/0.74  fof(f189,plain,(
% 2.72/0.74    spl14_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).
% 2.72/0.74  fof(f200,plain,(
% 2.72/0.74    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl14_1 | ~spl14_4)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f174,f186,f140])).
% 2.72/0.74  fof(f140,plain,(
% 2.72/0.74    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f48])).
% 2.72/0.74  fof(f48,plain,(
% 2.72/0.74    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(flattening,[],[f47])).
% 2.72/0.74  fof(f47,plain,(
% 2.72/0.74    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.72/0.74    inference(ennf_transformation,[],[f17])).
% 2.72/0.74  fof(f17,axiom,(
% 2.72/0.74    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 2.72/0.74  fof(f101,plain,(
% 2.72/0.74    v4_lattice3(sK0)),
% 2.72/0.74    inference(cnf_transformation,[],[f54])).
% 2.72/0.74  fof(f54,plain,(
% 2.72/0.74    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 2.72/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f53])).
% 2.72/0.74  fof(f53,plain,(
% 2.72/0.74    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 2.72/0.74    introduced(choice_axiom,[])).
% 2.72/0.74  fof(f26,plain,(
% 2.72/0.74    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.72/0.74    inference(flattening,[],[f25])).
% 2.72/0.74  fof(f25,plain,(
% 2.72/0.74    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.72/0.74    inference(ennf_transformation,[],[f20])).
% 2.72/0.74  fof(f20,negated_conjecture,(
% 2.72/0.74    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.72/0.74    inference(negated_conjecture,[],[f19])).
% 2.72/0.74  fof(f19,conjecture,(
% 2.72/0.74    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).
% 2.72/0.74  fof(f178,plain,(
% 2.72/0.74    v10_lattices(sK0) | ~spl14_2),
% 2.72/0.74    inference(avatar_component_clause,[],[f177])).
% 2.72/0.74  fof(f177,plain,(
% 2.72/0.74    spl14_2 <=> v10_lattices(sK0)),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 2.72/0.74  fof(f201,plain,(
% 2.72/0.74    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl14_1 | ~spl14_4)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f174,f196,f113])).
% 2.72/0.74  fof(f113,plain,(
% 2.72/0.74    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f34])).
% 2.72/0.74  fof(f34,plain,(
% 2.72/0.74    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(flattening,[],[f33])).
% 2.72/0.74  fof(f33,plain,(
% 2.72/0.74    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.72/0.74    inference(ennf_transformation,[],[f11])).
% 2.72/0.74  fof(f11,axiom,(
% 2.72/0.74    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 2.72/0.74  fof(f186,plain,(
% 2.72/0.74    l3_lattices(sK0) | ~spl14_4),
% 2.72/0.74    inference(avatar_component_clause,[],[f185])).
% 2.72/0.74  fof(f185,plain,(
% 2.72/0.74    spl14_4 <=> l3_lattices(sK0)),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).
% 2.72/0.74  fof(f174,plain,(
% 2.72/0.74    ~v2_struct_0(sK0) | spl14_1),
% 2.72/0.74    inference(avatar_component_clause,[],[f173])).
% 2.72/0.74  fof(f173,plain,(
% 2.72/0.74    spl14_1 <=> v2_struct_0(sK0)),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 2.72/0.74  fof(f1498,plain,(
% 2.72/0.74    spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4),
% 2.72/0.74    inference(avatar_contradiction_clause,[],[f1485])).
% 2.72/0.74  fof(f1485,plain,(
% 2.72/0.74    $false | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f104,f1408,f151])).
% 2.72/0.74  fof(f1408,plain,(
% 2.72/0.74    ( ! [X0] : (r2_hidden(sK9(sK0,sK2(sK0,k15_lattice3(sK0,X0)),X0),X0)) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f174,f186,f203,f1308,f138])).
% 2.72/0.74  fof(f1308,plain,(
% 2.72/0.74    ( ! [X0] : (~r4_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X0)),X0)) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f174,f178,f101,f186,f200,f203,f1230,f170])).
% 2.72/0.74  fof(f1230,plain,(
% 2.72/0.74    ( ! [X0] : (~r1_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f603,f536])).
% 2.72/0.74  fof(f536,plain,(
% 2.72/0.74    ( ! [X0,X1] : (~r1_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1)))) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(subsumption_resolution,[],[f535,f174])).
% 2.72/0.74  fof(f535,plain,(
% 2.72/0.74    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) | ~r1_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) | v2_struct_0(sK0)) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(subsumption_resolution,[],[f534,f197])).
% 2.72/0.74  fof(f534,plain,(
% 2.72/0.74    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) | ~r1_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(subsumption_resolution,[],[f533,f200])).
% 2.72/0.74  fof(f533,plain,(
% 2.72/0.74    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) | ~r1_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(subsumption_resolution,[],[f508,f203])).
% 2.72/0.74  fof(f508,plain,(
% 2.72/0.74    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) | ~r1_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) | ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,X1)),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(superposition,[],[f236,f111])).
% 2.72/0.74  fof(f236,plain,(
% 2.72/0.74    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k1_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))))) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f174,f186,f199,f200,f203,f132])).
% 2.72/0.74  fof(f603,plain,(
% 2.72/0.74    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(subsumption_resolution,[],[f602,f174])).
% 2.72/0.74  fof(f602,plain,(
% 2.72/0.74    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | v2_struct_0(sK0)) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(subsumption_resolution,[],[f601,f196])).
% 2.72/0.74  fof(f601,plain,(
% 2.72/0.74    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(subsumption_resolution,[],[f600,f200])).
% 2.72/0.74  fof(f600,plain,(
% 2.72/0.74    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(subsumption_resolution,[],[f575,f183])).
% 2.72/0.74  fof(f183,plain,(
% 2.72/0.74    ~v13_lattices(sK0) | spl14_3),
% 2.72/0.74    inference(avatar_component_clause,[],[f181])).
% 2.72/0.74  fof(f575,plain,(
% 2.72/0.74    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | v13_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(duplicate_literal_removal,[],[f574])).
% 2.72/0.74  fof(f574,plain,(
% 2.72/0.74    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | v13_lattices(sK0) | k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(superposition,[],[f122,f230])).
% 2.72/0.74  fof(f230,plain,(
% 2.72/0.74    ( ! [X0,X1] : (k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X0)),k15_lattice3(sK0,X1)) = k2_lattices(sK0,k15_lattice3(sK0,X1),sK2(sK0,k15_lattice3(sK0,X0)))) ) | (spl14_1 | ~spl14_2 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f174,f196,f198,f200,f203,f123])).
% 2.72/0.74  fof(f122,plain,(
% 2.72/0.74    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f64])).
% 2.72/0.74  fof(f64,plain,(
% 2.72/0.74    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f61,f63,f62])).
% 2.72/0.74  fof(f62,plain,(
% 2.72/0.74    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 2.72/0.74    introduced(choice_axiom,[])).
% 2.72/0.74  fof(f63,plain,(
% 2.72/0.74    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 2.72/0.74    introduced(choice_axiom,[])).
% 2.72/0.74  fof(f61,plain,(
% 2.72/0.74    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(rectify,[],[f60])).
% 2.72/0.74  fof(f60,plain,(
% 2.72/0.74    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(nnf_transformation,[],[f38])).
% 2.72/0.74  fof(f38,plain,(
% 2.72/0.74    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.72/0.74    inference(flattening,[],[f37])).
% 2.72/0.74  fof(f37,plain,(
% 2.72/0.74    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.72/0.74    inference(ennf_transformation,[],[f13])).
% 2.72/0.74  fof(f13,axiom,(
% 2.72/0.74    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).
% 2.72/0.74  fof(f203,plain,(
% 2.72/0.74    ( ! [X0] : (m1_subset_1(sK2(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))) ) | (spl14_1 | spl14_3 | ~spl14_4)),
% 2.72/0.74    inference(unit_resulting_resolution,[],[f174,f196,f183,f200,f121])).
% 2.72/0.74  fof(f121,plain,(
% 2.72/0.74    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f64])).
% 2.72/0.74  fof(f195,plain,(
% 2.72/0.74    ~spl14_1),
% 2.72/0.74    inference(avatar_split_clause,[],[f99,f173])).
% 2.72/0.74  fof(f99,plain,(
% 2.72/0.74    ~v2_struct_0(sK0)),
% 2.72/0.74    inference(cnf_transformation,[],[f54])).
% 2.72/0.74  fof(f194,plain,(
% 2.72/0.74    spl14_2),
% 2.72/0.74    inference(avatar_split_clause,[],[f100,f177])).
% 2.72/0.74  fof(f100,plain,(
% 2.72/0.74    v10_lattices(sK0)),
% 2.72/0.74    inference(cnf_transformation,[],[f54])).
% 2.72/0.74  fof(f193,plain,(
% 2.72/0.74    spl14_4),
% 2.72/0.74    inference(avatar_split_clause,[],[f102,f185])).
% 2.72/0.74  fof(f102,plain,(
% 2.72/0.74    l3_lattices(sK0)),
% 2.72/0.74    inference(cnf_transformation,[],[f54])).
% 2.72/0.74  fof(f192,plain,(
% 2.72/0.74    spl14_1 | ~spl14_2 | ~spl14_3 | ~spl14_4 | ~spl14_5),
% 2.72/0.74    inference(avatar_split_clause,[],[f103,f189,f185,f181,f177,f173])).
% 2.72/0.74  fof(f103,plain,(
% 2.72/0.74    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 2.72/0.74    inference(cnf_transformation,[],[f54])).
% 2.72/0.74  % SZS output end Proof for theBenchmark
% 2.72/0.74  % (5085)------------------------------
% 2.72/0.74  % (5085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.72/0.74  % (5085)Termination reason: Refutation
% 2.72/0.74  
% 2.72/0.74  % (5085)Memory used [KB]: 12153
% 2.72/0.74  % (5085)Time elapsed: 0.315 s
% 2.72/0.74  % (5085)------------------------------
% 2.72/0.74  % (5085)------------------------------
% 2.72/0.75  % (5058)Success in time 0.375 s
%------------------------------------------------------------------------------
