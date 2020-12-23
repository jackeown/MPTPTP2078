%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1575+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:25 EST 2020

% Result     : Theorem 11.40s
% Output     : Refutation 11.40s
% Verified   : 
% Statistics : Number of formulae       :  673 (1286 expanded)
%              Number of leaves         :  197 ( 518 expanded)
%              Depth                    :   17
%              Number of atoms          : 1925 (4459 expanded)
%              Number of equality atoms :  167 ( 512 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11164,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f6634,f6639,f6644,f6649,f6676,f6681,f6686,f6691,f6696,f6701,f6706,f6711,f6717,f6722,f6727,f6732,f6737,f6742,f6747,f6752,f6757,f6762,f6767,f6772,f6777,f6784,f6795,f6800,f6805,f6810,f6834,f6857,f6866,f6878,f6883,f6912,f6917,f6922,f6973,f6978,f6983,f6988,f6993,f6998,f7003,f7010,f7014,f7018,f7022,f7023,f7024,f7031,f7035,f7039,f7043,f7044,f7045,f7050,f7067,f7085,f7098,f7103,f7108,f7126,f7131,f7154,f7159,f7164,f7169,f7202,f7207,f7302,f7320,f7325,f7330,f7414,f7419,f7424,f7577,f7610,f7675,f7680,f7833,f7850,f7897,f7904,f7918,f7924,f7931,f7938,f7948,f7959,f8043,f8171,f8321,f8326,f9403,f9428,f9582,f9818,f9823,f9878,f9903,f9907,f9913,f9914,f9920,f9921,f9927,f9928,f10144,f10149,f10169,f10621,f10643,f10685,f10715,f10859,f10865,f11157,f11163])).

fof(f11163,plain,
    ( spl384_1
    | ~ spl384_2
    | spl384_3 ),
    inference(avatar_contradiction_clause,[],[f11162])).

fof(f11162,plain,
    ( $false
    | spl384_1
    | ~ spl384_2
    | spl384_3 ),
    inference(subsumption_resolution,[],[f11161,f6633])).

fof(f6633,plain,
    ( ~ v3_lattice3(sK0)
    | spl384_1 ),
    inference(avatar_component_clause,[],[f6631])).

fof(f6631,plain,
    ( spl384_1
  <=> v3_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_1])])).

fof(f11161,plain,
    ( v3_lattice3(sK0)
    | ~ spl384_2
    | spl384_3 ),
    inference(subsumption_resolution,[],[f11159,f6638])).

fof(f6638,plain,
    ( l1_orders_2(sK0)
    | ~ spl384_2 ),
    inference(avatar_component_clause,[],[f6636])).

fof(f6636,plain,
    ( spl384_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_2])])).

fof(f11159,plain,
    ( ~ l1_orders_2(sK0)
    | v3_lattice3(sK0)
    | ~ spl384_2
    | spl384_3 ),
    inference(resolution,[],[f8391,f9862])).

fof(f9862,plain,
    ( ! [X0] : r1_yellow_0(sK0,X0)
    | ~ spl384_2
    | spl384_3 ),
    inference(subsumption_resolution,[],[f9861,f6643])).

fof(f6643,plain,
    ( ~ v2_struct_0(sK0)
    | spl384_3 ),
    inference(avatar_component_clause,[],[f6641])).

fof(f6641,plain,
    ( spl384_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_3])])).

fof(f9861,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | r1_yellow_0(sK0,X0) )
    | ~ spl384_2 ),
    inference(subsumption_resolution,[],[f9853,f6638])).

fof(f9853,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | r1_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f9812,f4371])).

fof(f4371,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3093])).

fof(f3093,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r2_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
            | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3092])).

fof(f3092,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r2_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
            | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3032])).

fof(f3032,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,X1)
           => r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r1_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
           => r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_yellow_0)).

fof(f9812,plain,(
    ! [X5] : r1_yellow_0(sK0,k3_xboole_0(X5,u1_struct_0(sK0))) ),
    inference(resolution,[],[f9798,f9687])).

fof(f9687,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X9,X8),X8) ),
    inference(superposition,[],[f4674,f4673])).

fof(f4673,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f4674,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f9798,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | r1_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f4763,f4329])).

fof(f4329,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_yellow_0(sK0,X1) ) ),
    inference(cnf_transformation,[],[f3071])).

fof(f3071,plain,(
    ? [X0] :
      ( ~ v3_lattice3(X0)
      & ! [X1] :
          ( r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3070])).

fof(f3070,plain,(
    ? [X0] :
      ( ~ v3_lattice3(X0)
      & ! [X1] :
          ( r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3036])).

fof(f3036,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_yellow_0(X0,X1) )
         => v3_lattice3(X0) ) ) ),
    inference(negated_conjecture,[],[f3035])).

fof(f3035,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_yellow_0(X0,X1) )
       => v3_lattice3(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_yellow_0)).

fof(f4763,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f8391,plain,(
    ! [X7] :
      ( ~ r1_yellow_0(X7,sK3(X7))
      | ~ l1_orders_2(X7)
      | v3_lattice3(X7) ) ),
    inference(subsumption_resolution,[],[f8390,f4391])).

fof(f4391,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK11(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3097])).

fof(f3097,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3096])).

fof(f3096,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3042])).

fof(f3042,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X2,X5) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f2974])).

fof(f2974,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_yellow_0)).

fof(f8390,plain,(
    ! [X7] :
      ( ~ l1_orders_2(X7)
      | ~ r1_yellow_0(X7,sK3(X7))
      | v3_lattice3(X7)
      | ~ m1_subset_1(sK11(X7,sK3(X7)),u1_struct_0(X7)) ) ),
    inference(subsumption_resolution,[],[f8386,f4392])).

fof(f4392,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK11(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3097])).

fof(f8386,plain,(
    ! [X7] :
      ( ~ l1_orders_2(X7)
      | ~ r1_yellow_0(X7,sK3(X7))
      | ~ r2_lattice3(X7,sK3(X7),sK11(X7,sK3(X7)))
      | v3_lattice3(X7)
      | ~ m1_subset_1(sK11(X7,sK3(X7)),u1_struct_0(X7)) ) ),
    inference(duplicate_literal_removal,[],[f8385])).

fof(f8385,plain,(
    ! [X7] :
      ( ~ l1_orders_2(X7)
      | ~ r1_yellow_0(X7,sK3(X7))
      | ~ r2_lattice3(X7,sK3(X7),sK11(X7,sK3(X7)))
      | v3_lattice3(X7)
      | ~ m1_subset_1(sK11(X7,sK3(X7)),u1_struct_0(X7))
      | ~ r2_lattice3(X7,sK3(X7),sK11(X7,sK3(X7)))
      | ~ l1_orders_2(X7)
      | v3_lattice3(X7) ) ),
    inference(resolution,[],[f7079,f4349])).

fof(f4349,plain,(
    ! [X2,X0] :
      ( r2_lattice3(X0,sK3(X0),sK5(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK3(X0),X2)
      | ~ l1_orders_2(X0)
      | v3_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f3083])).

fof(f3083,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3082])).

fof(f3082,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2812])).

fof(f2812,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                 => r1_orders_2(X0,X2,X3) ) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_lattice3)).

fof(f7079,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(X0,X1,sK5(X0,sK11(X0,X1)))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,sK3(X0),sK11(X0,X1))
      | v3_lattice3(X0) ) ),
    inference(subsumption_resolution,[],[f7078,f4391])).

fof(f7078,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(X0,X1,sK5(X0,sK11(X0,X1)))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(sK11(X0,X1),u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK3(X0),sK11(X0,X1))
      | v3_lattice3(X0) ) ),
    inference(subsumption_resolution,[],[f7077,f4348])).

fof(f4348,plain,(
    ! [X2,X0] :
      ( m1_subset_1(sK5(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK3(X0),X2)
      | ~ l1_orders_2(X0)
      | v3_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f3083])).

fof(f7077,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5(X0,sK11(X0,X1)),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,sK5(X0,sK11(X0,X1)))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(sK11(X0,X1),u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK3(X0),sK11(X0,X1))
      | v3_lattice3(X0) ) ),
    inference(duplicate_literal_removal,[],[f7076])).

fof(f7076,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5(X0,sK11(X0,X1)),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,sK5(X0,sK11(X0,X1)))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(sK11(X0,X1),u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK3(X0),sK11(X0,X1))
      | ~ l1_orders_2(X0)
      | v3_lattice3(X0) ) ),
    inference(resolution,[],[f4390,f4350])).

fof(f4350,plain,(
    ! [X2,X0] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK3(X0),X2)
      | ~ l1_orders_2(X0)
      | v3_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f3083])).

fof(f4390,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,sK11(X0,X1),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X5)
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3097])).

fof(f11157,plain,
    ( ~ spl384_121
    | ~ spl384_5 ),
    inference(avatar_split_clause,[],[f11152,f6673,f11154])).

fof(f11154,plain,
    ( spl384_121
  <=> r1_tarski(sK300(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_121])])).

fof(f6673,plain,
    ( spl384_5
  <=> k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_5])])).

fof(f11152,plain,
    ( ~ r1_tarski(sK300(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | ~ spl384_5 ),
    inference(superposition,[],[f10161,f6675])).

fof(f6675,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)
    | ~ spl384_5 ),
    inference(avatar_component_clause,[],[f6673])).

fof(f10161,plain,(
    ! [X17] : ~ r1_tarski(sK300(k1_zfmisc_1(X17)),X17) ),
    inference(resolution,[],[f6463,f6180])).

fof(f6180,plain,(
    ! [X0] : ~ r2_hidden(sK300(X0),X0) ),
    inference(cnf_transformation,[],[f4244])).

fof(f4244,plain,(
    ! [X0] :
    ? [X1] :
      ( ~ r2_hidden(X1,X0)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f1109])).

fof(f1109,axiom,(
    ! [X0] :
      ~ ! [X1] :
          ( v3_ordinal1(X1)
         => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_ordinal1)).

fof(f6463,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f4765])).

fof(f4765,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f10865,plain,
    ( ~ spl384_120
    | ~ spl384_2
    | spl384_3
    | ~ spl384_6
    | spl384_81
    | spl384_86 ),
    inference(avatar_split_clause,[],[f10860,f7894,f7827,f6678,f6641,f6636,f10862])).

fof(f10862,plain,
    ( spl384_120
  <=> r2_yellow_0(sK0,sK163(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_120])])).

fof(f6678,plain,
    ( spl384_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_6])])).

fof(f7827,plain,
    ( spl384_81
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_81])])).

fof(f7894,plain,
    ( spl384_86
  <=> r2_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_86])])).

fof(f10860,plain,
    ( ~ r2_yellow_0(sK0,sK163(u1_struct_0(sK0)))
    | ~ spl384_2
    | spl384_3
    | ~ spl384_6
    | spl384_81
    | spl384_86 ),
    inference(subsumption_resolution,[],[f10854,f7828])).

fof(f7828,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | spl384_81 ),
    inference(avatar_component_clause,[],[f7827])).

fof(f10854,plain,
    ( ~ r2_yellow_0(sK0,sK163(u1_struct_0(sK0)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl384_2
    | spl384_3
    | ~ spl384_6
    | spl384_86 ),
    inference(resolution,[],[f10846,f5331])).

fof(f5331,plain,(
    ! [X0] :
      ( r1_xboole_0(sK163(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3624])).

fof(f3624,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1336])).

fof(f1336,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f10846,plain,
    ( ! [X60] :
        ( ~ r1_xboole_0(X60,u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,X60) )
    | ~ spl384_2
    | spl384_3
    | ~ spl384_6
    | spl384_86 ),
    inference(subsumption_resolution,[],[f10835,f6680])).

fof(f6680,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl384_6 ),
    inference(avatar_component_clause,[],[f6678])).

fof(f10835,plain,
    ( ! [X60] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r2_yellow_0(sK0,X60)
        | ~ r1_xboole_0(X60,u1_struct_0(sK0)) )
    | ~ spl384_2
    | spl384_3
    | spl384_86 ),
    inference(superposition,[],[f8035,f5308])).

fof(f5308,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f8035,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(k3_xboole_0(X1,u1_struct_0(sK0)))
        | ~ r2_yellow_0(sK0,X1) )
    | ~ spl384_2
    | spl384_3
    | spl384_86 ),
    inference(subsumption_resolution,[],[f8034,f6643])).

fof(f8034,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(k3_xboole_0(X1,u1_struct_0(sK0)))
        | ~ r2_yellow_0(sK0,X1)
        | v2_struct_0(sK0) )
    | ~ spl384_2
    | spl384_86 ),
    inference(subsumption_resolution,[],[f8032,f6638])).

fof(f8032,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(k3_xboole_0(X1,u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X1)
        | v2_struct_0(sK0) )
    | spl384_86 ),
    inference(resolution,[],[f7971,f4370])).

fof(f4370,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3093])).

fof(f7971,plain,
    ( ! [X0] :
        ( ~ r2_yellow_0(sK0,X0)
        | ~ v1_xboole_0(X0) )
    | spl384_86 ),
    inference(superposition,[],[f7896,f4827])).

fof(f4827,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3340])).

fof(f3340,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f7896,plain,
    ( ~ r2_yellow_0(sK0,k1_xboole_0)
    | spl384_86 ),
    inference(avatar_component_clause,[],[f7894])).

fof(f10859,plain,
    ( ~ spl384_119
    | ~ spl384_2
    | spl384_3
    | ~ spl384_6
    | spl384_86 ),
    inference(avatar_split_clause,[],[f10853,f7894,f6678,f6641,f6636,f10856])).

fof(f10856,plain,
    ( spl384_119
  <=> r2_yellow_0(sK0,k1_tarski(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_119])])).

fof(f10853,plain,
    ( ~ r2_yellow_0(sK0,k1_tarski(u1_struct_0(sK0)))
    | ~ spl384_2
    | spl384_3
    | ~ spl384_6
    | spl384_86 ),
    inference(resolution,[],[f10846,f10415])).

fof(f10415,plain,(
    ! [X3] : r1_xboole_0(k1_tarski(X3),X3) ),
    inference(resolution,[],[f10381,f5309])).

fof(f5309,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f3607])).

fof(f3607,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f10381,plain,(
    ! [X0] : r1_xboole_0(X0,k1_tarski(X0)) ),
    inference(subsumption_resolution,[],[f10379,f8428])).

fof(f8428,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f7491,f4633])).

fof(f4633,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f7491,plain,(
    ! [X2,X1] : k1_xboole_0 != k2_tarski(X1,X2) ),
    inference(subsumption_resolution,[],[f7489,f7269])).

fof(f7269,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f4565,f5343])).

fof(f5343,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f4565,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3200])).

fof(f3200,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f413])).

fof(f413,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f7489,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k2_tarski(X1,X2)
      | r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f4610,f4679])).

fof(f4679,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f4610,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) != k3_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3212])).

fof(f3212,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      | k2_tarski(X0,X1) != k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f419])).

fof(f419,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

fof(f10379,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f5331,f10192])).

fof(f10192,plain,(
    ! [X18] : sK163(k1_tarski(X18)) = X18 ),
    inference(subsumption_resolution,[],[f10183,f8428])).

fof(f10183,plain,(
    ! [X18] :
      ( sK163(k1_tarski(X18)) = X18
      | k1_xboole_0 = k1_tarski(X18) ) ),
    inference(resolution,[],[f6470,f5330])).

fof(f5330,plain,(
    ! [X0] :
      ( r2_hidden(sK163(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3624])).

fof(f6470,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f4796])).

fof(f4796,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f10715,plain,
    ( spl384_117
    | spl384_118 ),
    inference(avatar_split_clause,[],[f10700,f10713,f10709])).

fof(f10709,plain,
    ( spl384_117
  <=> v1_relat_1(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_117])])).

fof(f10713,plain,
    ( spl384_118
  <=> ! [X9] : ~ v1_relat_1(k1_zfmisc_1(X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_118])])).

fof(f10700,plain,(
    ! [X9] :
      ( ~ v1_relat_1(k1_zfmisc_1(X9))
      | v1_relat_1(k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f5197,f4805])).

fof(f4805,plain,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(cnf_transformation,[],[f631])).

fof(f631,axiom,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

fof(f5197,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f3544])).

fof(f3544,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f10685,plain,
    ( ~ spl384_116
    | ~ spl384_5 ),
    inference(avatar_split_clause,[],[f10680,f6673,f10682])).

fof(f10682,plain,
    ( spl384_116
  <=> r1_tarski(k1_zfmisc_1(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_116])])).

fof(f10680,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | ~ spl384_5 ),
    inference(superposition,[],[f10160,f6675])).

fof(f10160,plain,(
    ! [X16] : ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(X16)),X16) ),
    inference(resolution,[],[f6463,f9977])).

fof(f9977,plain,(
    ! [X0] : ~ r2_hidden(k1_zfmisc_1(X0),X0) ),
    inference(resolution,[],[f9850,f4755])).

fof(f4755,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3302])).

fof(f3302,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f9850,plain,(
    ! [X11] : r2_hidden(X11,k1_zfmisc_1(X11)) ),
    inference(resolution,[],[f4786,f4806])).

fof(f4806,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f434])).

fof(f434,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f4786,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f395])).

fof(f395,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f10643,plain,
    ( spl384_115
    | ~ spl384_26
    | ~ spl384_62 ),
    inference(avatar_split_clause,[],[f10638,f7123,f6781,f10640])).

fof(f10640,plain,
    ( spl384_115
  <=> k1_xboole_0 = k2_wellord1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_115])])).

fof(f6781,plain,
    ( spl384_26
  <=> k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_26])])).

fof(f7123,plain,
    ( spl384_62
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_62])])).

fof(f10638,plain,
    ( k1_xboole_0 = k2_wellord1(k1_xboole_0,k1_xboole_0)
    | ~ spl384_26
    | ~ spl384_62 ),
    inference(subsumption_resolution,[],[f10629,f7125])).

fof(f7125,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl384_62 ),
    inference(avatar_component_clause,[],[f7123])).

fof(f10629,plain,
    ( k1_xboole_0 = k2_wellord1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl384_26 ),
    inference(superposition,[],[f4986,f6783])).

fof(f6783,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ spl384_26 ),
    inference(avatar_component_clause,[],[f6781])).

fof(f4986,plain,(
    ! [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3452])).

fof(f3452,plain,(
    ! [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1175])).

fof(f1175,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

fof(f10621,plain,
    ( ~ spl384_114
    | ~ spl384_5 ),
    inference(avatar_split_clause,[],[f10616,f6673,f10618])).

fof(f10618,plain,
    ( spl384_114
  <=> r1_tarski(k1_tarski(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_114])])).

fof(f10616,plain,
    ( ~ r1_tarski(k1_tarski(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | ~ spl384_5 ),
    inference(superposition,[],[f10159,f6675])).

fof(f10159,plain,(
    ! [X15] : ~ r1_tarski(k1_tarski(k1_zfmisc_1(X15)),X15) ),
    inference(resolution,[],[f6463,f9404])).

fof(f9404,plain,(
    ! [X0] : ~ r2_hidden(k1_tarski(X0),X0) ),
    inference(resolution,[],[f4755,f6472])).

fof(f6472,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f6471])).

fof(f6471,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f4795])).

fof(f4795,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f175])).

fof(f10169,plain,
    ( ~ spl384_113
    | ~ spl384_5 ),
    inference(avatar_split_clause,[],[f10164,f6673,f10166])).

fof(f10166,plain,
    ( spl384_113
  <=> r1_tarski(k1_tarski(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_113])])).

fof(f10164,plain,
    ( ~ r1_tarski(k1_tarski(k1_xboole_0),k1_xboole_0)
    | ~ spl384_5 ),
    inference(superposition,[],[f10152,f6675])).

fof(f10152,plain,(
    ! [X2] : ~ r1_tarski(k1_zfmisc_1(X2),X2) ),
    inference(resolution,[],[f6463,f9411])).

fof(f9411,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(resolution,[],[f4762,f6464])).

fof(f6464,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f4773])).

fof(f4773,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f4762,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3312])).

fof(f3312,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1125])).

fof(f1125,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f10149,plain,
    ( spl384_112
    | ~ spl384_5 ),
    inference(avatar_split_clause,[],[f10138,f6673,f10146])).

fof(f10146,plain,
    ( spl384_112
  <=> r1_tarski(sK15(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_112])])).

fof(f10138,plain,
    ( r1_tarski(sK15(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | ~ spl384_5 ),
    inference(superposition,[],[f9829,f6675])).

fof(f9829,plain,(
    ! [X8] : r1_tarski(sK15(k1_zfmisc_1(X8)),X8) ),
    inference(resolution,[],[f4764,f4395])).

fof(f4395,plain,(
    ! [X0] : m1_subset_1(sK15(X0),X0) ),
    inference(cnf_transformation,[],[f474])).

fof(f474,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f4764,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f609])).

fof(f10144,plain,
    ( spl384_111
    | ~ spl384_5 ),
    inference(avatar_split_clause,[],[f10139,f6673,f10141])).

fof(f10141,plain,
    ( spl384_111
  <=> k1_xboole_0 = sK15(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_111])])).

fof(f10139,plain,
    ( k1_xboole_0 = sK15(k1_tarski(k1_xboole_0))
    | ~ spl384_5 ),
    inference(forward_demodulation,[],[f10136,f6675])).

fof(f10136,plain,(
    k1_xboole_0 = sK15(k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f9829,f4826])).

fof(f4826,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f3339])).

fof(f3339,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f9928,plain,
    ( spl384_107
    | ~ spl384_110
    | spl384_91 ),
    inference(avatar_split_clause,[],[f9894,f7928,f9924,f9905])).

fof(f9905,plain,
    ( spl384_107
  <=> ! [X9] : ~ v1_xboole_0(X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_107])])).

fof(f9924,plain,
    ( spl384_110
  <=> v1_xboole_0(sK22(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_110])])).

fof(f7928,plain,
    ( spl384_91
  <=> m1_subset_1(sK22(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_91])])).

fof(f9894,plain,
    ( ! [X12] :
        ( ~ v1_xboole_0(sK22(sK0))
        | ~ v1_xboole_0(X12) )
    | spl384_91 ),
    inference(duplicate_literal_removal,[],[f9893])).

fof(f9893,plain,
    ( ! [X12] :
        ( ~ v1_xboole_0(sK22(sK0))
        | ~ v1_xboole_0(X12)
        | ~ v1_xboole_0(X12) )
    | spl384_91 ),
    inference(resolution,[],[f4918,f8019])).

fof(f8019,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK22(sK0),X0)
        | ~ v1_xboole_0(X0) )
    | spl384_91 ),
    inference(superposition,[],[f7929,f4827])).

fof(f7929,plain,
    ( ~ m1_subset_1(sK22(sK0),k1_xboole_0)
    | spl384_91 ),
    inference(avatar_component_clause,[],[f7928])).

fof(f4918,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3403])).

fof(f3403,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f9927,plain,
    ( ~ spl384_110
    | ~ spl384_6
    | spl384_91 ),
    inference(avatar_split_clause,[],[f9922,f7928,f6678,f9924])).

fof(f9922,plain,
    ( ~ v1_xboole_0(sK22(sK0))
    | ~ spl384_6
    | spl384_91 ),
    inference(subsumption_resolution,[],[f9892,f6680])).

fof(f9892,plain,
    ( ~ v1_xboole_0(sK22(sK0))
    | ~ v1_xboole_0(k1_xboole_0)
    | spl384_91 ),
    inference(resolution,[],[f4918,f7929])).

fof(f9921,plain,
    ( spl384_107
    | ~ spl384_109
    | spl384_92 ),
    inference(avatar_split_clause,[],[f9895,f7935,f9917,f9905])).

fof(f9917,plain,
    ( spl384_109
  <=> v1_xboole_0(sK21(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_109])])).

fof(f7935,plain,
    ( spl384_92
  <=> m1_subset_1(sK21(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_92])])).

fof(f9895,plain,
    ( ! [X11] :
        ( ~ v1_xboole_0(sK21(sK0))
        | ~ v1_xboole_0(X11) )
    | spl384_92 ),
    inference(duplicate_literal_removal,[],[f9891])).

fof(f9891,plain,
    ( ! [X11] :
        ( ~ v1_xboole_0(sK21(sK0))
        | ~ v1_xboole_0(X11)
        | ~ v1_xboole_0(X11) )
    | spl384_92 ),
    inference(resolution,[],[f4918,f8020])).

fof(f8020,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK21(sK0),X0)
        | ~ v1_xboole_0(X0) )
    | spl384_92 ),
    inference(superposition,[],[f7936,f4827])).

fof(f7936,plain,
    ( ~ m1_subset_1(sK21(sK0),k1_xboole_0)
    | spl384_92 ),
    inference(avatar_component_clause,[],[f7935])).

fof(f9920,plain,
    ( ~ spl384_109
    | ~ spl384_6
    | spl384_92 ),
    inference(avatar_split_clause,[],[f9915,f7935,f6678,f9917])).

fof(f9915,plain,
    ( ~ v1_xboole_0(sK21(sK0))
    | ~ spl384_6
    | spl384_92 ),
    inference(subsumption_resolution,[],[f9890,f6680])).

fof(f9890,plain,
    ( ~ v1_xboole_0(sK21(sK0))
    | ~ v1_xboole_0(k1_xboole_0)
    | spl384_92 ),
    inference(resolution,[],[f4918,f7936])).

fof(f9914,plain,
    ( spl384_107
    | ~ spl384_108
    | spl384_89 ),
    inference(avatar_split_clause,[],[f9896,f7915,f9910,f9905])).

fof(f9910,plain,
    ( spl384_108
  <=> v1_xboole_0(sK18(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_108])])).

fof(f7915,plain,
    ( spl384_89
  <=> m1_subset_1(sK18(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_89])])).

fof(f9896,plain,
    ( ! [X10] :
        ( ~ v1_xboole_0(sK18(sK0))
        | ~ v1_xboole_0(X10) )
    | spl384_89 ),
    inference(duplicate_literal_removal,[],[f9889])).

fof(f9889,plain,
    ( ! [X10] :
        ( ~ v1_xboole_0(sK18(sK0))
        | ~ v1_xboole_0(X10)
        | ~ v1_xboole_0(X10) )
    | spl384_89 ),
    inference(resolution,[],[f4918,f8011])).

fof(f8011,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK18(sK0),X0)
        | ~ v1_xboole_0(X0) )
    | spl384_89 ),
    inference(superposition,[],[f7916,f4827])).

fof(f7916,plain,
    ( ~ m1_subset_1(sK18(sK0),k1_xboole_0)
    | spl384_89 ),
    inference(avatar_component_clause,[],[f7915])).

fof(f9913,plain,
    ( ~ spl384_108
    | ~ spl384_6
    | spl384_89 ),
    inference(avatar_split_clause,[],[f9908,f7915,f6678,f9910])).

fof(f9908,plain,
    ( ~ v1_xboole_0(sK18(sK0))
    | ~ spl384_6
    | spl384_89 ),
    inference(subsumption_resolution,[],[f9888,f6680])).

fof(f9888,plain,
    ( ~ v1_xboole_0(sK18(sK0))
    | ~ v1_xboole_0(k1_xboole_0)
    | spl384_89 ),
    inference(resolution,[],[f4918,f7916])).

fof(f9907,plain,
    ( spl384_107
    | ~ spl384_106
    | spl384_90 ),
    inference(avatar_split_clause,[],[f9897,f7921,f9900,f9905])).

fof(f9900,plain,
    ( spl384_106
  <=> v1_xboole_0(sK17(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_106])])).

fof(f7921,plain,
    ( spl384_90
  <=> m1_subset_1(sK17(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_90])])).

fof(f9897,plain,
    ( ! [X9] :
        ( ~ v1_xboole_0(sK17(sK0))
        | ~ v1_xboole_0(X9) )
    | spl384_90 ),
    inference(duplicate_literal_removal,[],[f9887])).

fof(f9887,plain,
    ( ! [X9] :
        ( ~ v1_xboole_0(sK17(sK0))
        | ~ v1_xboole_0(X9)
        | ~ v1_xboole_0(X9) )
    | spl384_90 ),
    inference(resolution,[],[f4918,f8018])).

fof(f8018,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK17(sK0),X0)
        | ~ v1_xboole_0(X0) )
    | spl384_90 ),
    inference(superposition,[],[f7922,f4827])).

fof(f7922,plain,
    ( ~ m1_subset_1(sK17(sK0),k1_xboole_0)
    | spl384_90 ),
    inference(avatar_component_clause,[],[f7921])).

fof(f9903,plain,
    ( ~ spl384_106
    | ~ spl384_6
    | spl384_90 ),
    inference(avatar_split_clause,[],[f9898,f7921,f6678,f9900])).

fof(f9898,plain,
    ( ~ v1_xboole_0(sK17(sK0))
    | ~ spl384_6
    | spl384_90 ),
    inference(subsumption_resolution,[],[f9886,f6680])).

fof(f9886,plain,
    ( ~ v1_xboole_0(sK17(sK0))
    | ~ v1_xboole_0(k1_xboole_0)
    | spl384_90 ),
    inference(resolution,[],[f4918,f7922])).

fof(f9878,plain,(
    spl384_105 ),
    inference(avatar_split_clause,[],[f9872,f9875])).

fof(f9875,plain,
    ( spl384_105
  <=> k1_xboole_0 = sK76(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_105])])).

fof(f9872,plain,(
    k1_xboole_0 = sK76(k1_xboole_0) ),
    inference(resolution,[],[f9830,f4826])).

fof(f9830,plain,(
    ! [X9] : r1_tarski(sK76(X9),X9) ),
    inference(resolution,[],[f4764,f4922])).

fof(f4922,plain,(
    ! [X0] : m1_subset_1(sK76(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f490])).

fof(f490,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f9823,plain,(
    spl384_104 ),
    inference(avatar_split_clause,[],[f9808,f9820])).

fof(f9820,plain,
    ( spl384_104
  <=> r1_yellow_0(sK0,k2_relat_1(sK144(u1_struct_0(sK0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_104])])).

fof(f9808,plain,(
    r1_yellow_0(sK0,k2_relat_1(sK144(u1_struct_0(sK0),k1_xboole_0))) ),
    inference(resolution,[],[f9798,f6498])).

fof(f6498,plain,(
    ! [X0] : r1_tarski(k2_relat_1(sK144(X0,k1_xboole_0)),X0) ),
    inference(equality_resolution,[],[f5138])).

fof(f5138,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | r1_tarski(k2_relat_1(sK144(X0,X1)),X0) ) ),
    inference(cnf_transformation,[],[f3497])).

fof(f3497,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f3496])).

fof(f3496,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f1001])).

fof(f1001,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f9818,plain,(
    spl384_103 ),
    inference(avatar_split_clause,[],[f9804,f9815])).

fof(f9815,plain,
    ( spl384_103
  <=> r1_yellow_0(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_103])])).

fof(f9804,plain,(
    r1_yellow_0(sK0,u1_struct_0(sK0)) ),
    inference(resolution,[],[f9798,f6464])).

fof(f9582,plain,(
    spl384_102 ),
    inference(avatar_split_clause,[],[f9576,f9579])).

fof(f9579,plain,
    ( spl384_102
  <=> k1_xboole_0 = k2_relat_1(sK144(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_102])])).

fof(f9576,plain,(
    k1_xboole_0 = k2_relat_1(sK144(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f6498,f4826])).

fof(f9428,plain,
    ( spl384_101
    | ~ spl384_5 ),
    inference(avatar_split_clause,[],[f9423,f6673,f9425])).

fof(f9425,plain,
    ( spl384_101
  <=> m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_101])])).

fof(f9423,plain,
    ( m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_tarski(k1_xboole_0)))
    | ~ spl384_5 ),
    inference(superposition,[],[f4805,f6675])).

fof(f9403,plain,
    ( ~ spl384_100
    | spl384_95 ),
    inference(avatar_split_clause,[],[f9394,f7956,f9400])).

fof(f9400,plain,
    ( spl384_100
  <=> v1_xboole_0(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_100])])).

fof(f7956,plain,
    ( spl384_95
  <=> m1_subset_1(u1_orders_2(sK0),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_95])])).

fof(f9394,plain,
    ( ~ v1_xboole_0(u1_orders_2(sK0))
    | spl384_95 ),
    inference(resolution,[],[f9387,f8021])).

fof(f8021,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_orders_2(sK0),k1_tarski(X0))
        | ~ v1_xboole_0(X0) )
    | spl384_95 ),
    inference(superposition,[],[f7957,f4827])).

fof(f7957,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_tarski(k1_xboole_0))
    | spl384_95 ),
    inference(avatar_component_clause,[],[f7956])).

fof(f9387,plain,(
    ! [X0] : m1_subset_1(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f4754,f6472])).

fof(f4754,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3301])).

fof(f3301,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f8326,plain,
    ( spl384_99
    | ~ spl384_5 ),
    inference(avatar_split_clause,[],[f8315,f6673,f8323])).

fof(f8323,plain,
    ( spl384_99
  <=> m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_99])])).

fof(f8315,plain,
    ( m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl384_5 ),
    inference(superposition,[],[f4829,f6675])).

fof(f4829,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f8321,plain,
    ( spl384_98
    | ~ spl384_5 ),
    inference(avatar_split_clause,[],[f8312,f6673,f8318])).

fof(f8318,plain,
    ( spl384_98
  <=> m1_subset_1(sK76(k1_xboole_0),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_98])])).

fof(f8312,plain,
    ( m1_subset_1(sK76(k1_xboole_0),k1_tarski(k1_xboole_0))
    | ~ spl384_5 ),
    inference(superposition,[],[f4922,f6675])).

fof(f8171,plain,(
    spl384_97 ),
    inference(avatar_split_clause,[],[f8166,f8168])).

fof(f8168,plain,
    ( spl384_97
  <=> r1_yellow_0(sK0,sK76(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_97])])).

fof(f8166,plain,(
    r1_yellow_0(sK0,sK76(u1_struct_0(sK0))) ),
    inference(resolution,[],[f4922,f4329])).

fof(f8043,plain,
    ( ~ spl384_96
    | ~ spl384_2
    | spl384_88
    | spl384_89 ),
    inference(avatar_split_clause,[],[f8038,f7915,f7911,f6636,f8040])).

fof(f8040,plain,
    ( spl384_96
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_96])])).

fof(f7911,plain,
    ( spl384_88
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_88])])).

fof(f8038,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl384_2
    | spl384_88
    | spl384_89 ),
    inference(subsumption_resolution,[],[f8037,f7912])).

fof(f7912,plain,
    ( ~ v2_lattice3(sK0)
    | spl384_88 ),
    inference(avatar_component_clause,[],[f7911])).

fof(f8037,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_lattice3(sK0)
    | ~ spl384_2
    | spl384_89 ),
    inference(subsumption_resolution,[],[f8036,f6638])).

fof(f8036,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_lattice3(sK0)
    | spl384_89 ),
    inference(resolution,[],[f8011,f4405])).

fof(f4405,plain,(
    ! [X0] :
      ( m1_subset_1(sK18(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f3101])).

fof(f3101,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3100])).

fof(f3100,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2811])).

fof(f2811,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r1_orders_2(X0,X4,X2)
                            & r1_orders_2(X0,X4,X1) )
                         => r1_orders_2(X0,X4,X3) ) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattice3)).

fof(f7959,plain,
    ( spl384_95
    | ~ spl384_2
    | ~ spl384_5
    | ~ spl384_81 ),
    inference(avatar_split_clause,[],[f7954,f7827,f6673,f6636,f7956])).

fof(f7954,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_tarski(k1_xboole_0))
    | ~ spl384_2
    | ~ spl384_5
    | ~ spl384_81 ),
    inference(forward_demodulation,[],[f7953,f6675])).

fof(f7953,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl384_2
    | ~ spl384_81 ),
    inference(forward_demodulation,[],[f7952,f6473])).

fof(f6473,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f4817])).

fof(f4817,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f7952,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl384_2
    | ~ spl384_81 ),
    inference(subsumption_resolution,[],[f7882,f6638])).

fof(f7882,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ l1_orders_2(sK0)
    | ~ spl384_81 ),
    inference(superposition,[],[f4556,f7829])).

fof(f7829,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl384_81 ),
    inference(avatar_component_clause,[],[f7827])).

fof(f4556,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3192])).

fof(f3192,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1905])).

fof(f1905,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f7948,plain,
    ( ~ spl384_93
    | spl384_94
    | ~ spl384_2
    | spl384_3
    | ~ spl384_81 ),
    inference(avatar_split_clause,[],[f7940,f7827,f6641,f6636,f7946,f7942])).

fof(f7942,plain,
    ( spl384_93
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_93])])).

fof(f7946,plain,
    ( spl384_94
  <=> ! [X18] :
        ( ~ m1_subset_1(X18,k1_xboole_0)
        | r1_orders_2(sK0,X18,X18) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_94])])).

fof(f7940,plain,
    ( ! [X18] :
        ( ~ m1_subset_1(X18,k1_xboole_0)
        | ~ v3_orders_2(sK0)
        | r1_orders_2(sK0,X18,X18) )
    | ~ spl384_2
    | spl384_3
    | ~ spl384_81 ),
    inference(subsumption_resolution,[],[f7939,f6643])).

fof(f7939,plain,
    ( ! [X18] :
        ( ~ m1_subset_1(X18,k1_xboole_0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | r1_orders_2(sK0,X18,X18) )
    | ~ spl384_2
    | ~ spl384_81 ),
    inference(subsumption_resolution,[],[f7875,f6638])).

fof(f7875,plain,
    ( ! [X18] :
        ( ~ m1_subset_1(X18,k1_xboole_0)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | r1_orders_2(sK0,X18,X18) )
    | ~ spl384_81 ),
    inference(superposition,[],[f4421,f7829])).

fof(f4421,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r1_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f3113])).

fof(f3113,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3112])).

fof(f3112,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1952])).

fof(f1952,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f7938,plain,
    ( spl384_92
    | ~ spl384_2
    | ~ spl384_81
    | spl384_83 ),
    inference(avatar_split_clause,[],[f7933,f7843,f7827,f6636,f7935])).

fof(f7843,plain,
    ( spl384_83
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_83])])).

fof(f7933,plain,
    ( m1_subset_1(sK21(sK0),k1_xboole_0)
    | ~ spl384_2
    | ~ spl384_81
    | spl384_83 ),
    inference(subsumption_resolution,[],[f7932,f7844])).

fof(f7844,plain,
    ( ~ v1_lattice3(sK0)
    | spl384_83 ),
    inference(avatar_component_clause,[],[f7843])).

fof(f7932,plain,
    ( m1_subset_1(sK21(sK0),k1_xboole_0)
    | v1_lattice3(sK0)
    | ~ spl384_2
    | ~ spl384_81 ),
    inference(subsumption_resolution,[],[f7874,f6638])).

fof(f7874,plain,
    ( m1_subset_1(sK21(sK0),k1_xboole_0)
    | ~ l1_orders_2(sK0)
    | v1_lattice3(sK0)
    | ~ spl384_81 ),
    inference(superposition,[],[f4417,f7829])).

fof(f4417,plain,(
    ! [X0] :
      ( m1_subset_1(sK21(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f3105])).

fof(f3105,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3104])).

fof(f3104,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r1_orders_2(X0,X2,X4)
                        | ~ r1_orders_2(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2810])).

fof(f2810,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r1_orders_2(X0,X2,X4)
                            & r1_orders_2(X0,X1,X4) )
                         => r1_orders_2(X0,X3,X4) ) )
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_lattice3)).

fof(f7931,plain,
    ( spl384_91
    | ~ spl384_2
    | ~ spl384_81
    | spl384_83 ),
    inference(avatar_split_clause,[],[f7926,f7843,f7827,f6636,f7928])).

fof(f7926,plain,
    ( m1_subset_1(sK22(sK0),k1_xboole_0)
    | ~ spl384_2
    | ~ spl384_81
    | spl384_83 ),
    inference(subsumption_resolution,[],[f7925,f7844])).

fof(f7925,plain,
    ( m1_subset_1(sK22(sK0),k1_xboole_0)
    | v1_lattice3(sK0)
    | ~ spl384_2
    | ~ spl384_81 ),
    inference(subsumption_resolution,[],[f7873,f6638])).

fof(f7873,plain,
    ( m1_subset_1(sK22(sK0),k1_xboole_0)
    | ~ l1_orders_2(sK0)
    | v1_lattice3(sK0)
    | ~ spl384_81 ),
    inference(superposition,[],[f4416,f7829])).

fof(f4416,plain,(
    ! [X0] :
      ( m1_subset_1(sK22(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f3105])).

fof(f7924,plain,
    ( spl384_88
    | spl384_90
    | ~ spl384_2
    | ~ spl384_81 ),
    inference(avatar_split_clause,[],[f7919,f7827,f6636,f7921,f7911])).

fof(f7919,plain,
    ( m1_subset_1(sK17(sK0),k1_xboole_0)
    | v2_lattice3(sK0)
    | ~ spl384_2
    | ~ spl384_81 ),
    inference(subsumption_resolution,[],[f7872,f6638])).

fof(f7872,plain,
    ( m1_subset_1(sK17(sK0),k1_xboole_0)
    | ~ l1_orders_2(sK0)
    | v2_lattice3(sK0)
    | ~ spl384_81 ),
    inference(superposition,[],[f4406,f7829])).

fof(f4406,plain,(
    ! [X0] :
      ( m1_subset_1(sK17(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f3101])).

fof(f7918,plain,
    ( spl384_88
    | spl384_89
    | ~ spl384_2
    | ~ spl384_81 ),
    inference(avatar_split_clause,[],[f7909,f7827,f6636,f7915,f7911])).

fof(f7909,plain,
    ( m1_subset_1(sK18(sK0),k1_xboole_0)
    | v2_lattice3(sK0)
    | ~ spl384_2
    | ~ spl384_81 ),
    inference(subsumption_resolution,[],[f7871,f6638])).

fof(f7871,plain,
    ( m1_subset_1(sK18(sK0),k1_xboole_0)
    | ~ l1_orders_2(sK0)
    | v2_lattice3(sK0)
    | ~ spl384_81 ),
    inference(superposition,[],[f4405,f7829])).

fof(f7904,plain,
    ( spl384_87
    | spl384_86
    | ~ spl384_2
    | spl384_3
    | ~ spl384_81 ),
    inference(avatar_split_clause,[],[f7900,f7827,f6641,f6636,f7894,f7902])).

fof(f7902,plain,
    ( spl384_87
  <=> ! [X10] : ~ r2_yellow_0(sK0,X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_87])])).

fof(f7900,plain,
    ( ! [X10] :
        ( r2_yellow_0(sK0,k1_xboole_0)
        | ~ r2_yellow_0(sK0,X10) )
    | ~ spl384_2
    | spl384_3
    | ~ spl384_81 ),
    inference(forward_demodulation,[],[f7899,f4679])).

fof(f7899,plain,
    ( ! [X10] :
        ( r2_yellow_0(sK0,k3_xboole_0(X10,k1_xboole_0))
        | ~ r2_yellow_0(sK0,X10) )
    | ~ spl384_2
    | spl384_3
    | ~ spl384_81 ),
    inference(subsumption_resolution,[],[f7898,f6643])).

fof(f7898,plain,
    ( ! [X10] :
        ( r2_yellow_0(sK0,k3_xboole_0(X10,k1_xboole_0))
        | ~ r2_yellow_0(sK0,X10)
        | v2_struct_0(sK0) )
    | ~ spl384_2
    | ~ spl384_81 ),
    inference(subsumption_resolution,[],[f7865,f6638])).

fof(f7865,plain,
    ( ! [X10] :
        ( r2_yellow_0(sK0,k3_xboole_0(X10,k1_xboole_0))
        | ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X10)
        | v2_struct_0(sK0) )
    | ~ spl384_81 ),
    inference(superposition,[],[f4370,f7829])).

fof(f7897,plain,
    ( spl384_85
    | ~ spl384_86
    | ~ spl384_2
    | spl384_3
    | ~ spl384_81 ),
    inference(avatar_split_clause,[],[f7889,f7827,f6641,f6636,f7894,f7891])).

fof(f7891,plain,
    ( spl384_85
  <=> ! [X9] : r2_yellow_0(sK0,X9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_85])])).

fof(f7889,plain,
    ( ! [X9] :
        ( ~ r2_yellow_0(sK0,k1_xboole_0)
        | r2_yellow_0(sK0,X9) )
    | ~ spl384_2
    | spl384_3
    | ~ spl384_81 ),
    inference(forward_demodulation,[],[f7888,f4679])).

fof(f7888,plain,
    ( ! [X9] :
        ( ~ r2_yellow_0(sK0,k3_xboole_0(X9,k1_xboole_0))
        | r2_yellow_0(sK0,X9) )
    | ~ spl384_2
    | spl384_3
    | ~ spl384_81 ),
    inference(subsumption_resolution,[],[f7887,f6643])).

fof(f7887,plain,
    ( ! [X9] :
        ( ~ r2_yellow_0(sK0,k3_xboole_0(X9,k1_xboole_0))
        | v2_struct_0(sK0)
        | r2_yellow_0(sK0,X9) )
    | ~ spl384_2
    | ~ spl384_81 ),
    inference(subsumption_resolution,[],[f7864,f6638])).

fof(f7864,plain,
    ( ! [X9] :
        ( ~ r2_yellow_0(sK0,k3_xboole_0(X9,k1_xboole_0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | r2_yellow_0(sK0,X9) )
    | ~ spl384_81 ),
    inference(superposition,[],[f4369,f7829])).

fof(f4369,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3093])).

fof(f7850,plain,
    ( spl384_83
    | ~ spl384_84
    | ~ spl384_2
    | spl384_3
    | ~ spl384_6
    | ~ spl384_58
    | ~ spl384_81 ),
    inference(avatar_split_clause,[],[f7841,f7827,f7082,f6678,f6641,f6636,f7847,f7843])).

fof(f7847,plain,
    ( spl384_84
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_84])])).

fof(f7082,plain,
    ( spl384_58
  <=> r1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_58])])).

fof(f7841,plain,
    ( ~ v5_orders_2(sK0)
    | v1_lattice3(sK0)
    | ~ spl384_2
    | spl384_3
    | ~ spl384_6
    | ~ spl384_58
    | ~ spl384_81 ),
    inference(subsumption_resolution,[],[f7839,f6638])).

fof(f7839,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | v1_lattice3(sK0)
    | ~ spl384_2
    | spl384_3
    | ~ spl384_6
    | ~ spl384_58
    | ~ spl384_81 ),
    inference(resolution,[],[f7838,f4363])).

fof(f4363,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(X0,k2_tarski(sK8(X0),sK9(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f3089])).

fof(f3089,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3088])).

fof(f3088,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2999])).

fof(f2999,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_0)).

fof(f7838,plain,
    ( ! [X0] : r1_yellow_0(sK0,X0)
    | ~ spl384_2
    | spl384_3
    | ~ spl384_6
    | ~ spl384_58
    | ~ spl384_81 ),
    inference(subsumption_resolution,[],[f7837,f6680])).

fof(f7837,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | r1_yellow_0(sK0,X0) )
    | ~ spl384_2
    | spl384_3
    | ~ spl384_58
    | ~ spl384_81 ),
    inference(forward_demodulation,[],[f7834,f4679])).

fof(f7834,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k3_xboole_0(X0,k1_xboole_0))
        | r1_yellow_0(sK0,X0) )
    | ~ spl384_2
    | spl384_3
    | ~ spl384_58
    | ~ spl384_81 ),
    inference(backward_demodulation,[],[f7567,f7829])).

fof(f7567,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k3_xboole_0(X0,u1_struct_0(sK0)))
        | r1_yellow_0(sK0,X0) )
    | ~ spl384_2
    | spl384_3
    | ~ spl384_58 ),
    inference(subsumption_resolution,[],[f7566,f6643])).

fof(f7566,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k3_xboole_0(X0,u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | r1_yellow_0(sK0,X0) )
    | ~ spl384_2
    | ~ spl384_58 ),
    inference(subsumption_resolution,[],[f7565,f6638])).

fof(f7565,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k3_xboole_0(X0,u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | r1_yellow_0(sK0,X0) )
    | ~ spl384_58 ),
    inference(resolution,[],[f7543,f4371])).

fof(f7543,plain,
    ( ! [X0] :
        ( r1_yellow_0(sK0,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl384_58 ),
    inference(superposition,[],[f7084,f4827])).

fof(f7084,plain,
    ( r1_yellow_0(sK0,k1_xboole_0)
    | ~ spl384_58 ),
    inference(avatar_component_clause,[],[f7082])).

fof(f7833,plain,
    ( spl384_81
    | spl384_82 ),
    inference(avatar_split_clause,[],[f7818,f7831,f7827])).

fof(f7831,plain,
    ( spl384_82
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_yellow_0(sK0,k2_tarski(X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_82])])).

fof(f7818,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_xboole_0 = u1_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_yellow_0(sK0,k2_tarski(X1,X0)) ) ),
    inference(resolution,[],[f4623,f4329])).

fof(f4623,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f3221])).

fof(f3221,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          | k1_xboole_0 = X0
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f3220])).

fof(f3220,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          | k1_xboole_0 = X0
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f528])).

fof(f528,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ( k1_xboole_0 != X0
           => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_subset_1)).

fof(f7680,plain,
    ( spl384_80
    | ~ spl384_15
    | ~ spl384_66 ),
    inference(avatar_split_clause,[],[f7668,f7161,f6724,f7677])).

fof(f7677,plain,
    ( spl384_80
  <=> v3_relat_2(sK74) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_80])])).

fof(f6724,plain,
    ( spl384_15
  <=> v1_xboole_0(sK74) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_15])])).

fof(f7161,plain,
    ( spl384_66
  <=> v3_relat_2(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_66])])).

fof(f7668,plain,
    ( v3_relat_2(sK74)
    | ~ spl384_15
    | ~ spl384_66 ),
    inference(resolution,[],[f7549,f6726])).

fof(f6726,plain,
    ( v1_xboole_0(sK74)
    | ~ spl384_15 ),
    inference(avatar_component_clause,[],[f6724])).

fof(f7549,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v3_relat_2(X0) )
    | ~ spl384_66 ),
    inference(superposition,[],[f7163,f4827])).

fof(f7163,plain,
    ( v3_relat_2(k1_xboole_0)
    | ~ spl384_66 ),
    inference(avatar_component_clause,[],[f7161])).

fof(f7675,plain,
    ( spl384_79
    | ~ spl384_33
    | ~ spl384_66 ),
    inference(avatar_split_clause,[],[f7667,f7161,f6863,f7672])).

fof(f7672,plain,
    ( spl384_79
  <=> v3_relat_2(k1_wellord2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_79])])).

fof(f6863,plain,
    ( spl384_33
  <=> v1_xboole_0(k1_wellord2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_33])])).

fof(f7667,plain,
    ( v3_relat_2(k1_wellord2(k1_xboole_0))
    | ~ spl384_33
    | ~ spl384_66 ),
    inference(resolution,[],[f7549,f6865])).

fof(f6865,plain,
    ( v1_xboole_0(k1_wellord2(k1_xboole_0))
    | ~ spl384_33 ),
    inference(avatar_component_clause,[],[f6863])).

fof(f7610,plain,
    ( spl384_78
    | ~ spl384_15
    | ~ spl384_65 ),
    inference(avatar_split_clause,[],[f7603,f7156,f6724,f7607])).

fof(f7607,plain,
    ( spl384_78
  <=> v4_relat_2(sK74) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_78])])).

fof(f7156,plain,
    ( spl384_65
  <=> v4_relat_2(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_65])])).

fof(f7603,plain,
    ( v4_relat_2(sK74)
    | ~ spl384_15
    | ~ spl384_65 ),
    inference(resolution,[],[f7548,f6726])).

fof(f7548,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v4_relat_2(X0) )
    | ~ spl384_65 ),
    inference(superposition,[],[f7158,f4827])).

fof(f7158,plain,
    ( v4_relat_2(k1_xboole_0)
    | ~ spl384_65 ),
    inference(avatar_component_clause,[],[f7156])).

fof(f7577,plain,
    ( spl384_77
    | ~ spl384_15
    | ~ spl384_64 ),
    inference(avatar_split_clause,[],[f7570,f7151,f6724,f7574])).

fof(f7574,plain,
    ( spl384_77
  <=> v8_relat_2(sK74) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_77])])).

fof(f7151,plain,
    ( spl384_64
  <=> v8_relat_2(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_64])])).

fof(f7570,plain,
    ( v8_relat_2(sK74)
    | ~ spl384_15
    | ~ spl384_64 ),
    inference(resolution,[],[f7547,f6726])).

fof(f7547,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v8_relat_2(X0) )
    | ~ spl384_64 ),
    inference(superposition,[],[f7153,f4827])).

fof(f7153,plain,
    ( v8_relat_2(k1_xboole_0)
    | ~ spl384_64 ),
    inference(avatar_component_clause,[],[f7151])).

fof(f7424,plain,
    ( spl384_76
    | ~ spl384_15 ),
    inference(avatar_split_clause,[],[f7407,f6724,f7421])).

fof(f7421,plain,
    ( spl384_76
  <=> v1_finset_1(sK74) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_76])])).

fof(f7407,plain,
    ( v1_finset_1(sK74)
    | ~ spl384_15 ),
    inference(resolution,[],[f6282,f6726])).

fof(f6282,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f4293])).

fof(f4293,plain,(
    ! [X0] :
      ( v1_finset_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1707])).

fof(f1707,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_finset_1)).

fof(f7419,plain,
    ( spl384_75
    | ~ spl384_33 ),
    inference(avatar_split_clause,[],[f7406,f6863,f7416])).

fof(f7416,plain,
    ( spl384_75
  <=> v1_finset_1(k1_wellord2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_75])])).

fof(f7406,plain,
    ( v1_finset_1(k1_wellord2(k1_xboole_0))
    | ~ spl384_33 ),
    inference(resolution,[],[f6282,f6865])).

fof(f7414,plain,
    ( spl384_74
    | ~ spl384_6 ),
    inference(avatar_split_clause,[],[f7405,f6678,f7411])).

fof(f7411,plain,
    ( spl384_74
  <=> v1_finset_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_74])])).

fof(f7405,plain,
    ( v1_finset_1(k1_xboole_0)
    | ~ spl384_6 ),
    inference(resolution,[],[f6282,f6680])).

fof(f7330,plain,
    ( spl384_73
    | ~ spl384_15 ),
    inference(avatar_split_clause,[],[f7313,f6724,f7327])).

fof(f7327,plain,
    ( spl384_73
  <=> v3_ordinal1(sK74) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_73])])).

fof(f7313,plain,
    ( v3_ordinal1(sK74)
    | ~ spl384_15 ),
    inference(resolution,[],[f6189,f6726])).

fof(f6189,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f4248])).

fof(f4248,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1056])).

fof(f1056,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_ordinal1)).

fof(f7325,plain,
    ( spl384_72
    | ~ spl384_33 ),
    inference(avatar_split_clause,[],[f7312,f6863,f7322])).

fof(f7322,plain,
    ( spl384_72
  <=> v3_ordinal1(k1_wellord2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_72])])).

fof(f7312,plain,
    ( v3_ordinal1(k1_wellord2(k1_xboole_0))
    | ~ spl384_33 ),
    inference(resolution,[],[f6189,f6865])).

fof(f7320,plain,
    ( spl384_71
    | ~ spl384_6 ),
    inference(avatar_split_clause,[],[f7311,f6678,f7317])).

fof(f7317,plain,
    ( spl384_71
  <=> v3_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_71])])).

fof(f7311,plain,
    ( v3_ordinal1(k1_xboole_0)
    | ~ spl384_6 ),
    inference(resolution,[],[f6189,f6680])).

fof(f7302,plain,
    ( spl384_70
    | ~ spl384_34 ),
    inference(avatar_split_clause,[],[f7297,f6875,f7299])).

fof(f7299,plain,
    ( spl384_70
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_70])])).

fof(f6875,plain,
    ( spl384_34
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_34])])).

fof(f7297,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl384_34 ),
    inference(superposition,[],[f5561,f6877])).

fof(f6877,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl384_34 ),
    inference(avatar_component_clause,[],[f6875])).

fof(f5561,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f1522])).

fof(f1522,axiom,(
    ! [X0] :
      ( v1_partfun1(k6_relat_1(X0),X0)
      & v1_funct_1(k6_relat_1(X0))
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_funct_2)).

fof(f7207,plain,
    ( spl384_69
    | ~ spl384_15 ),
    inference(avatar_split_clause,[],[f7196,f6724,f7204])).

fof(f7204,plain,
    ( spl384_69
  <=> v2_funct_1(sK74) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_69])])).

fof(f7196,plain,
    ( v2_funct_1(sK74)
    | ~ spl384_15 ),
    inference(resolution,[],[f6929,f6726])).

fof(f6929,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v2_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f6928,f4927])).

fof(f4927,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f3405])).

fof(f3405,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f890])).

fof(f890,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f6928,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f6021,f4928])).

fof(f4928,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3406])).

fof(f3406,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f6021,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f4124])).

fof(f4124,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f4123])).

fof(f4123,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f891])).

fof(f891,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

fof(f7202,plain,
    ( spl384_68
    | ~ spl384_33 ),
    inference(avatar_split_clause,[],[f7195,f6863,f7199])).

fof(f7199,plain,
    ( spl384_68
  <=> v2_funct_1(k1_wellord2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_68])])).

fof(f7195,plain,
    ( v2_funct_1(k1_wellord2(k1_xboole_0))
    | ~ spl384_33 ),
    inference(resolution,[],[f6929,f6865])).

fof(f7169,plain,
    ( spl384_67
    | ~ spl384_34 ),
    inference(avatar_split_clause,[],[f7149,f6875,f7166])).

fof(f7166,plain,
    ( spl384_67
  <=> v2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_67])])).

fof(f7149,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl384_34 ),
    inference(superposition,[],[f5608,f6877])).

fof(f5608,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f922])).

fof(f922,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f7164,plain,
    ( spl384_66
    | ~ spl384_34 ),
    inference(avatar_split_clause,[],[f7147,f6875,f7161])).

fof(f7147,plain,
    ( v3_relat_2(k1_xboole_0)
    | ~ spl384_34 ),
    inference(superposition,[],[f4901,f6877])).

fof(f4901,plain,(
    ! [X0] : v3_relat_2(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1532])).

fof(f1532,axiom,(
    ! [X0] :
      ( v8_relat_2(k6_relat_1(X0))
      & v4_relat_2(k6_relat_1(X0))
      & v3_relat_2(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_partfun1)).

fof(f7159,plain,
    ( spl384_65
    | ~ spl384_34 ),
    inference(avatar_split_clause,[],[f7146,f6875,f7156])).

fof(f7146,plain,
    ( v4_relat_2(k1_xboole_0)
    | ~ spl384_34 ),
    inference(superposition,[],[f4902,f6877])).

fof(f4902,plain,(
    ! [X0] : v4_relat_2(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1532])).

fof(f7154,plain,
    ( spl384_64
    | ~ spl384_34 ),
    inference(avatar_split_clause,[],[f7145,f6875,f7151])).

fof(f7145,plain,
    ( v8_relat_2(k1_xboole_0)
    | ~ spl384_34 ),
    inference(superposition,[],[f4903,f6877])).

fof(f4903,plain,(
    ! [X0] : v8_relat_2(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1532])).

fof(f7131,plain,
    ( spl384_63
    | ~ spl384_15 ),
    inference(avatar_split_clause,[],[f7120,f6724,f7128])).

fof(f7128,plain,
    ( spl384_63
  <=> v1_relat_1(sK74) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_63])])).

fof(f7120,plain,
    ( v1_relat_1(sK74)
    | ~ spl384_15 ),
    inference(resolution,[],[f4928,f6726])).

fof(f7126,plain,
    ( spl384_62
    | ~ spl384_6 ),
    inference(avatar_split_clause,[],[f7118,f6678,f7123])).

fof(f7118,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl384_6 ),
    inference(resolution,[],[f4928,f6680])).

fof(f7108,plain,
    ( spl384_61
    | ~ spl384_15 ),
    inference(avatar_split_clause,[],[f7092,f6724,f7105])).

fof(f7105,plain,
    ( spl384_61
  <=> v1_funct_1(sK74) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_61])])).

fof(f7092,plain,
    ( v1_funct_1(sK74)
    | ~ spl384_15 ),
    inference(resolution,[],[f4927,f6726])).

fof(f7103,plain,
    ( spl384_60
    | ~ spl384_33 ),
    inference(avatar_split_clause,[],[f7091,f6863,f7100])).

fof(f7100,plain,
    ( spl384_60
  <=> v1_funct_1(k1_wellord2(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_60])])).

fof(f7091,plain,
    ( v1_funct_1(k1_wellord2(k1_xboole_0))
    | ~ spl384_33 ),
    inference(resolution,[],[f4927,f6865])).

fof(f7098,plain,
    ( spl384_59
    | ~ spl384_6 ),
    inference(avatar_split_clause,[],[f7090,f6678,f7095])).

fof(f7095,plain,
    ( spl384_59
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_59])])).

fof(f7090,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl384_6 ),
    inference(resolution,[],[f4927,f6680])).

fof(f7085,plain,(
    spl384_58 ),
    inference(avatar_split_clause,[],[f7080,f7082])).

fof(f7080,plain,(
    r1_yellow_0(sK0,k1_xboole_0) ),
    inference(resolution,[],[f4829,f4329])).

fof(f7067,plain,(
    spl384_57 ),
    inference(avatar_split_clause,[],[f7062,f7064])).

fof(f7064,plain,
    ( spl384_57
  <=> r1_yellow_0(sK0,sK15(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_57])])).

fof(f7062,plain,(
    r1_yellow_0(sK0,sK15(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f4395,f4329])).

fof(f7050,plain,(
    spl384_56 ),
    inference(avatar_split_clause,[],[f6395,f7047])).

fof(f7047,plain,
    ( spl384_56
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_56])])).

fof(f6395,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f387])).

fof(f387,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f7045,plain,
    ( spl384_53
    | spl384_55 ),
    inference(avatar_split_clause,[],[f6264,f7041,f7033])).

fof(f7033,plain,
    ( spl384_53
  <=> ! [X7] :
        ( ~ r2_hidden(X7,k1_xboole_0)
        | ~ r1_tarski(sK324(X7),X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_53])])).

fof(f7041,plain,
    ( spl384_55
  <=> ! [X5,X0] :
        ( ~ v1_finset_1(X0)
        | sP323(sK322(X0),X0)
        | k1_xboole_0 = X0
        | r2_hidden(sK326(X0,X5),k2_xboole_0(sK321(X0),k1_tarski(sK320(X0))))
        | ~ r2_hidden(X5,k2_xboole_0(sK321(X0),k1_tarski(sK320(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_55])])).

fof(f6264,plain,(
    ! [X0,X7,X5] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X7,k1_xboole_0)
      | ~ r1_tarski(sK324(X7),X7)
      | ~ r2_hidden(X5,k2_xboole_0(sK321(X0),k1_tarski(sK320(X0))))
      | r2_hidden(sK326(X0,X5),k2_xboole_0(sK321(X0),k1_tarski(sK320(X0))))
      | k1_xboole_0 = X0
      | sP323(sK322(X0),X0) ) ),
    inference(cnf_transformation,[],[f4292])).

fof(f4292,plain,(
    ! [X0] :
      ( ? [X9] :
          ( ! [X10] :
              ( r1_tarski(X10,X9)
              | ~ r2_hidden(X10,X0) )
          & r2_hidden(X9,X0) )
      | k1_xboole_0 = X0
      | ? [X1,X2] :
          ( ! [X5] :
              ( ? [X6] :
                  ( ~ r1_tarski(X6,X5)
                  & r2_hidden(X6,k2_xboole_0(X2,k1_tarski(X1))) )
              | ~ r2_hidden(X5,k2_xboole_0(X2,k1_tarski(X1))) )
          & k1_xboole_0 != k2_xboole_0(X2,k1_tarski(X1))
          & ( ? [X3] :
                ( ! [X4] :
                    ( r1_tarski(X4,X3)
                    | ~ r2_hidden(X4,X2) )
                & r2_hidden(X3,X2) )
            | k1_xboole_0 = X2 )
          & r1_tarski(X2,X0)
          & r2_hidden(X1,X0) )
      | ( ! [X7] :
            ( ? [X8] :
                ( ~ r1_tarski(X8,X7)
                & r2_hidden(X8,k1_xboole_0) )
            | ~ r2_hidden(X7,k1_xboole_0) )
        & k1_xboole_0 != k1_xboole_0 )
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f4291])).

fof(f4291,plain,(
    ! [X0] :
      ( ? [X9] :
          ( ! [X10] :
              ( r1_tarski(X10,X9)
              | ~ r2_hidden(X10,X0) )
          & r2_hidden(X9,X0) )
      | k1_xboole_0 = X0
      | ? [X1,X2] :
          ( ! [X5] :
              ( ? [X6] :
                  ( ~ r1_tarski(X6,X5)
                  & r2_hidden(X6,k2_xboole_0(X2,k1_tarski(X1))) )
              | ~ r2_hidden(X5,k2_xboole_0(X2,k1_tarski(X1))) )
          & k1_xboole_0 != k2_xboole_0(X2,k1_tarski(X1))
          & ( ? [X3] :
                ( ! [X4] :
                    ( r1_tarski(X4,X3)
                    | ~ r2_hidden(X4,X2) )
                & r2_hidden(X3,X2) )
            | k1_xboole_0 = X2 )
          & r1_tarski(X2,X0)
          & r2_hidden(X1,X0) )
      | ( ! [X7] :
            ( ? [X8] :
                ( ~ r1_tarski(X8,X7)
                & r2_hidden(X8,k1_xboole_0) )
            | ~ r2_hidden(X7,k1_xboole_0) )
        & k1_xboole_0 != k1_xboole_0 )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f3068])).

fof(f3068,plain,(
    ! [X0] :
      ( ( ! [X1,X2] :
            ( ( ~ ( ! [X3] :
                      ~ ( ! [X4] :
                            ( r2_hidden(X4,X2)
                           => r1_tarski(X4,X3) )
                        & r2_hidden(X3,X2) )
                  & k1_xboole_0 != X2 )
              & r1_tarski(X2,X0)
              & r2_hidden(X1,X0) )
           => ~ ( ! [X5] :
                    ~ ( ! [X6] :
                          ( r2_hidden(X6,k2_xboole_0(X2,k1_tarski(X1)))
                         => r1_tarski(X6,X5) )
                      & r2_hidden(X5,k2_xboole_0(X2,k1_tarski(X1))) )
                & k1_xboole_0 != k2_xboole_0(X2,k1_tarski(X1)) ) )
        & ~ ( ! [X7] :
                ~ ( ! [X8] :
                      ( r2_hidden(X8,k1_xboole_0)
                     => r1_tarski(X8,X7) )
                  & r2_hidden(X7,k1_xboole_0) )
            & k1_xboole_0 != k1_xboole_0 )
        & v1_finset_1(X0) )
     => ~ ( ! [X9] :
              ~ ( ! [X10] :
                    ( r2_hidden(X10,X0)
                   => r1_tarski(X10,X9) )
                & r2_hidden(X9,X0) )
          & k1_xboole_0 != X0 ) ) ),
    inference(rectify,[],[f1738])).

fof(f1738,axiom,(
    ! [X0] :
      ( ( ! [X3,X4] :
            ( ( ~ ( ! [X5] :
                      ~ ( ! [X6] :
                            ( r2_hidden(X6,X4)
                           => r1_tarski(X6,X5) )
                        & r2_hidden(X5,X4) )
                  & k1_xboole_0 != X4 )
              & r1_tarski(X4,X0)
              & r2_hidden(X3,X0) )
           => ~ ( ! [X7] :
                    ~ ( ! [X8] :
                          ( r2_hidden(X8,k2_xboole_0(X4,k1_tarski(X3)))
                         => r1_tarski(X8,X7) )
                      & r2_hidden(X7,k2_xboole_0(X4,k1_tarski(X3))) )
                & k1_xboole_0 != k2_xboole_0(X4,k1_tarski(X3)) ) )
        & ~ ( ! [X1] :
                ~ ( ! [X2] :
                      ( r2_hidden(X2,k1_xboole_0)
                     => r1_tarski(X2,X1) )
                  & r2_hidden(X1,k1_xboole_0) )
            & k1_xboole_0 != k1_xboole_0 )
        & v1_finset_1(X0) )
     => ~ ( ! [X9] :
              ~ ( ! [X10] :
                    ( r2_hidden(X10,X0)
                   => r1_tarski(X10,X9) )
                & r2_hidden(X9,X0) )
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s2_finset_1__e6_54__finset_1)).

fof(f7044,plain,
    ( spl384_53
    | spl384_54 ),
    inference(avatar_split_clause,[],[f6265,f7037,f7033])).

fof(f7037,plain,
    ( spl384_54
  <=> ! [X5,X0] :
        ( ~ v1_finset_1(X0)
        | sP323(sK322(X0),X0)
        | k1_xboole_0 = X0
        | ~ r1_tarski(sK326(X0,X5),X5)
        | ~ r2_hidden(X5,k2_xboole_0(sK321(X0),k1_tarski(sK320(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_54])])).

fof(f6265,plain,(
    ! [X0,X7,X5] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X7,k1_xboole_0)
      | ~ r1_tarski(sK324(X7),X7)
      | ~ r2_hidden(X5,k2_xboole_0(sK321(X0),k1_tarski(sK320(X0))))
      | ~ r1_tarski(sK326(X0,X5),X5)
      | k1_xboole_0 = X0
      | sP323(sK322(X0),X0) ) ),
    inference(cnf_transformation,[],[f4292])).

fof(f7043,plain,
    ( spl384_51
    | spl384_55 ),
    inference(avatar_split_clause,[],[f6266,f7041,f7026])).

fof(f7026,plain,
    ( spl384_51
  <=> ! [X7] :
        ( ~ r2_hidden(X7,k1_xboole_0)
        | r2_hidden(sK324(X7),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_51])])).

fof(f6266,plain,(
    ! [X0,X7,X5] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X7,k1_xboole_0)
      | r2_hidden(sK324(X7),k1_xboole_0)
      | ~ r2_hidden(X5,k2_xboole_0(sK321(X0),k1_tarski(sK320(X0))))
      | r2_hidden(sK326(X0,X5),k2_xboole_0(sK321(X0),k1_tarski(sK320(X0))))
      | k1_xboole_0 = X0
      | sP323(sK322(X0),X0) ) ),
    inference(cnf_transformation,[],[f4292])).

fof(f7039,plain,
    ( spl384_51
    | spl384_54 ),
    inference(avatar_split_clause,[],[f6267,f7037,f7026])).

fof(f6267,plain,(
    ! [X0,X7,X5] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X7,k1_xboole_0)
      | r2_hidden(sK324(X7),k1_xboole_0)
      | ~ r2_hidden(X5,k2_xboole_0(sK321(X0),k1_tarski(sK320(X0))))
      | ~ r1_tarski(sK326(X0,X5),X5)
      | k1_xboole_0 = X0
      | sP323(sK322(X0),X0) ) ),
    inference(cnf_transformation,[],[f4292])).

fof(f7035,plain,
    ( spl384_53
    | spl384_52 ),
    inference(avatar_split_clause,[],[f6270,f7029,f7033])).

fof(f7029,plain,
    ( spl384_52
  <=> ! [X0] :
        ( ~ v1_finset_1(X0)
        | sP323(sK322(X0),X0)
        | k1_xboole_0 = X0
        | r2_hidden(sK325(X0),sK321(X0))
        | k1_xboole_0 = sK321(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_52])])).

fof(f6270,plain,(
    ! [X0,X7] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X7,k1_xboole_0)
      | ~ r1_tarski(sK324(X7),X7)
      | k1_xboole_0 = sK321(X0)
      | r2_hidden(sK325(X0),sK321(X0))
      | k1_xboole_0 = X0
      | sP323(sK322(X0),X0) ) ),
    inference(cnf_transformation,[],[f4292])).

fof(f7031,plain,
    ( spl384_51
    | spl384_52 ),
    inference(avatar_split_clause,[],[f6271,f7029,f7026])).

fof(f6271,plain,(
    ! [X0,X7] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X7,k1_xboole_0)
      | r2_hidden(sK324(X7),k1_xboole_0)
      | k1_xboole_0 = sK321(X0)
      | r2_hidden(sK325(X0),sK321(X0))
      | k1_xboole_0 = X0
      | sP323(sK322(X0),X0) ) ),
    inference(cnf_transformation,[],[f4292])).

fof(f7024,plain,
    ( spl384_48
    | spl384_50 ),
    inference(avatar_split_clause,[],[f6241,f7020,f7012])).

fof(f7012,plain,
    ( spl384_48
  <=> ! [X7] :
        ( ~ r2_hidden(X7,k1_xboole_0)
        | ~ r1_tarski(X7,sK317(X7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_48])])).

fof(f7020,plain,
    ( spl384_50
  <=> ! [X5,X0] :
        ( ~ v1_finset_1(X0)
        | sP316(sK315(X0),X0)
        | k1_xboole_0 = X0
        | r2_hidden(sK319(X0,X5),k2_xboole_0(sK314(X0),k1_tarski(sK313(X0))))
        | ~ r2_hidden(X5,k2_xboole_0(sK314(X0),k1_tarski(sK313(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_50])])).

fof(f6241,plain,(
    ! [X0,X7,X5] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X7,k1_xboole_0)
      | ~ r1_tarski(X7,sK317(X7))
      | ~ r2_hidden(X5,k2_xboole_0(sK314(X0),k1_tarski(sK313(X0))))
      | r2_hidden(sK319(X0,X5),k2_xboole_0(sK314(X0),k1_tarski(sK313(X0))))
      | k1_xboole_0 = X0
      | sP316(sK315(X0),X0) ) ),
    inference(cnf_transformation,[],[f4290])).

fof(f4290,plain,(
    ! [X0] :
      ( ? [X9] :
          ( ! [X10] :
              ( r1_tarski(X9,X10)
              | ~ r2_hidden(X10,X0) )
          & r2_hidden(X9,X0) )
      | k1_xboole_0 = X0
      | ? [X1,X2] :
          ( ! [X5] :
              ( ? [X6] :
                  ( ~ r1_tarski(X5,X6)
                  & r2_hidden(X6,k2_xboole_0(X2,k1_tarski(X1))) )
              | ~ r2_hidden(X5,k2_xboole_0(X2,k1_tarski(X1))) )
          & k1_xboole_0 != k2_xboole_0(X2,k1_tarski(X1))
          & ( ? [X3] :
                ( ! [X4] :
                    ( r1_tarski(X3,X4)
                    | ~ r2_hidden(X4,X2) )
                & r2_hidden(X3,X2) )
            | k1_xboole_0 = X2 )
          & r1_tarski(X2,X0)
          & r2_hidden(X1,X0) )
      | ( ! [X7] :
            ( ? [X8] :
                ( ~ r1_tarski(X7,X8)
                & r2_hidden(X8,k1_xboole_0) )
            | ~ r2_hidden(X7,k1_xboole_0) )
        & k1_xboole_0 != k1_xboole_0 )
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f4289])).

fof(f4289,plain,(
    ! [X0] :
      ( ? [X9] :
          ( ! [X10] :
              ( r1_tarski(X9,X10)
              | ~ r2_hidden(X10,X0) )
          & r2_hidden(X9,X0) )
      | k1_xboole_0 = X0
      | ? [X1,X2] :
          ( ! [X5] :
              ( ? [X6] :
                  ( ~ r1_tarski(X5,X6)
                  & r2_hidden(X6,k2_xboole_0(X2,k1_tarski(X1))) )
              | ~ r2_hidden(X5,k2_xboole_0(X2,k1_tarski(X1))) )
          & k1_xboole_0 != k2_xboole_0(X2,k1_tarski(X1))
          & ( ? [X3] :
                ( ! [X4] :
                    ( r1_tarski(X3,X4)
                    | ~ r2_hidden(X4,X2) )
                & r2_hidden(X3,X2) )
            | k1_xboole_0 = X2 )
          & r1_tarski(X2,X0)
          & r2_hidden(X1,X0) )
      | ( ! [X7] :
            ( ? [X8] :
                ( ~ r1_tarski(X7,X8)
                & r2_hidden(X8,k1_xboole_0) )
            | ~ r2_hidden(X7,k1_xboole_0) )
        & k1_xboole_0 != k1_xboole_0 )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f3067])).

fof(f3067,plain,(
    ! [X0] :
      ( ( ! [X1,X2] :
            ( ( ~ ( ! [X3] :
                      ~ ( ! [X4] :
                            ( r2_hidden(X4,X2)
                           => r1_tarski(X3,X4) )
                        & r2_hidden(X3,X2) )
                  & k1_xboole_0 != X2 )
              & r1_tarski(X2,X0)
              & r2_hidden(X1,X0) )
           => ~ ( ! [X5] :
                    ~ ( ! [X6] :
                          ( r2_hidden(X6,k2_xboole_0(X2,k1_tarski(X1)))
                         => r1_tarski(X5,X6) )
                      & r2_hidden(X5,k2_xboole_0(X2,k1_tarski(X1))) )
                & k1_xboole_0 != k2_xboole_0(X2,k1_tarski(X1)) ) )
        & ~ ( ! [X7] :
                ~ ( ! [X8] :
                      ( r2_hidden(X8,k1_xboole_0)
                     => r1_tarski(X7,X8) )
                  & r2_hidden(X7,k1_xboole_0) )
            & k1_xboole_0 != k1_xboole_0 )
        & v1_finset_1(X0) )
     => ~ ( ! [X9] :
              ~ ( ! [X10] :
                    ( r2_hidden(X10,X0)
                   => r1_tarski(X9,X10) )
                & r2_hidden(X9,X0) )
          & k1_xboole_0 != X0 ) ) ),
    inference(rectify,[],[f1737])).

fof(f1737,axiom,(
    ! [X0] :
      ( ( ! [X3,X4] :
            ( ( ~ ( ! [X5] :
                      ~ ( ! [X6] :
                            ( r2_hidden(X6,X4)
                           => r1_tarski(X5,X6) )
                        & r2_hidden(X5,X4) )
                  & k1_xboole_0 != X4 )
              & r1_tarski(X4,X0)
              & r2_hidden(X3,X0) )
           => ~ ( ! [X7] :
                    ~ ( ! [X8] :
                          ( r2_hidden(X8,k2_xboole_0(X4,k1_tarski(X3)))
                         => r1_tarski(X7,X8) )
                      & r2_hidden(X7,k2_xboole_0(X4,k1_tarski(X3))) )
                & k1_xboole_0 != k2_xboole_0(X4,k1_tarski(X3)) ) )
        & ~ ( ! [X1] :
                ~ ( ! [X2] :
                      ( r2_hidden(X2,k1_xboole_0)
                     => r1_tarski(X1,X2) )
                  & r2_hidden(X1,k1_xboole_0) )
            & k1_xboole_0 != k1_xboole_0 )
        & v1_finset_1(X0) )
     => ~ ( ! [X9] :
              ~ ( ! [X10] :
                    ( r2_hidden(X10,X0)
                   => r1_tarski(X9,X10) )
                & r2_hidden(X9,X0) )
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s2_finset_1__e6_53__finset_1)).

fof(f7023,plain,
    ( spl384_48
    | spl384_49 ),
    inference(avatar_split_clause,[],[f6242,f7016,f7012])).

fof(f7016,plain,
    ( spl384_49
  <=> ! [X5,X0] :
        ( ~ v1_finset_1(X0)
        | sP316(sK315(X0),X0)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X5,sK319(X0,X5))
        | ~ r2_hidden(X5,k2_xboole_0(sK314(X0),k1_tarski(sK313(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_49])])).

fof(f6242,plain,(
    ! [X0,X7,X5] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X7,k1_xboole_0)
      | ~ r1_tarski(X7,sK317(X7))
      | ~ r2_hidden(X5,k2_xboole_0(sK314(X0),k1_tarski(sK313(X0))))
      | ~ r1_tarski(X5,sK319(X0,X5))
      | k1_xboole_0 = X0
      | sP316(sK315(X0),X0) ) ),
    inference(cnf_transformation,[],[f4290])).

fof(f7022,plain,
    ( spl384_46
    | spl384_50 ),
    inference(avatar_split_clause,[],[f6243,f7020,f7005])).

fof(f7005,plain,
    ( spl384_46
  <=> ! [X7] :
        ( ~ r2_hidden(X7,k1_xboole_0)
        | r2_hidden(sK317(X7),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_46])])).

fof(f6243,plain,(
    ! [X0,X7,X5] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X7,k1_xboole_0)
      | r2_hidden(sK317(X7),k1_xboole_0)
      | ~ r2_hidden(X5,k2_xboole_0(sK314(X0),k1_tarski(sK313(X0))))
      | r2_hidden(sK319(X0,X5),k2_xboole_0(sK314(X0),k1_tarski(sK313(X0))))
      | k1_xboole_0 = X0
      | sP316(sK315(X0),X0) ) ),
    inference(cnf_transformation,[],[f4290])).

fof(f7018,plain,
    ( spl384_46
    | spl384_49 ),
    inference(avatar_split_clause,[],[f6244,f7016,f7005])).

fof(f6244,plain,(
    ! [X0,X7,X5] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X7,k1_xboole_0)
      | r2_hidden(sK317(X7),k1_xboole_0)
      | ~ r2_hidden(X5,k2_xboole_0(sK314(X0),k1_tarski(sK313(X0))))
      | ~ r1_tarski(X5,sK319(X0,X5))
      | k1_xboole_0 = X0
      | sP316(sK315(X0),X0) ) ),
    inference(cnf_transformation,[],[f4290])).

fof(f7014,plain,
    ( spl384_48
    | spl384_47 ),
    inference(avatar_split_clause,[],[f6247,f7008,f7012])).

fof(f7008,plain,
    ( spl384_47
  <=> ! [X0] :
        ( ~ v1_finset_1(X0)
        | sP316(sK315(X0),X0)
        | k1_xboole_0 = X0
        | r2_hidden(sK318(X0),sK314(X0))
        | k1_xboole_0 = sK314(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_47])])).

fof(f6247,plain,(
    ! [X0,X7] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X7,k1_xboole_0)
      | ~ r1_tarski(X7,sK317(X7))
      | k1_xboole_0 = sK314(X0)
      | r2_hidden(sK318(X0),sK314(X0))
      | k1_xboole_0 = X0
      | sP316(sK315(X0),X0) ) ),
    inference(cnf_transformation,[],[f4290])).

fof(f7010,plain,
    ( spl384_46
    | spl384_47 ),
    inference(avatar_split_clause,[],[f6248,f7008,f7005])).

fof(f6248,plain,(
    ! [X0,X7] :
      ( ~ v1_finset_1(X0)
      | ~ r2_hidden(X7,k1_xboole_0)
      | r2_hidden(sK317(X7),k1_xboole_0)
      | k1_xboole_0 = sK314(X0)
      | r2_hidden(sK318(X0),sK314(X0))
      | k1_xboole_0 = X0
      | sP316(sK315(X0),X0) ) ),
    inference(cnf_transformation,[],[f4290])).

fof(f7003,plain,(
    ~ spl384_45 ),
    inference(avatar_split_clause,[],[f6199,f7000])).

fof(f7000,plain,
    ( spl384_45
  <=> v1_xboole_0(sK306) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_45])])).

fof(f6199,plain,(
    ~ v1_xboole_0(sK306) ),
    inference(cnf_transformation,[],[f1729])).

fof(f1729,axiom,(
    ? [X0] :
      ( v1_finset_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_finset_1)).

fof(f6998,plain,(
    spl384_44 ),
    inference(avatar_split_clause,[],[f6200,f6995])).

fof(f6995,plain,
    ( spl384_44
  <=> v1_finset_1(sK306) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_44])])).

fof(f6200,plain,(
    v1_finset_1(sK306) ),
    inference(cnf_transformation,[],[f1729])).

fof(f6993,plain,(
    ~ spl384_43 ),
    inference(avatar_split_clause,[],[f6195,f6990])).

fof(f6990,plain,
    ( spl384_43
  <=> v1_xboole_0(sK305) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_43])])).

fof(f6195,plain,(
    ~ v1_xboole_0(sK305) ),
    inference(cnf_transformation,[],[f1732])).

fof(f1732,axiom,(
    ? [X0] :
      ( v1_finset_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_finset_1)).

fof(f6988,plain,(
    spl384_42 ),
    inference(avatar_split_clause,[],[f6196,f6985])).

fof(f6985,plain,
    ( spl384_42
  <=> v1_relat_1(sK305) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_42])])).

fof(f6196,plain,(
    v1_relat_1(sK305) ),
    inference(cnf_transformation,[],[f1732])).

fof(f6983,plain,(
    spl384_41 ),
    inference(avatar_split_clause,[],[f6197,f6980])).

fof(f6980,plain,
    ( spl384_41
  <=> v1_funct_1(sK305) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_41])])).

fof(f6197,plain,(
    v1_funct_1(sK305) ),
    inference(cnf_transformation,[],[f1732])).

fof(f6978,plain,(
    spl384_40 ),
    inference(avatar_split_clause,[],[f6198,f6975])).

fof(f6975,plain,
    ( spl384_40
  <=> v1_finset_1(sK305) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_40])])).

fof(f6198,plain,(
    v1_finset_1(sK305) ),
    inference(cnf_transformation,[],[f1732])).

fof(f6973,plain,(
    spl384_39 ),
    inference(avatar_split_clause,[],[f6169,f6970])).

fof(f6970,plain,
    ( spl384_39
  <=> v3_ordinal1(sK296) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_39])])).

fof(f6169,plain,(
    v3_ordinal1(sK296) ),
    inference(cnf_transformation,[],[f1080])).

fof(f1080,axiom,(
    ? [X0] : v3_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_ordinal1)).

fof(f6922,plain,(
    spl384_38 ),
    inference(avatar_split_clause,[],[f6000,f6919])).

fof(f6919,plain,
    ( spl384_38
  <=> v1_relat_1(sK266) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_38])])).

fof(f6000,plain,(
    v1_relat_1(sK266) ),
    inference(cnf_transformation,[],[f931])).

fof(f931,axiom,(
    ? [X0] :
      ( v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_funct_1)).

fof(f6917,plain,(
    spl384_37 ),
    inference(avatar_split_clause,[],[f6001,f6914])).

fof(f6914,plain,
    ( spl384_37
  <=> v1_funct_1(sK266) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_37])])).

fof(f6001,plain,(
    v1_funct_1(sK266) ),
    inference(cnf_transformation,[],[f931])).

fof(f6912,plain,(
    spl384_36 ),
    inference(avatar_split_clause,[],[f6002,f6909])).

fof(f6909,plain,
    ( spl384_36
  <=> v2_funct_1(sK266) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_36])])).

fof(f6002,plain,(
    v2_funct_1(sK266) ),
    inference(cnf_transformation,[],[f931])).

fof(f6883,plain,(
    spl384_35 ),
    inference(avatar_split_clause,[],[f5614,f6880])).

fof(f6880,plain,
    ( spl384_35
  <=> l1_pre_topc(sK200) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_35])])).

fof(f5614,plain,(
    l1_pre_topc(sK200) ),
    inference(cnf_transformation,[],[f1788])).

fof(f1788,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_l1_pre_topc)).

fof(f6878,plain,(
    spl384_34 ),
    inference(avatar_split_clause,[],[f5613,f6875])).

fof(f5613,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f873])).

fof(f873,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f6866,plain,(
    spl384_33 ),
    inference(avatar_split_clause,[],[f5482,f6863])).

fof(f5482,plain,(
    v1_xboole_0(k1_wellord2(k1_xboole_0)) ),
    inference(cnf_transformation,[],[f1429])).

fof(f1429,axiom,
    ( v1_xboole_0(k1_wellord2(k1_xboole_0))
    & v1_relat_1(k1_wellord2(k1_xboole_0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_wellord2)).

fof(f6857,plain,(
    spl384_32 ),
    inference(avatar_split_clause,[],[f5398,f6854])).

fof(f6854,plain,
    ( spl384_32
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_32])])).

fof(f5398,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f861])).

fof(f861,axiom,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

fof(f6834,plain,(
    spl384_31 ),
    inference(avatar_split_clause,[],[f6512,f6831])).

fof(f6831,plain,
    ( spl384_31
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_31])])).

fof(f6512,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f5342])).

fof(f5342,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f3629])).

fof(f3629,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f132,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f6810,plain,(
    spl384_30 ),
    inference(avatar_split_clause,[],[f5194,f6807])).

fof(f6807,plain,
    ( spl384_30
  <=> v1_relat_1(sK154) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_30])])).

fof(f5194,plain,(
    v1_relat_1(sK154) ),
    inference(cnf_transformation,[],[f930])).

fof(f930,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_1)).

fof(f6805,plain,(
    spl384_29 ),
    inference(avatar_split_clause,[],[f5195,f6802])).

fof(f6802,plain,
    ( spl384_29
  <=> v1_funct_1(sK154) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_29])])).

fof(f5195,plain,(
    v1_funct_1(sK154) ),
    inference(cnf_transformation,[],[f930])).

fof(f6800,plain,(
    spl384_28 ),
    inference(avatar_split_clause,[],[f5179,f6797])).

fof(f6797,plain,
    ( spl384_28
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_28])])).

fof(f5179,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f856,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f6795,plain,(
    spl384_27 ),
    inference(avatar_split_clause,[],[f5180,f6792])).

fof(f6792,plain,
    ( spl384_27
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_27])])).

fof(f5180,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f6784,plain,(
    spl384_26 ),
    inference(avatar_split_clause,[],[f4970,f6781])).

fof(f4970,plain,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f858])).

fof(f858,axiom,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

fof(f6777,plain,(
    spl384_25 ),
    inference(avatar_split_clause,[],[f4942,f6774])).

fof(f6774,plain,
    ( spl384_25
  <=> l3_lattices(sK82) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_25])])).

fof(f4942,plain,(
    l3_lattices(sK82) ),
    inference(cnf_transformation,[],[f2683])).

fof(f2683,axiom,(
    ? [X0] :
      ( v3_lattices(X0)
      & ~ v2_struct_0(X0)
      & l3_lattices(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc6_lattices)).

fof(f6772,plain,(
    ~ spl384_24 ),
    inference(avatar_split_clause,[],[f4943,f6769])).

fof(f6769,plain,
    ( spl384_24
  <=> v2_struct_0(sK82) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_24])])).

fof(f4943,plain,(
    ~ v2_struct_0(sK82) ),
    inference(cnf_transformation,[],[f2683])).

fof(f6767,plain,(
    spl384_23 ),
    inference(avatar_split_clause,[],[f4944,f6764])).

fof(f6764,plain,
    ( spl384_23
  <=> v3_lattices(sK82) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_23])])).

fof(f4944,plain,(
    v3_lattices(sK82) ),
    inference(cnf_transformation,[],[f2683])).

fof(f6762,plain,(
    spl384_22 ),
    inference(avatar_split_clause,[],[f4938,f6759])).

fof(f6759,plain,
    ( spl384_22
  <=> l3_lattices(sK81) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_22])])).

fof(f4938,plain,(
    l3_lattices(sK81) ),
    inference(cnf_transformation,[],[f2684])).

fof(f2684,axiom,(
    ? [X0] :
      ( v10_lattices(X0)
      & v3_lattices(X0)
      & ~ v2_struct_0(X0)
      & l3_lattices(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc9_lattices)).

fof(f6757,plain,(
    ~ spl384_21 ),
    inference(avatar_split_clause,[],[f4939,f6754])).

fof(f6754,plain,
    ( spl384_21
  <=> v2_struct_0(sK81) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_21])])).

fof(f4939,plain,(
    ~ v2_struct_0(sK81) ),
    inference(cnf_transformation,[],[f2684])).

fof(f6752,plain,(
    spl384_20 ),
    inference(avatar_split_clause,[],[f4940,f6749])).

fof(f6749,plain,
    ( spl384_20
  <=> v3_lattices(sK81) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_20])])).

fof(f4940,plain,(
    v3_lattices(sK81) ),
    inference(cnf_transformation,[],[f2684])).

fof(f6747,plain,(
    spl384_19 ),
    inference(avatar_split_clause,[],[f4941,f6744])).

fof(f6744,plain,
    ( spl384_19
  <=> v10_lattices(sK81) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_19])])).

fof(f4941,plain,(
    v10_lattices(sK81) ),
    inference(cnf_transformation,[],[f2684])).

fof(f6742,plain,(
    spl384_18 ),
    inference(avatar_split_clause,[],[f4936,f6739])).

fof(f6739,plain,
    ( spl384_18
  <=> l3_lattices(sK80) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_18])])).

fof(f4936,plain,(
    l3_lattices(sK80) ),
    inference(cnf_transformation,[],[f2681])).

fof(f2681,axiom,(
    ? [X0] :
      ( v3_lattices(X0)
      & l3_lattices(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_lattices)).

fof(f6737,plain,(
    spl384_17 ),
    inference(avatar_split_clause,[],[f4937,f6734])).

fof(f6734,plain,
    ( spl384_17
  <=> v3_lattices(sK80) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_17])])).

fof(f4937,plain,(
    v3_lattices(sK80) ),
    inference(cnf_transformation,[],[f2681])).

fof(f6732,plain,(
    ~ spl384_16 ),
    inference(avatar_split_clause,[],[f4908,f6729])).

fof(f6729,plain,
    ( spl384_16
  <=> v1_xboole_0(sK75) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_16])])).

fof(f4908,plain,(
    ~ v1_xboole_0(sK75) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_xboole_0)).

fof(f6727,plain,(
    spl384_15 ),
    inference(avatar_split_clause,[],[f4907,f6724])).

fof(f4907,plain,(
    v1_xboole_0(sK74) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f6722,plain,(
    ~ spl384_14 ),
    inference(avatar_split_clause,[],[f4905,f6719])).

fof(f6719,plain,
    ( spl384_14
  <=> v1_xboole_0(sK73) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_14])])).

fof(f4905,plain,(
    ~ v1_xboole_0(sK73) ),
    inference(cnf_transformation,[],[f702])).

fof(f702,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relat_1)).

fof(f6717,plain,(
    spl384_13 ),
    inference(avatar_split_clause,[],[f4906,f6714])).

fof(f6714,plain,
    ( spl384_13
  <=> v1_relat_1(sK73) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_13])])).

fof(f4906,plain,(
    v1_relat_1(sK73) ),
    inference(cnf_transformation,[],[f702])).

fof(f6711,plain,(
    spl384_12 ),
    inference(avatar_split_clause,[],[f4857,f6708])).

fof(f6708,plain,
    ( spl384_12
  <=> l1_orders_2(sK65) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_12])])).

fof(f4857,plain,(
    l1_orders_2(sK65) ),
    inference(cnf_transformation,[],[f1931])).

fof(f1931,axiom,(
    ? [X0] :
      ( v1_orders_2(X0)
      & l1_orders_2(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_orders_2)).

fof(f6706,plain,(
    spl384_11 ),
    inference(avatar_split_clause,[],[f4858,f6703])).

fof(f6703,plain,
    ( spl384_11
  <=> v1_orders_2(sK65) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_11])])).

fof(f4858,plain,(
    v1_orders_2(sK65) ),
    inference(cnf_transformation,[],[f1931])).

fof(f6701,plain,(
    spl384_10 ),
    inference(avatar_split_clause,[],[f4854,f6698])).

fof(f6698,plain,
    ( spl384_10
  <=> l1_orders_2(sK64) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_10])])).

fof(f4854,plain,(
    l1_orders_2(sK64) ),
    inference(cnf_transformation,[],[f2895])).

fof(f2895,axiom,(
    ? [X0] :
      ( v1_orders_2(X0)
      & v2_struct_0(X0)
      & l1_orders_2(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_orders_2)).

fof(f6696,plain,(
    spl384_9 ),
    inference(avatar_split_clause,[],[f4855,f6693])).

fof(f6693,plain,
    ( spl384_9
  <=> v2_struct_0(sK64) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_9])])).

fof(f4855,plain,(
    v2_struct_0(sK64) ),
    inference(cnf_transformation,[],[f2895])).

fof(f6691,plain,(
    spl384_8 ),
    inference(avatar_split_clause,[],[f4856,f6688])).

fof(f6688,plain,
    ( spl384_8
  <=> v1_orders_2(sK64) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_8])])).

fof(f4856,plain,(
    v1_orders_2(sK64) ),
    inference(cnf_transformation,[],[f2895])).

fof(f6686,plain,(
    spl384_7 ),
    inference(avatar_split_clause,[],[f4853,f6683])).

fof(f6683,plain,
    ( spl384_7
  <=> l3_lattices(sK63) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_7])])).

fof(f4853,plain,(
    l3_lattices(sK63) ),
    inference(cnf_transformation,[],[f2051])).

fof(f2051,axiom,(
    ? [X0] : l3_lattices(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_l3_lattices)).

fof(f6681,plain,(
    spl384_6 ),
    inference(avatar_split_clause,[],[f4831,f6678])).

fof(f4831,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f6676,plain,(
    spl384_5 ),
    inference(avatar_split_clause,[],[f4808,f6673])).

fof(f4808,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f376,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f6649,plain,(
    spl384_4 ),
    inference(avatar_split_clause,[],[f4396,f6646])).

fof(f6646,plain,
    ( spl384_4
  <=> l1_orders_2(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl384_4])])).

fof(f4396,plain,(
    l1_orders_2(sK16) ),
    inference(cnf_transformation,[],[f1906])).

fof(f1906,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_l1_orders_2)).

fof(f6644,plain,(
    ~ spl384_3 ),
    inference(avatar_split_clause,[],[f4330,f6641])).

fof(f4330,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3071])).

fof(f6639,plain,(
    spl384_2 ),
    inference(avatar_split_clause,[],[f4331,f6636])).

fof(f4331,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3071])).

fof(f6634,plain,(
    ~ spl384_1 ),
    inference(avatar_split_clause,[],[f4332,f6631])).

fof(f4332,plain,(
    ~ v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f3071])).
%------------------------------------------------------------------------------
