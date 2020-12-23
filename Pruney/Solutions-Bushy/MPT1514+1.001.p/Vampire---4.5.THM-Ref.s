%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1514+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:59 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 434 expanded)
%              Number of leaves         :   22 ( 132 expanded)
%              Depth                    :   44
%              Number of atoms          : 1138 (2228 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (8421)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f593,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f104,f146,f151,f156,f161,f173,f187,f202,f205,f210,f592])).

fof(f592,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_12
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f591])).

fof(f591,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_12
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f590,f186])).

fof(f186,plain,
    ( ~ r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl6_12
  <=> r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f590,plain,
    ( r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f588,f105])).

fof(f105,plain,
    ( ! [X10] : m1_subset_1(k15_lattice3(sK0,X10),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f85,f79])).

fof(f79,plain,
    ( l3_lattices(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl6_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f85,plain,
    ( ! [X10] :
        ( ~ l3_lattices(sK0)
        | m1_subset_1(k15_lattice3(sK0,X10),u1_struct_0(sK0)) )
    | spl6_1 ),
    inference(resolution,[],[f64,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f64,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f588,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(resolution,[],[f583,f115])).

fof(f115,plain,
    ( ! [X2] : r4_lattice3(sK0,k15_lattice3(sK0,X2),X2)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f114,f64])).

fof(f114,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | r4_lattice3(sK0,k15_lattice3(sK0,X2),X2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f113,f79])).

fof(f113,plain,
    ( ! [X2] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | r4_lattice3(sK0,k15_lattice3(sK0,X2),X2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f112,f74])).

fof(f74,plain,
    ( v4_lattice3(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_3
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f112,plain,
    ( ! [X2] :
        ( ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | r4_lattice3(sK0,k15_lattice3(sK0,X2),X2) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f107,f69])).

fof(f69,plain,
    ( v10_lattices(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f107,plain,
    ( ! [X2] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | r4_lattice3(sK0,k15_lattice3(sK0,X2),X2) )
    | spl6_1
    | ~ spl6_4 ),
    inference(resolution,[],[f105,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | r4_lattice3(X0,k15_lattice3(X0,X1),X1) ) ),
    inference(equality_resolution,[],[f51])).

% (8439)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r4_lattice3(X0,X2,X1)
      | k15_lattice3(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f583,plain,
    ( ! [X0] :
        ( ~ r4_lattice3(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,sK1) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f582,f64])).

fof(f582,plain,
    ( ! [X0] :
        ( ~ r4_lattice3(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,sK1)
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f581,f79])).

fof(f581,plain,
    ( ! [X0] :
        ( ~ r4_lattice3(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,sK1)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f580])).

fof(f580,plain,
    ( ! [X0] :
        ( ~ r4_lattice3(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,sK1)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r4_lattice3(sK0,X0,sK1) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(resolution,[],[f575,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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

fof(f575,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,X0,sK1),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,sK1) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f574,f116])).

fof(f116,plain,
    ( ! [X6,X7] :
        ( r2_hidden(sK5(sK0,X6,X7),X7)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r4_lattice3(sK0,X6,X7) )
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f83,f79])).

fof(f83,plain,
    ( ! [X6,X7] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r2_hidden(sK5(sK0,X6,X7),X7)
        | r4_lattice3(sK0,X6,X7) )
    | spl6_1 ),
    inference(resolution,[],[f64,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X2),X2)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f574,plain,
    ( ! [X0] :
        ( r4_lattice3(sK0,X0,sK1)
        | ~ r4_lattice3(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,X0,sK1),sK1)
        | ~ m1_subset_1(sK5(sK0,X0,sK1),u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(resolution,[],[f571,f30])).

fof(f30,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f12])).

% (8435)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).

fof(f571,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(sK5(sK0,X0,sK1)),X1)
        | r4_lattice3(sK0,X0,sK1)
        | ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f570,f64])).

fof(f570,plain,
    ( ! [X0,X1] :
        ( r4_lattice3(sK0,X0,sK1)
        | ~ r2_hidden(sK3(sK5(sK0,X0,sK1)),X1)
        | ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f569,f79])).

fof(f569,plain,
    ( ! [X0,X1] :
        ( r4_lattice3(sK0,X0,sK1)
        | ~ r2_hidden(sK3(sK5(sK0,X0,sK1)),X1)
        | ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f568])).

fof(f568,plain,
    ( ! [X0,X1] :
        ( r4_lattice3(sK0,X0,sK1)
        | ~ r2_hidden(sK3(sK5(sK0,X0,sK1)),X1)
        | ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r4_lattice3(sK0,X0,sK1) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(resolution,[],[f565,f53])).

fof(f565,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,X0,sK1),u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,sK1)
        | ~ r2_hidden(sK3(sK5(sK0,X0,sK1)),X1)
        | ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f564,f116])).

fof(f564,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,sK1)
        | ~ r2_hidden(sK3(sK5(sK0,X0,sK1)),X1)
        | ~ r4_lattice3(sK0,X0,X1)
        | ~ r2_hidden(sK5(sK0,X0,sK1),sK1)
        | ~ m1_subset_1(sK5(sK0,X0,sK1),u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(resolution,[],[f446,f28])).

fof(f28,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(X3),u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f446,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK3(sK5(sK0,X3,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r4_lattice3(sK0,X3,sK1)
        | ~ r2_hidden(sK3(sK5(sK0,X3,sK1)),X4)
        | ~ r4_lattice3(sK0,X3,X4) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f445])).

fof(f445,plain,
    ( ! [X4,X3] :
        ( r4_lattice3(sK0,X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK5(sK0,X3,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(sK3(sK5(sK0,X3,sK1)),X4)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X3,X4) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(resolution,[],[f432,f127])).

fof(f127,plain,
    ( ! [X4,X5,X3] :
        ( r1_lattices(sK0,X4,X3)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,X5)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X3,X5) )
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f82,f79])).

fof(f82,plain,
    ( ! [X4,X5,X3] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,X5)
        | r1_lattices(sK0,X4,X3)
        | ~ r4_lattice3(sK0,X3,X5) )
    | spl6_1 ),
    inference(resolution,[],[f64,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | r1_lattices(X0,X3,X1)
      | ~ r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f432,plain,
    ( ! [X0] :
        ( ~ r1_lattices(sK0,sK3(sK5(sK0,X0,sK1)),X0)
        | r4_lattice3(sK0,X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f431,f64])).

fof(f431,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,sK1)
        | ~ r1_lattices(sK0,sK3(sK5(sK0,X0,sK1)),X0)
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f430,f79])).

fof(f430,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,sK1)
        | ~ r1_lattices(sK0,sK3(sK5(sK0,X0,sK1)),X0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f429])).

fof(f429,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,sK1)
        | ~ r1_lattices(sK0,sK3(sK5(sK0,X0,sK1)),X0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r4_lattice3(sK0,X0,sK1) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(resolution,[],[f402,f53])).

fof(f402,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,X0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,sK1)
        | ~ r1_lattices(sK0,sK3(sK5(sK0,X0,sK1)),X0) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f401])).

fof(f401,plain,
    ( ! [X0] :
        ( ~ r1_lattices(sK0,sK3(sK5(sK0,X0,sK1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,sK1)
        | ~ m1_subset_1(sK5(sK0,X0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,sK1) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(resolution,[],[f329,f116])).

fof(f329,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(sK0,X0,X1),sK1)
        | ~ r1_lattices(sK0,sK3(sK5(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f325,f28])).

fof(f325,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3(sK5(sK0,X0,X1)),u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1)
        | ~ r1_lattices(sK0,sK3(sK5(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,X0,X1),sK1)
        | ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(resolution,[],[f293,f29])).

fof(f29,plain,(
    ! [X3] :
      ( r3_lattices(sK0,X3,sK3(X3))
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f293,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_lattices(sK0,sK5(sK0,X0,X2),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X2)
        | ~ r1_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f292,f64])).

fof(f292,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X2)
        | ~ r1_lattices(sK0,X1,X0)
        | ~ r3_lattices(sK0,sK5(sK0,X0,X2),X1)
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f291,f79])).

fof(f291,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X2)
        | ~ r1_lattices(sK0,X1,X0)
        | ~ r3_lattices(sK0,sK5(sK0,X0,X2),X1)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f290])).

fof(f290,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X2)
        | ~ r1_lattices(sK0,X1,X0)
        | ~ r3_lattices(sK0,sK5(sK0,X0,X2),X1)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r4_lattice3(sK0,X0,X2) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(resolution,[],[f257,f53])).

fof(f257,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(sK5(sK0,X5,X6),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r4_lattice3(sK0,X5,X6)
        | ~ r1_lattices(sK0,X4,X5)
        | ~ r3_lattices(sK0,sK5(sK0,X5,X6),X4) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f254])).

fof(f254,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_lattices(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r4_lattice3(sK0,X5,X6)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X5,X6),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK5(sK0,X5,X6),X4) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(resolution,[],[f244,f168])).

fof(f168,plain,
    ( ! [X14,X13] :
        ( r1_lattices(sK0,X13,X14)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X13,X14) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f167,f79])).

fof(f167,plain,
    ( ! [X14,X13] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | r1_lattices(sK0,X13,X14)
        | ~ r3_lattices(sK0,X13,X14) )
    | spl6_1
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f166,f136])).

fof(f136,plain,
    ( v9_lattices(sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_8
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f166,plain,
    ( ! [X14,X13] :
        ( ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | r1_lattices(sK0,X13,X14)
        | ~ r3_lattices(sK0,X13,X14) )
    | spl6_1
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f165,f140])).

fof(f140,plain,
    ( v8_lattices(sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl6_9
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f165,plain,
    ( ! [X14,X13] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | r1_lattices(sK0,X13,X14)
        | ~ r3_lattices(sK0,X13,X14) )
    | spl6_1
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f87,f144])).

fof(f144,plain,
    ( v6_lattices(sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_10
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f87,plain,
    ( ! [X14,X13] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | r1_lattices(sK0,X13,X14)
        | ~ r3_lattices(sK0,X13,X14) )
    | spl6_1 ),
    inference(resolution,[],[f64,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f244,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattices(sK0,sK5(sK0,X1,X2),X0)
        | ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X1,X2) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f243,f64])).

fof(f243,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattices(sK0,X0,X1)
        | ~ r1_lattices(sK0,sK5(sK0,X1,X2),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X1,X2)
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f242,f79])).

fof(f242,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattices(sK0,X0,X1)
        | ~ r1_lattices(sK0,sK5(sK0,X1,X2),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X1,X2)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f241])).

fof(f241,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattices(sK0,X0,X1)
        | ~ r1_lattices(sK0,sK5(sK0,X1,X2),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X1,X2)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r4_lattice3(sK0,X1,X2) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(resolution,[],[f213,f53])).

fof(f213,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X2,X0)
        | ~ r1_lattices(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X2,X0)
        | ~ r1_lattices(sK0,sK5(sK0,X0,X1),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(resolution,[],[f193,f117])).

fof(f117,plain,
    ( ! [X8,X9] :
        ( ~ r1_lattices(sK0,sK5(sK0,X8,X9),X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r4_lattice3(sK0,X8,X9) )
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f84,f79])).

fof(f84,plain,
    ( ! [X8,X9] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,sK5(sK0,X8,X9),X8)
        | r4_lattice3(sK0,X8,X9) )
    | spl6_1 ),
    inference(resolution,[],[f64,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f193,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattices(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X1,X2)
        | ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl6_13
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,X2)
        | ~ r1_lattices(sK0,X1,X2)
        | ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f210,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_15 ),
    inference(subsumption_resolution,[],[f208,f79])).

fof(f208,plain,
    ( ~ l3_lattices(sK0)
    | spl6_1
    | ~ spl6_2
    | spl6_15 ),
    inference(subsumption_resolution,[],[f207,f69])).

fof(f207,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_1
    | spl6_15 ),
    inference(subsumption_resolution,[],[f206,f64])).

fof(f206,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_15 ),
    inference(resolution,[],[f201,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f201,plain,
    ( ~ v5_lattices(sK0)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl6_15
  <=> v5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f205,plain,
    ( ~ spl6_4
    | spl6_14 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl6_4
    | spl6_14 ),
    inference(subsumption_resolution,[],[f203,f79])).

fof(f203,plain,
    ( ~ l3_lattices(sK0)
    | spl6_14 ),
    inference(resolution,[],[f197,f37])).

fof(f37,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f197,plain,
    ( ~ l2_lattices(sK0)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl6_14
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f202,plain,
    ( spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_1 ),
    inference(avatar_split_clause,[],[f81,f62,f199,f195,f192])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_lattices(sK0)
        | ~ l2_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X1)
        | ~ r1_lattices(sK0,X1,X2)
        | r1_lattices(sK0,X0,X2) )
    | spl6_1 ),
    inference(resolution,[],[f64,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X2,X3)
      | r1_lattices(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_lattices)).

fof(f187,plain,
    ( ~ spl6_12
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_11 ),
    inference(avatar_split_clause,[],[f179,f170,f77,f72,f67,f62,f184])).

fof(f170,plain,
    ( spl6_11
  <=> r1_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f179,plain,
    ( ~ r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_11 ),
    inference(subsumption_resolution,[],[f176,f105])).

fof(f176,plain,
    ( ~ r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_11 ),
    inference(resolution,[],[f172,f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f110,f64])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f109,f79])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f108,f74])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f106,f69])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl6_1
    | ~ spl6_4 ),
    inference(resolution,[],[f105,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | r1_lattices(X0,k15_lattice3(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f172,plain,
    ( ~ r1_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f170])).

fof(f173,plain,
    ( ~ spl6_11
    | spl6_1
    | ~ spl6_4
    | spl6_5
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f164,f132,f101,f77,f62,f170])).

fof(f101,plain,
    ( spl6_5
  <=> r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f132,plain,
    ( spl6_7
  <=> ! [X11,X12] :
        ( ~ m1_subset_1(X11,u1_struct_0(sK0))
        | r3_lattices(sK0,X11,X12)
        | ~ r1_lattices(sK0,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f164,plain,
    ( ~ r1_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    | spl6_1
    | ~ spl6_4
    | spl6_5
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f163,f105])).

fof(f163,plain,
    ( ~ r1_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_4
    | spl6_5
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f162,f105])).

fof(f162,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | spl6_5
    | ~ spl6_7 ),
    inference(resolution,[],[f133,f103])).

fof(f103,plain,
    ( ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f133,plain,
    ( ! [X12,X11] :
        ( r3_lattices(sK0,X11,X12)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0)) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f132])).

fof(f161,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_10 ),
    inference(subsumption_resolution,[],[f159,f79])).

fof(f159,plain,
    ( ~ l3_lattices(sK0)
    | spl6_1
    | ~ spl6_2
    | spl6_10 ),
    inference(subsumption_resolution,[],[f158,f69])).

fof(f158,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_1
    | spl6_10 ),
    inference(subsumption_resolution,[],[f157,f64])).

fof(f157,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_10 ),
    inference(resolution,[],[f145,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f145,plain,
    ( ~ v6_lattices(sK0)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f156,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_9 ),
    inference(subsumption_resolution,[],[f154,f79])).

fof(f154,plain,
    ( ~ l3_lattices(sK0)
    | spl6_1
    | ~ spl6_2
    | spl6_9 ),
    inference(subsumption_resolution,[],[f153,f69])).

fof(f153,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_1
    | spl6_9 ),
    inference(subsumption_resolution,[],[f152,f64])).

fof(f152,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_9 ),
    inference(resolution,[],[f141,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f141,plain,
    ( ~ v8_lattices(sK0)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f151,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_8 ),
    inference(subsumption_resolution,[],[f149,f79])).

fof(f149,plain,
    ( ~ l3_lattices(sK0)
    | spl6_1
    | ~ spl6_2
    | spl6_8 ),
    inference(subsumption_resolution,[],[f148,f69])).

fof(f148,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_1
    | spl6_8 ),
    inference(subsumption_resolution,[],[f147,f64])).

fof(f147,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl6_8 ),
    inference(resolution,[],[f137,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f137,plain,
    ( ~ v9_lattices(sK0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f146,plain,
    ( spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f130,f77,f62,f143,f139,f135,f132])).

fof(f130,plain,
    ( ! [X12,X11] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X11,X12)
        | r3_lattices(sK0,X11,X12) )
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f86,f79])).

fof(f86,plain,
    ( ! [X12,X11] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X11,X12)
        | r3_lattices(sK0,X11,X12) )
    | spl6_1 ),
    inference(resolution,[],[f64,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f104,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f31,f101])).

fof(f31,plain,(
    ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f80,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f35,f77])).

fof(f35,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f34,f72])).

fof(f34,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f33,f67])).

fof(f33,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f32,f62])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

%------------------------------------------------------------------------------
