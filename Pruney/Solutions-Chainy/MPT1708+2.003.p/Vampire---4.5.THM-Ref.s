%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 513 expanded)
%              Number of leaves         :   19 ( 103 expanded)
%              Depth                    :   20
%              Number of atoms          :  649 (4170 expanded)
%              Number of equality atoms :   25 ( 514 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f84,f95,f124,f132,f141,f162,f222,f251,f253,f258,f263])).

fof(f263,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f261,f68])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f67,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    | ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) ) )
                  & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X5] :
                            ( X3 = X5
                            & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( ~ r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                     => ( ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X2)) )
                        & ? [X4] :
                            ( X3 = X4
                            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))
                   => ( ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) )
                      & ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).

fof(f67,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f28,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f28,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f261,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f260,f32])).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f260,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f259,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f259,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f90,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f90,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_6
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f258,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f256,f66])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f65,f31])).

fof(f65,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f25,f33])).

% (27986)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f25,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f256,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f255,f32])).

fof(f255,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f254,f24])).

fof(f24,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f254,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f73,f34])).

fof(f73,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_3
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f253,plain,
    ( spl5_5
    | ~ spl5_8
    | ~ spl5_9
    | spl5_10
    | ~ spl5_11
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | spl5_5
    | ~ spl5_8
    | ~ spl5_9
    | spl5_10
    | ~ spl5_11
    | spl5_13 ),
    inference(subsumption_resolution,[],[f249,f83])).

fof(f83,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl5_5
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f249,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl5_8
    | ~ spl5_9
    | spl5_10
    | ~ spl5_11
    | spl5_13 ),
    inference(resolution,[],[f246,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f246,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_8
    | ~ spl5_9
    | spl5_10
    | ~ spl5_11
    | spl5_13 ),
    inference(subsumption_resolution,[],[f177,f245])).

fof(f245,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_8
    | ~ spl5_9
    | spl5_10
    | spl5_13 ),
    inference(subsumption_resolution,[],[f244,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f244,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK0)
    | ~ spl5_8
    | ~ spl5_9
    | spl5_10
    | spl5_13 ),
    inference(subsumption_resolution,[],[f243,f110])).

fof(f110,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl5_8
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f243,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9
    | spl5_10
    | spl5_13 ),
    inference(subsumption_resolution,[],[f242,f114])).

fof(f114,plain,
    ( v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_9
  <=> v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f242,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_10
    | spl5_13 ),
    inference(subsumption_resolution,[],[f241,f118])).

fof(f118,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_10
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f241,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f240,f26])).

fof(f26,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f240,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f239,f25])).

fof(f239,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f238,f24])).

fof(f238,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f237,f28])).

fof(f237,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f236,f27])).

fof(f236,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f223,f31])).

fof(f223,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0)
    | spl5_13 ),
    inference(superposition,[],[f187,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f36])).

% (27980)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(X3)
      | ~ v1_pre_topc(X3)
      | ~ m1_pre_topc(X3,X0)
      | u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f187,plain,
    ( ~ v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl5_13
  <=> v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f177,plain,
    ( r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_11 ),
    inference(resolution,[],[f123,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f123,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_11
  <=> m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f251,plain,
    ( spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | spl5_10
    | ~ spl5_11
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | spl5_10
    | ~ spl5_11
    | spl5_13 ),
    inference(subsumption_resolution,[],[f248,f94])).

fof(f94,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_7
  <=> r2_hidden(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f248,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl5_8
    | ~ spl5_9
    | spl5_10
    | ~ spl5_11
    | spl5_13 ),
    inference(resolution,[],[f246,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f222,plain,
    ( ~ spl5_8
    | spl5_10
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl5_8
    | spl5_10
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f220,f164])).

fof(f164,plain,
    ( l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f163,f31])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_8 ),
    inference(resolution,[],[f110,f33])).

fof(f220,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | spl5_10
    | ~ spl5_13 ),
    inference(resolution,[],[f197,f32])).

fof(f197,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl5_10
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f195,f118])).

fof(f195,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_13 ),
    inference(resolution,[],[f188,f34])).

fof(f188,plain,
    ( v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f186])).

fof(f162,plain,(
    ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f160,f29])).

fof(f160,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f159,f25])).

fof(f159,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f158,f24])).

fof(f158,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f157,f28])).

fof(f157,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f156,f27])).

fof(f156,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f155,f31])).

fof(f155,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(resolution,[],[f119,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f119,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f141,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl5_8 ),
    inference(subsumption_resolution,[],[f139,f29])).

fof(f139,plain,
    ( v2_struct_0(sK0)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f138,f25])).

fof(f138,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f137,f24])).

fof(f137,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f136,f28])).

fof(f136,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f135,f27])).

fof(f135,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(subsumption_resolution,[],[f134,f31])).

fof(f134,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_8 ),
    inference(resolution,[],[f111,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f111,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f132,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl5_9 ),
    inference(subsumption_resolution,[],[f130,f29])).

fof(f130,plain,
    ( v2_struct_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f129,f25])).

fof(f129,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f128,f24])).

fof(f128,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f127,f28])).

fof(f127,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f126,f27])).

fof(f126,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_9 ),
    inference(subsumption_resolution,[],[f125,f31])).

fof(f125,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl5_9 ),
    inference(resolution,[],[f115,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f115,plain,
    ( ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f124,plain,
    ( ~ spl5_8
    | ~ spl5_9
    | spl5_10
    | spl5_11 ),
    inference(avatar_split_clause,[],[f107,f121,f117,f113,f109])).

fof(f107,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f106,f29])).

fof(f106,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f105,f26])).

fof(f105,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f104,f25])).

fof(f104,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f103,f24])).

fof(f103,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f102,f28])).

fof(f102,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f101,f27])).

fof(f101,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f98,f31])).

fof(f98,plain,
    ( m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f23,f52])).

fof(f23,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f95,plain,
    ( spl5_6
    | ~ spl5_7
    | spl5_2 ),
    inference(avatar_split_clause,[],[f86,f61,f92,f88])).

fof(f61,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f86,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | spl5_2 ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f84,plain,
    ( spl5_3
    | ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f70,f57,f81,f72])).

fof(f57,plain,
    ( spl5_1
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f70,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | spl5_1 ),
    inference(resolution,[],[f59,f39])).

fof(f59,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f64,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f51,f61,f57])).

fof(f51,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4] :
      ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | sK3 != X5
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:03:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (27983)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.42  % (27978)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (27974)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (27988)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  % (27974)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f264,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f64,f84,f95,f124,f132,f141,f162,f222,f251,f253,f258,f263])).
% 0.21/0.46  fof(f263,plain,(
% 0.21/0.46    ~spl5_6),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f262])).
% 0.21/0.46  fof(f262,plain,(
% 0.21/0.46    $false | ~spl5_6),
% 0.21/0.46    inference(subsumption_resolution,[],[f261,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    l1_pre_topc(sK1)),
% 0.21/0.46    inference(subsumption_resolution,[],[f67,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    l1_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) | ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X5] : (X3 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))))))),
% 0.21/0.46    inference(rectify,[],[f9])).
% 0.21/0.47  fof(f9,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f8])).
% 0.21/0.47  fof(f8,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k2_tsep_1(X0,X1,X2))) => (? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X2))) & ? [X4] : (X3 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 0.21/0.47    inference(resolution,[],[f28,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    m1_pre_topc(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f261,plain,(
% 0.21/0.47    ~l1_pre_topc(sK1) | ~spl5_6),
% 0.21/0.47    inference(resolution,[],[f260,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.47  fof(f260,plain,(
% 0.21/0.47    ~l1_struct_0(sK1) | ~spl5_6),
% 0.21/0.47    inference(subsumption_resolution,[],[f259,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ~v2_struct_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f259,plain,(
% 0.21/0.47    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl5_6),
% 0.21/0.47    inference(resolution,[],[f90,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    v1_xboole_0(u1_struct_0(sK1)) | ~spl5_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f88])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl5_6 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.47  fof(f258,plain,(
% 0.21/0.47    ~spl5_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f257])).
% 0.21/0.47  fof(f257,plain,(
% 0.21/0.47    $false | ~spl5_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f256,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    l1_pre_topc(sK2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f65,f31])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.21/0.47    inference(resolution,[],[f25,f33])).
% 0.21/0.47  % (27986)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    m1_pre_topc(sK2,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f256,plain,(
% 0.21/0.47    ~l1_pre_topc(sK2) | ~spl5_3),
% 0.21/0.47    inference(resolution,[],[f255,f32])).
% 0.21/0.47  fof(f255,plain,(
% 0.21/0.47    ~l1_struct_0(sK2) | ~spl5_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f254,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ~v2_struct_0(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f254,plain,(
% 0.21/0.47    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl5_3),
% 0.21/0.47    inference(resolution,[],[f73,f34])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    v1_xboole_0(u1_struct_0(sK2)) | ~spl5_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl5_3 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.47  fof(f253,plain,(
% 0.21/0.47    spl5_5 | ~spl5_8 | ~spl5_9 | spl5_10 | ~spl5_11 | spl5_13),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f252])).
% 0.21/0.47  fof(f252,plain,(
% 0.21/0.47    $false | (spl5_5 | ~spl5_8 | ~spl5_9 | spl5_10 | ~spl5_11 | spl5_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f249,f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ~r2_hidden(sK3,u1_struct_0(sK2)) | spl5_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl5_5 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.47  fof(f249,plain,(
% 0.21/0.47    r2_hidden(sK3,u1_struct_0(sK2)) | (~spl5_8 | ~spl5_9 | spl5_10 | ~spl5_11 | spl5_13)),
% 0.21/0.47    inference(resolution,[],[f246,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.47  fof(f246,plain,(
% 0.21/0.47    r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (~spl5_8 | ~spl5_9 | spl5_10 | ~spl5_11 | spl5_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f177,f245])).
% 0.21/0.47  fof(f245,plain,(
% 0.21/0.47    ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (~spl5_8 | ~spl5_9 | spl5_10 | spl5_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f244,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f244,plain,(
% 0.21/0.47    ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK0) | (~spl5_8 | ~spl5_9 | spl5_10 | spl5_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f243,f110])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | ~spl5_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f109])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    spl5_8 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.47  fof(f243,plain,(
% 0.21/0.47    ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | (~spl5_9 | spl5_10 | spl5_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f242,f114])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~spl5_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f113])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    spl5_9 <=> v1_pre_topc(k2_tsep_1(sK0,sK1,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.47  fof(f242,plain,(
% 0.21/0.47    ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | (spl5_10 | spl5_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f241,f118])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | spl5_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f117])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    spl5_10 <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.47  fof(f241,plain,(
% 0.21/0.47    ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_13),
% 0.21/0.47    inference(subsumption_resolution,[],[f240,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ~r1_tsep_1(sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f240,plain,(
% 0.21/0.47    ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | r1_tsep_1(sK1,sK2) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_13),
% 0.21/0.47    inference(subsumption_resolution,[],[f239,f25])).
% 0.21/0.47  fof(f239,plain,(
% 0.21/0.47    ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK1,sK2) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_13),
% 0.21/0.47    inference(subsumption_resolution,[],[f238,f24])).
% 0.21/0.47  fof(f238,plain,(
% 0.21/0.47    ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK1,sK2) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_13),
% 0.21/0.47    inference(subsumption_resolution,[],[f237,f28])).
% 0.21/0.47  fof(f237,plain,(
% 0.21/0.47    ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK1,sK2) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_13),
% 0.21/0.47    inference(subsumption_resolution,[],[f236,f27])).
% 0.21/0.47  fof(f236,plain,(
% 0.21/0.47    ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK1,sK2) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_13),
% 0.21/0.47    inference(subsumption_resolution,[],[f223,f31])).
% 0.21/0.47  fof(f223,plain,(
% 0.21/0.47    ~v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK1,sK2) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0) | spl5_13),
% 0.21/0.47    inference(superposition,[],[f187,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X1,X2) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f36])).
% 0.21/0.47  % (27980)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X1,X2) | v2_struct_0(X3) | ~v1_pre_topc(X3) | ~m1_pre_topc(X3,X0) | u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).
% 0.21/0.47  fof(f187,plain,(
% 0.21/0.47    ~v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | spl5_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f186])).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    spl5_13 <=> v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    r2_hidden(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v1_xboole_0(k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl5_11),
% 0.21/0.47    inference(resolution,[],[f123,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl5_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f121])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    spl5_11 <=> m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.47  fof(f251,plain,(
% 0.21/0.47    spl5_7 | ~spl5_8 | ~spl5_9 | spl5_10 | ~spl5_11 | spl5_13),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f250])).
% 0.21/0.47  fof(f250,plain,(
% 0.21/0.47    $false | (spl5_7 | ~spl5_8 | ~spl5_9 | spl5_10 | ~spl5_11 | spl5_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f248,f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    ~r2_hidden(sK3,u1_struct_0(sK1)) | spl5_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f92])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl5_7 <=> r2_hidden(sK3,u1_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.47  fof(f248,plain,(
% 0.21/0.47    r2_hidden(sK3,u1_struct_0(sK1)) | (~spl5_8 | ~spl5_9 | spl5_10 | ~spl5_11 | spl5_13)),
% 0.21/0.47    inference(resolution,[],[f246,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f222,plain,(
% 0.21/0.47    ~spl5_8 | spl5_10 | ~spl5_13),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f221])).
% 0.21/0.47  fof(f221,plain,(
% 0.21/0.47    $false | (~spl5_8 | spl5_10 | ~spl5_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f220,f164])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~spl5_8),
% 0.21/0.47    inference(subsumption_resolution,[],[f163,f31])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~spl5_8),
% 0.21/0.47    inference(resolution,[],[f110,f33])).
% 0.21/0.47  fof(f220,plain,(
% 0.21/0.47    ~l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | (spl5_10 | ~spl5_13)),
% 0.21/0.47    inference(resolution,[],[f197,f32])).
% 0.21/0.47  fof(f197,plain,(
% 0.21/0.47    ~l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | (spl5_10 | ~spl5_13)),
% 0.21/0.47    inference(subsumption_resolution,[],[f195,f118])).
% 0.21/0.47  fof(f195,plain,(
% 0.21/0.47    ~l1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl5_13),
% 0.21/0.47    inference(resolution,[],[f188,f34])).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    v1_xboole_0(u1_struct_0(k2_tsep_1(sK0,sK1,sK2))) | ~spl5_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f186])).
% 0.21/0.47  fof(f162,plain,(
% 0.21/0.47    ~spl5_10),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    $false | ~spl5_10),
% 0.21/0.47    inference(subsumption_resolution,[],[f160,f29])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    v2_struct_0(sK0) | ~spl5_10),
% 0.21/0.47    inference(subsumption_resolution,[],[f159,f25])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_10),
% 0.21/0.47    inference(subsumption_resolution,[],[f158,f24])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_10),
% 0.21/0.47    inference(subsumption_resolution,[],[f157,f28])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_10),
% 0.21/0.47    inference(subsumption_resolution,[],[f156,f27])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_10),
% 0.21/0.47    inference(subsumption_resolution,[],[f155,f31])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl5_10),
% 0.21/0.47    inference(resolution,[],[f119,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl5_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f117])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    spl5_8),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f140])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    $false | spl5_8),
% 0.21/0.47    inference(subsumption_resolution,[],[f139,f29])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    v2_struct_0(sK0) | spl5_8),
% 0.21/0.47    inference(subsumption_resolution,[],[f138,f25])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_8),
% 0.21/0.47    inference(subsumption_resolution,[],[f137,f24])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_8),
% 0.21/0.47    inference(subsumption_resolution,[],[f136,f28])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_8),
% 0.21/0.47    inference(subsumption_resolution,[],[f135,f27])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_8),
% 0.21/0.47    inference(subsumption_resolution,[],[f134,f31])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_8),
% 0.21/0.47    inference(resolution,[],[f111,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | spl5_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f109])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    spl5_9),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f131])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    $false | spl5_9),
% 0.21/0.47    inference(subsumption_resolution,[],[f130,f29])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    v2_struct_0(sK0) | spl5_9),
% 0.21/0.47    inference(subsumption_resolution,[],[f129,f25])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_9),
% 0.21/0.47    inference(subsumption_resolution,[],[f128,f24])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_9),
% 0.21/0.47    inference(subsumption_resolution,[],[f127,f28])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_9),
% 0.21/0.47    inference(subsumption_resolution,[],[f126,f27])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_9),
% 0.21/0.47    inference(subsumption_resolution,[],[f125,f31])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | spl5_9),
% 0.21/0.47    inference(resolution,[],[f115,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | spl5_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f113])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ~spl5_8 | ~spl5_9 | spl5_10 | spl5_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f107,f121,f117,f113,f109])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f106,f29])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f105,f26])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | r1_tsep_1(sK1,sK2) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f104,f25])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK1,sK2) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f103,f24])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK1,sK2) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f102,f28])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK1,sK2) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f101,f27])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK1,sK2) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f98,f31])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    m1_subset_1(sK3,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK1,sK2) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | v2_struct_0(sK0)),
% 0.21/0.47    inference(superposition,[],[f23,f52])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    m1_subset_1(sK3,u1_struct_0(k2_tsep_1(sK0,sK1,sK2)))),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    spl5_6 | ~spl5_7 | spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f86,f61,f92,f88])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl5_2 <=> m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ~r2_hidden(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | spl5_2),
% 0.21/0.47    inference(resolution,[],[f63,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ~m1_subset_1(sK3,u1_struct_0(sK1)) | spl5_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl5_3 | ~spl5_5 | spl5_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f70,f57,f81,f72])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl5_1 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ~r2_hidden(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | spl5_1),
% 0.21/0.47    inference(resolution,[],[f59,f39])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ~m1_subset_1(sK3,u1_struct_0(sK2)) | spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f57])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ~spl5_1 | ~spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f51,f61,f57])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.47    inference(equality_resolution,[],[f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X4] : (~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X4) )),
% 0.21/0.47    inference(equality_resolution,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X4,X5] : (~m1_subset_1(X5,u1_struct_0(sK1)) | sK3 != X5 | ~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X4) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (27974)------------------------------
% 0.21/0.47  % (27974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (27974)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (27974)Memory used [KB]: 10618
% 0.21/0.47  % (27974)Time elapsed: 0.068 s
% 0.21/0.47  % (27974)------------------------------
% 0.21/0.47  % (27974)------------------------------
% 0.21/0.47  % (27969)Success in time 0.121 s
%------------------------------------------------------------------------------
