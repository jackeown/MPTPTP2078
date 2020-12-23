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
% DateTime   : Thu Dec  3 13:23:29 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 255 expanded)
%              Number of leaves         :   30 ( 115 expanded)
%              Depth                    :    8
%              Number of atoms          :  373 (1041 expanded)
%              Number of equality atoms :   36 ( 129 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f208,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f95,f100,f106,f117,f130,f154,f160,f166,f177,f182,f205])).

fof(f205,plain,
    ( ~ spl3_20
    | spl3_11
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f187,f174,f114,f179])).

fof(f179,plain,
    ( spl3_20
  <=> r2_hidden(sK2(sK1,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f114,plain,
    ( spl3_11
  <=> r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f174,plain,
    ( spl3_19
  <=> r2_hidden(sK2(sK1,k1_tarski(k1_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f187,plain,
    ( ~ r2_hidden(sK2(sK1,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | spl3_11
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f116,f176,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f45,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f176,plain,
    ( r2_hidden(sK2(sK1,k1_tarski(k1_xboole_0)),sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f174])).

fof(f116,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f182,plain,
    ( spl3_20
    | spl3_18 ),
    inference(avatar_split_clause,[],[f171,f163,f179])).

fof(f163,plain,
    ( spl3_18
  <=> r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f171,plain,
    ( r2_hidden(sK2(sK1,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f165,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f165,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f163])).

fof(f177,plain,
    ( spl3_19
    | spl3_18 ),
    inference(avatar_split_clause,[],[f172,f163,f174])).

fof(f172,plain,
    ( r2_hidden(sK2(sK1,k1_tarski(k1_xboole_0)),sK1)
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f165,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f166,plain,
    ( ~ spl3_18
    | spl3_17 ),
    inference(avatar_split_clause,[],[f161,f157,f163])).

fof(f157,plain,
    ( spl3_17
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f161,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl3_17 ),
    inference(unit_resulting_resolution,[],[f159,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f159,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f157])).

fof(f160,plain,
    ( ~ spl3_17
    | spl3_1
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f155,f151,f57,f157])).

fof(f57,plain,
    ( spl3_1
  <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f151,plain,
    ( spl3_16
  <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f155,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | spl3_1
    | ~ spl3_16 ),
    inference(superposition,[],[f59,f153])).

fof(f153,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f151])).

fof(f59,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f154,plain,
    ( spl3_16
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f149,f127,f62,f151])).

fof(f62,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f127,plain,
    ( spl3_13
  <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f149,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f129,f109])).

fof(f109,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f64,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f64,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f129,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f130,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_6
    | ~ spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f124,f92,f87,f82,f72,f67,f62,f127])).

fof(f67,plain,
    ( spl3_3
  <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f72,plain,
    ( spl3_4
  <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f82,plain,
    ( spl3_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f87,plain,
    ( spl3_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f92,plain,
    ( spl3_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f124,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_6
    | ~ spl3_7
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f94,f89,f84,f74,f69,f64,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0))
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f42,f39,f39,f39,f39])).

fof(f39,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

fof(f69,plain,
    ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f74,plain,
    ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f84,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f89,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f94,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f117,plain,
    ( ~ spl3_11
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_6
    | ~ spl3_9
    | spl3_10 ),
    inference(avatar_split_clause,[],[f111,f103,f97,f82,f77,f72,f67,f62,f114])).

fof(f77,plain,
    ( spl3_5
  <=> v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f97,plain,
    ( spl3_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f103,plain,
    ( spl3_10
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f111,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_6
    | ~ spl3_9
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f99,f84,f105,f74,f69,f79,f64,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f40,f39,f39,f39,f39])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

fof(f79,plain,
    ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f105,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f99,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f106,plain,
    ( ~ spl3_10
    | ~ spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f101,f92,f87,f103])).

fof(f101,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ spl3_7
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f94,f89,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f100,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f38,f97])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f95,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f30,f92])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        & ~ v1_xboole_0(X1) )
   => ( sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(f90,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f31,f87])).

fof(f31,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f53,f77])).

fof(f53,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f33,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f52,f72])).

fof(f52,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f34,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f51,f67])).

fof(f51,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f35,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f50,f62])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f37,f57])).

fof(f37,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:12:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.43  % (778)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.44  % (783)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.44  % (775)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.45  % (781)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.45  % (775)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f208,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f95,f100,f106,f117,f130,f154,f160,f166,f177,f182,f205])).
% 0.19/0.45  fof(f205,plain,(
% 0.19/0.45    ~spl3_20 | spl3_11 | ~spl3_19),
% 0.19/0.45    inference(avatar_split_clause,[],[f187,f174,f114,f179])).
% 0.19/0.45  fof(f179,plain,(
% 0.19/0.45    spl3_20 <=> r2_hidden(sK2(sK1,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.19/0.45  fof(f114,plain,(
% 0.19/0.45    spl3_11 <=> r2_hidden(k1_xboole_0,sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.45  fof(f174,plain,(
% 0.19/0.45    spl3_19 <=> r2_hidden(sK2(sK1,k1_tarski(k1_xboole_0)),sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.19/0.45  fof(f187,plain,(
% 0.19/0.45    ~r2_hidden(sK2(sK1,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0)) | (spl3_11 | ~spl3_19)),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f116,f176,f108])).
% 0.19/0.45  fof(f108,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_tarski(X2)) | ~r2_hidden(X0,X1) | r2_hidden(X2,X1)) )),
% 0.19/0.45    inference(resolution,[],[f45,f46])).
% 0.19/0.45  fof(f46,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f22])).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.19/0.45    inference(ennf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.19/0.45  fof(f45,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f28])).
% 0.19/0.45  fof(f28,plain,(
% 0.19/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f27])).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.45    inference(ennf_transformation,[],[f12])).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.45    inference(rectify,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.19/0.45  fof(f176,plain,(
% 0.19/0.45    r2_hidden(sK2(sK1,k1_tarski(k1_xboole_0)),sK1) | ~spl3_19),
% 0.19/0.45    inference(avatar_component_clause,[],[f174])).
% 0.19/0.45  fof(f116,plain,(
% 0.19/0.45    ~r2_hidden(k1_xboole_0,sK1) | spl3_11),
% 0.19/0.45    inference(avatar_component_clause,[],[f114])).
% 0.19/0.45  fof(f182,plain,(
% 0.19/0.45    spl3_20 | spl3_18),
% 0.19/0.45    inference(avatar_split_clause,[],[f171,f163,f179])).
% 0.19/0.45  fof(f163,plain,(
% 0.19/0.45    spl3_18 <=> r1_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.19/0.45  fof(f171,plain,(
% 0.19/0.45    r2_hidden(sK2(sK1,k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0)) | spl3_18),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f165,f44])).
% 0.19/0.45  fof(f44,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f28])).
% 0.19/0.45  fof(f165,plain,(
% 0.19/0.45    ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) | spl3_18),
% 0.19/0.45    inference(avatar_component_clause,[],[f163])).
% 0.19/0.45  fof(f177,plain,(
% 0.19/0.45    spl3_19 | spl3_18),
% 0.19/0.45    inference(avatar_split_clause,[],[f172,f163,f174])).
% 0.19/0.45  fof(f172,plain,(
% 0.19/0.45    r2_hidden(sK2(sK1,k1_tarski(k1_xboole_0)),sK1) | spl3_18),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f165,f43])).
% 0.19/0.45  fof(f43,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f28])).
% 0.19/0.45  fof(f166,plain,(
% 0.19/0.45    ~spl3_18 | spl3_17),
% 0.19/0.45    inference(avatar_split_clause,[],[f161,f157,f163])).
% 0.19/0.45  fof(f157,plain,(
% 0.19/0.45    spl3_17 <=> sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.19/0.45  fof(f161,plain,(
% 0.19/0.45    ~r1_xboole_0(sK1,k1_tarski(k1_xboole_0)) | spl3_17),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f159,f47])).
% 0.19/0.45  fof(f47,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.19/0.45    inference(cnf_transformation,[],[f29])).
% 0.19/0.45  fof(f29,plain,(
% 0.19/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.45    inference(nnf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.19/0.45  fof(f159,plain,(
% 0.19/0.45    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | spl3_17),
% 0.19/0.45    inference(avatar_component_clause,[],[f157])).
% 0.19/0.45  fof(f160,plain,(
% 0.19/0.45    ~spl3_17 | spl3_1 | ~spl3_16),
% 0.19/0.45    inference(avatar_split_clause,[],[f155,f151,f57,f157])).
% 0.19/0.45  fof(f57,plain,(
% 0.19/0.45    spl3_1 <=> sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.45  fof(f151,plain,(
% 0.19/0.45    spl3_16 <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.19/0.45  fof(f155,plain,(
% 0.19/0.45    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (spl3_1 | ~spl3_16)),
% 0.19/0.45    inference(superposition,[],[f59,f153])).
% 0.19/0.45  fof(f153,plain,(
% 0.19/0.45    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | ~spl3_16),
% 0.19/0.45    inference(avatar_component_clause,[],[f151])).
% 0.19/0.45  fof(f59,plain,(
% 0.19/0.45    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl3_1),
% 0.19/0.45    inference(avatar_component_clause,[],[f57])).
% 0.19/0.45  fof(f154,plain,(
% 0.19/0.45    spl3_16 | ~spl3_2 | ~spl3_13),
% 0.19/0.45    inference(avatar_split_clause,[],[f149,f127,f62,f151])).
% 0.19/0.45  fof(f62,plain,(
% 0.19/0.45    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.45  fof(f127,plain,(
% 0.19/0.45    spl3_13 <=> k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.19/0.45  fof(f149,plain,(
% 0.19/0.45    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) | (~spl3_2 | ~spl3_13)),
% 0.19/0.45    inference(forward_demodulation,[],[f129,f109])).
% 0.19/0.45  fof(f109,plain,(
% 0.19/0.45    ( ! [X0] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl3_2),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f64,f49])).
% 0.19/0.45  fof(f49,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f23])).
% 0.19/0.45  fof(f23,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.19/0.45  fof(f64,plain,(
% 0.19/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | ~spl3_2),
% 0.19/0.45    inference(avatar_component_clause,[],[f62])).
% 0.19/0.45  fof(f129,plain,(
% 0.19/0.45    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0)) | ~spl3_13),
% 0.19/0.45    inference(avatar_component_clause,[],[f127])).
% 0.19/0.45  fof(f130,plain,(
% 0.19/0.45    spl3_13 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_6 | ~spl3_7 | spl3_8),
% 0.19/0.45    inference(avatar_split_clause,[],[f124,f92,f87,f82,f72,f67,f62,f127])).
% 0.19/0.45  fof(f67,plain,(
% 0.19/0.45    spl3_3 <=> v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.45  fof(f72,plain,(
% 0.19/0.45    spl3_4 <=> v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.45  fof(f82,plain,(
% 0.19/0.45    spl3_6 <=> v1_xboole_0(sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.45  fof(f87,plain,(
% 0.19/0.45    spl3_7 <=> l1_struct_0(sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.45  fof(f92,plain,(
% 0.19/0.45    spl3_8 <=> v2_struct_0(sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.45  fof(f124,plain,(
% 0.19/0.45    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_6 | ~spl3_7 | spl3_8)),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f94,f89,f84,f74,f69,f64,f55])).
% 0.19/0.45  fof(f55,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | v1_xboole_0(X1) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) | v2_struct_0(X0)) )),
% 0.19/0.45    inference(definition_unfolding,[],[f42,f39,f39,f39,f39])).
% 0.19/0.45  fof(f39,plain,(
% 0.19/0.45    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f7])).
% 0.19/0.45  fof(f7,axiom,(
% 0.19/0.45    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.19/0.45  fof(f42,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f20])).
% 0.19/0.45  fof(f20,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.45    inference(flattening,[],[f19])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f8])).
% 0.19/0.45  fof(f8,axiom,(
% 0.19/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).
% 0.19/0.45  fof(f69,plain,(
% 0.19/0.45    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~spl3_3),
% 0.19/0.45    inference(avatar_component_clause,[],[f67])).
% 0.19/0.45  fof(f74,plain,(
% 0.19/0.45    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~spl3_4),
% 0.19/0.45    inference(avatar_component_clause,[],[f72])).
% 0.19/0.45  fof(f84,plain,(
% 0.19/0.45    ~v1_xboole_0(sK1) | spl3_6),
% 0.19/0.45    inference(avatar_component_clause,[],[f82])).
% 0.19/0.45  fof(f89,plain,(
% 0.19/0.45    l1_struct_0(sK0) | ~spl3_7),
% 0.19/0.45    inference(avatar_component_clause,[],[f87])).
% 0.19/0.45  fof(f94,plain,(
% 0.19/0.45    ~v2_struct_0(sK0) | spl3_8),
% 0.19/0.45    inference(avatar_component_clause,[],[f92])).
% 0.19/0.45  fof(f117,plain,(
% 0.19/0.45    ~spl3_11 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_6 | ~spl3_9 | spl3_10),
% 0.19/0.45    inference(avatar_split_clause,[],[f111,f103,f97,f82,f77,f72,f67,f62,f114])).
% 0.19/0.45  fof(f77,plain,(
% 0.19/0.45    spl3_5 <=> v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.45  fof(f97,plain,(
% 0.19/0.45    spl3_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.45  fof(f103,plain,(
% 0.19/0.45    spl3_10 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.45  fof(f111,plain,(
% 0.19/0.45    ~r2_hidden(k1_xboole_0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | spl3_6 | ~spl3_9 | spl3_10)),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f99,f84,f105,f74,f69,f79,f64,f54])).
% 0.19/0.45  fof(f54,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.19/0.45    inference(definition_unfolding,[],[f40,f39,f39,f39,f39])).
% 0.19/0.45  fof(f40,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f16])).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.19/0.45    inference(flattening,[],[f15])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f9])).
% 0.19/0.45  fof(f9,axiom,(
% 0.19/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).
% 0.19/0.45  fof(f79,plain,(
% 0.19/0.45    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~spl3_5),
% 0.19/0.45    inference(avatar_component_clause,[],[f77])).
% 0.19/0.45  fof(f105,plain,(
% 0.19/0.45    ~v1_xboole_0(k2_struct_0(sK0)) | spl3_10),
% 0.19/0.45    inference(avatar_component_clause,[],[f103])).
% 0.19/0.45  fof(f99,plain,(
% 0.19/0.45    v1_xboole_0(k1_xboole_0) | ~spl3_9),
% 0.19/0.45    inference(avatar_component_clause,[],[f97])).
% 0.19/0.45  fof(f106,plain,(
% 0.19/0.45    ~spl3_10 | ~spl3_7 | spl3_8),
% 0.19/0.45    inference(avatar_split_clause,[],[f101,f92,f87,f103])).
% 0.19/0.45  fof(f101,plain,(
% 0.19/0.45    ~v1_xboole_0(k2_struct_0(sK0)) | (~spl3_7 | spl3_8)),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f94,f89,f41])).
% 0.19/0.45  fof(f41,plain,(
% 0.19/0.45    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f18])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.45    inference(flattening,[],[f17])).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,axiom,(
% 0.19/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.19/0.45  fof(f100,plain,(
% 0.19/0.45    spl3_9),
% 0.19/0.45    inference(avatar_split_clause,[],[f38,f97])).
% 0.19/0.45  fof(f38,plain,(
% 0.19/0.45    v1_xboole_0(k1_xboole_0)),
% 0.19/0.45    inference(cnf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    v1_xboole_0(k1_xboole_0)),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.45  fof(f95,plain,(
% 0.19/0.45    ~spl3_8),
% 0.19/0.45    inference(avatar_split_clause,[],[f30,f92])).
% 0.19/0.45  fof(f30,plain,(
% 0.19/0.45    ~v2_struct_0(sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f26])).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f25,f24])).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    ? [X1] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) => (sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.19/0.45    inference(flattening,[],[f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f11])).
% 0.19/0.45  fof(f11,negated_conjecture,(
% 0.19/0.45    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.19/0.45    inference(negated_conjecture,[],[f10])).
% 0.19/0.45  fof(f10,conjecture,(
% 0.19/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 0.19/0.45  fof(f90,plain,(
% 0.19/0.45    spl3_7),
% 0.19/0.45    inference(avatar_split_clause,[],[f31,f87])).
% 0.19/0.45  fof(f31,plain,(
% 0.19/0.45    l1_struct_0(sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f26])).
% 0.19/0.45  fof(f85,plain,(
% 0.19/0.45    ~spl3_6),
% 0.19/0.45    inference(avatar_split_clause,[],[f32,f82])).
% 0.19/0.45  fof(f32,plain,(
% 0.19/0.45    ~v1_xboole_0(sK1)),
% 0.19/0.45    inference(cnf_transformation,[],[f26])).
% 0.19/0.45  fof(f80,plain,(
% 0.19/0.45    spl3_5),
% 0.19/0.45    inference(avatar_split_clause,[],[f53,f77])).
% 0.19/0.45  fof(f53,plain,(
% 0.19/0.45    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.19/0.45    inference(definition_unfolding,[],[f33,f39])).
% 0.19/0.45  fof(f33,plain,(
% 0.19/0.45    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.19/0.45    inference(cnf_transformation,[],[f26])).
% 0.19/0.45  fof(f75,plain,(
% 0.19/0.45    spl3_4),
% 0.19/0.45    inference(avatar_split_clause,[],[f52,f72])).
% 0.19/0.45  fof(f52,plain,(
% 0.19/0.45    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.19/0.45    inference(definition_unfolding,[],[f34,f39])).
% 0.19/0.45  fof(f34,plain,(
% 0.19/0.45    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.19/0.45    inference(cnf_transformation,[],[f26])).
% 0.19/0.45  fof(f70,plain,(
% 0.19/0.45    spl3_3),
% 0.19/0.45    inference(avatar_split_clause,[],[f51,f67])).
% 0.19/0.45  fof(f51,plain,(
% 0.19/0.45    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.19/0.45    inference(definition_unfolding,[],[f35,f39])).
% 0.19/0.45  fof(f35,plain,(
% 0.19/0.45    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.19/0.45    inference(cnf_transformation,[],[f26])).
% 0.19/0.45  fof(f65,plain,(
% 0.19/0.45    spl3_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f50,f62])).
% 0.19/0.45  fof(f50,plain,(
% 0.19/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.19/0.45    inference(definition_unfolding,[],[f36,f39])).
% 0.19/0.45  fof(f36,plain,(
% 0.19/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.19/0.45    inference(cnf_transformation,[],[f26])).
% 0.19/0.45  fof(f60,plain,(
% 0.19/0.45    ~spl3_1),
% 0.19/0.45    inference(avatar_split_clause,[],[f37,f57])).
% 0.19/0.45  fof(f37,plain,(
% 0.19/0.45    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.19/0.45    inference(cnf_transformation,[],[f26])).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (775)------------------------------
% 0.19/0.45  % (775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (775)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (775)Memory used [KB]: 6268
% 0.19/0.45  % (775)Time elapsed: 0.014 s
% 0.19/0.45  % (775)------------------------------
% 0.19/0.45  % (775)------------------------------
% 0.19/0.46  % (785)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.46  % (765)Success in time 0.118 s
%------------------------------------------------------------------------------
