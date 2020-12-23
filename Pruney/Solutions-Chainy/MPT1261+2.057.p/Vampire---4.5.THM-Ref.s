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
% DateTime   : Thu Dec  3 13:11:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 388 expanded)
%              Number of leaves         :   58 ( 176 expanded)
%              Depth                    :   13
%              Number of atoms          :  665 (1248 expanded)
%              Number of equality atoms :  140 ( 282 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f883,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f96,f102,f106,f110,f114,f126,f134,f144,f148,f157,f175,f179,f185,f199,f207,f218,f230,f235,f239,f257,f294,f318,f336,f357,f359,f398,f503,f526,f531,f570,f609,f684,f713,f872,f875,f880,f882])).

fof(f882,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_15
    | ~ spl2_27
    | ~ spl2_31
    | ~ spl2_34
    | ~ spl2_41
    | ~ spl2_56
    | ~ spl2_69 ),
    inference(avatar_contradiction_clause,[],[f881])).

fof(f881,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_15
    | ~ spl2_27
    | ~ spl2_31
    | ~ spl2_34
    | ~ spl2_41
    | ~ spl2_56
    | ~ spl2_69 ),
    inference(subsumption_resolution,[],[f878,f343])).

fof(f343,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_27
    | ~ spl2_31 ),
    inference(unit_resulting_resolution,[],[f81,f76,f86,f276,f229])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) != X1
        | v4_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl2_27
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) != X1
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f276,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f275])).

% (23710)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f275,plain,
    ( spl2_31
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f86,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f76,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f81,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f878,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_15
    | ~ spl2_34
    | ~ spl2_41
    | ~ spl2_56
    | ~ spl2_69 ),
    inference(trivial_inequality_removal,[],[f877])).

fof(f877,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_15
    | ~ spl2_34
    | ~ spl2_41
    | ~ spl2_56
    | ~ spl2_69 ),
    inference(forward_demodulation,[],[f571,f722])).

fof(f722,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_15
    | ~ spl2_41
    | ~ spl2_56
    | ~ spl2_69 ),
    inference(forward_demodulation,[],[f716,f534])).

fof(f534,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_41
    | ~ spl2_56 ),
    inference(unit_resulting_resolution,[],[f356,f530])).

fof(f530,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f529])).

fof(f529,plain,
    ( spl2_56
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f356,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f354])).

% (23718)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f354,plain,
    ( spl2_41
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f716,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_15
    | ~ spl2_69 ),
    inference(superposition,[],[f143,f712])).

fof(f712,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f710])).

fof(f710,plain,
    ( spl2_69
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f143,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl2_15
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f571,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f50,f293])).

fof(f293,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl2_34
  <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f50,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f880,plain,
    ( ~ spl2_15
    | spl2_39
    | ~ spl2_41
    | ~ spl2_56
    | ~ spl2_69 ),
    inference(avatar_contradiction_clause,[],[f879])).

fof(f879,plain,
    ( $false
    | ~ spl2_15
    | spl2_39
    | ~ spl2_41
    | ~ spl2_56
    | ~ spl2_69 ),
    inference(subsumption_resolution,[],[f722,f334])).

fof(f334,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | spl2_39 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl2_39
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f875,plain,
    ( ~ spl2_6
    | ~ spl2_18
    | spl2_31
    | ~ spl2_59
    | ~ spl2_80 ),
    inference(avatar_contradiction_clause,[],[f874])).

fof(f874,plain,
    ( $false
    | ~ spl2_6
    | ~ spl2_18
    | spl2_31
    | ~ spl2_59
    | ~ spl2_80 ),
    inference(subsumption_resolution,[],[f277,f873])).

fof(f873,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_6
    | ~ spl2_18
    | ~ spl2_59
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f871,f664])).

fof(f664,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_6
    | ~ spl2_18
    | ~ spl2_59 ),
    inference(forward_demodulation,[],[f659,f101])).

fof(f101,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl2_6
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f659,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_18
    | ~ spl2_59 ),
    inference(superposition,[],[f156,f569])).

fof(f569,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f567])).

fof(f567,plain,
    ( spl2_59
  <=> k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f156,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl2_18
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f871,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_80 ),
    inference(avatar_component_clause,[],[f869])).

fof(f869,plain,
    ( spl2_80
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).

fof(f277,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_31 ),
    inference(avatar_component_clause,[],[f275])).

fof(f872,plain,
    ( spl2_80
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_26
    | ~ spl2_29
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f273,f254,f237,f216,f84,f79,f869])).

fof(f216,plain,
    ( spl2_26
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f237,plain,
    ( spl2_29
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f254,plain,
    ( spl2_30
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f273,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_26
    | ~ spl2_29
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f263,f248])).

fof(f248,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_29 ),
    inference(unit_resulting_resolution,[],[f81,f86,f238])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f237])).

fof(f263,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_26
    | ~ spl2_30 ),
    inference(unit_resulting_resolution,[],[f86,f256,f217])).

fof(f217,plain,
    ( ! [X2,X0,X1] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f216])).

fof(f256,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f254])).

fof(f713,plain,
    ( spl2_69
    | ~ spl2_34
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f319,f315,f292,f710])).

fof(f315,plain,
    ( spl2_37
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f319,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_34
    | ~ spl2_37 ),
    inference(superposition,[],[f317,f293])).

fof(f317,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f315])).

fof(f684,plain,
    ( spl2_41
    | ~ spl2_39
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f588,f396,f333,f354])).

fof(f396,plain,
    ( spl2_45
  <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f588,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_39
    | ~ spl2_45 ),
    inference(superposition,[],[f397,f335])).

fof(f335,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f333])).

fof(f397,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f396])).

fof(f609,plain,
    ( spl2_40
    | ~ spl2_8
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f585,f333,f108,f347])).

fof(f347,plain,
    ( spl2_40
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f108,plain,
    ( spl2_8
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f585,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_8
    | ~ spl2_39 ),
    inference(superposition,[],[f109,f335])).

fof(f109,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f570,plain,
    ( spl2_59
    | ~ spl2_40
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f508,f501,f347,f567])).

fof(f501,plain,
    ( spl2_54
  <=> ! [X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X1,X2)
        | ~ r1_tarski(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f508,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_40
    | ~ spl2_54 ),
    inference(unit_resulting_resolution,[],[f349,f502])).

fof(f502,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 = k4_xboole_0(X1,X2)
        | ~ r1_tarski(X1,X2) )
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f501])).

fof(f349,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f347])).

fof(f531,plain,
    ( spl2_56
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_45
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f527,f524,f396,f173,f142,f529])).

fof(f173,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f524,plain,
    ( spl2_55
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f527,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_45
    | ~ spl2_55 ),
    inference(forward_demodulation,[],[f525,f421])).

fof(f421,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,X1))
    | ~ spl2_15
    | ~ spl2_19
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f410,f143])).

fof(f410,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))
    | ~ spl2_19
    | ~ spl2_45 ),
    inference(unit_resulting_resolution,[],[f397,f174])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f173])).

fof(f525,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f524])).

fof(f526,plain,
    ( spl2_55
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f191,f177,f173,f524])).

fof(f177,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_19
    | ~ spl2_20 ),
    inference(superposition,[],[f178,f174])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f177])).

fof(f503,plain,
    ( spl2_54
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f167,f146,f132,f112,f104,f100,f501])).

fof(f104,plain,
    ( spl2_7
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f112,plain,
    ( spl2_9
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f132,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f146,plain,
    ( spl2_16
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f167,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 = k4_xboole_0(X1,X2)
        | ~ r1_tarski(X1,X2) )
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f165,f166])).

fof(f166,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f164,f135])).

fof(f135,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(superposition,[],[f113,f101])).

fof(f113,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f164,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)
    | ~ spl2_7
    | ~ spl2_16 ),
    inference(superposition,[],[f147,f105])).

fof(f105,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f147,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f146])).

fof(f165,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1)
        | ~ r1_tarski(X1,X2) )
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(superposition,[],[f147,f133])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f398,plain,
    ( spl2_45
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f139,f124,f108,f396])).

fof(f124,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f139,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f109,f125])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f359,plain,
    ( ~ spl2_2
    | spl2_40
    | ~ spl2_4
    | ~ spl2_3
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f223,f205,f84,f89,f347,f79])).

fof(f89,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f205,plain,
    ( spl2_24
  <=> ! [X1,X0] :
        ( r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f223,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_24 ),
    inference(resolution,[],[f206,f86])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | r1_tarski(k2_tops_1(X0,X1),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f205])).

fof(f357,plain,
    ( spl2_41
    | ~ spl2_12
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f352,f347,f124,f354])).

fof(f352,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_12
    | ~ spl2_40 ),
    inference(unit_resulting_resolution,[],[f349,f125])).

fof(f336,plain,
    ( ~ spl2_3
    | spl2_39
    | ~ spl2_5
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f194,f183,f93,f333,f84])).

fof(f93,plain,
    ( spl2_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f183,plain,
    ( spl2_21
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f194,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5
    | ~ spl2_21 ),
    inference(superposition,[],[f184,f95])).

fof(f95,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f184,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f183])).

fof(f318,plain,
    ( spl2_37
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f243,f233,f84,f79,f315])).

fof(f233,plain,
    ( spl2_28
  <=> ! [X1,X0] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f243,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(unit_resulting_resolution,[],[f81,f86,f234])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f233])).

fof(f294,plain,
    ( spl2_34
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f193,f183,f84,f292])).

fof(f193,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(unit_resulting_resolution,[],[f86,f184])).

fof(f257,plain,
    ( spl2_30
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f208,f197,f84,f79,f254])).

fof(f197,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f208,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f81,f86,f198])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f197])).

fof(f239,plain,(
    spl2_29 ),
    inference(avatar_split_clause,[],[f53,f237])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f235,plain,(
    spl2_28 ),
    inference(avatar_split_clause,[],[f52,f233])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f230,plain,(
    spl2_27 ),
    inference(avatar_split_clause,[],[f55,f228])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f218,plain,(
    spl2_26 ),
    inference(avatar_split_clause,[],[f72,f216])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f207,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f56,f205])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f199,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f68,f197])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f185,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f71,f183])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f179,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f67,f177])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f175,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f66,f173])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f157,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f64,f155])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f148,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f63,f146])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f144,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f62,f142])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f134,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f65,f132])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f126,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f70,f124])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f114,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f59,f112])).

fof(f59,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f110,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f58,f108])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f106,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f57,f104])).

fof(f57,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f102,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f51,f100])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f96,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f49,f93,f89])).

fof(f49,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f48,f84])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f47,f79])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f46,f74])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:24:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (23711)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (23712)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (23719)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (23720)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (23716)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (23717)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (23705)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (23709)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (23708)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (23714)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (23706)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (23713)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.53  % (23708)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f883,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f77,f82,f87,f96,f102,f106,f110,f114,f126,f134,f144,f148,f157,f175,f179,f185,f199,f207,f218,f230,f235,f239,f257,f294,f318,f336,f357,f359,f398,f503,f526,f531,f570,f609,f684,f713,f872,f875,f880,f882])).
% 0.22/0.54  fof(f882,plain,(
% 0.22/0.54    ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_15 | ~spl2_27 | ~spl2_31 | ~spl2_34 | ~spl2_41 | ~spl2_56 | ~spl2_69),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f881])).
% 0.22/0.54  fof(f881,plain,(
% 0.22/0.54    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_15 | ~spl2_27 | ~spl2_31 | ~spl2_34 | ~spl2_41 | ~spl2_56 | ~spl2_69)),
% 0.22/0.54    inference(subsumption_resolution,[],[f878,f343])).
% 0.22/0.54  fof(f343,plain,(
% 0.22/0.54    v4_pre_topc(sK1,sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_27 | ~spl2_31)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f81,f76,f86,f276,f229])).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_27),
% 0.22/0.54    inference(avatar_component_clause,[],[f228])).
% 0.22/0.54  fof(f228,plain,(
% 0.22/0.54    spl2_27 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.22/0.54  fof(f276,plain,(
% 0.22/0.54    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_31),
% 0.22/0.54    inference(avatar_component_clause,[],[f275])).
% 0.22/0.54  % (23710)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.54  fof(f275,plain,(
% 0.22/0.54    spl2_31 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    v2_pre_topc(sK0) | ~spl2_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    spl2_1 <=> v2_pre_topc(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    l1_pre_topc(sK0) | ~spl2_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    spl2_2 <=> l1_pre_topc(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.54  fof(f878,plain,(
% 0.22/0.54    ~v4_pre_topc(sK1,sK0) | (~spl2_15 | ~spl2_34 | ~spl2_41 | ~spl2_56 | ~spl2_69)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f877])).
% 0.22/0.54  fof(f877,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | (~spl2_15 | ~spl2_34 | ~spl2_41 | ~spl2_56 | ~spl2_69)),
% 0.22/0.54    inference(forward_demodulation,[],[f571,f722])).
% 0.22/0.54  fof(f722,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_15 | ~spl2_41 | ~spl2_56 | ~spl2_69)),
% 0.22/0.54    inference(forward_demodulation,[],[f716,f534])).
% 0.22/0.54  fof(f534,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_41 | ~spl2_56)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f356,f530])).
% 0.22/0.54  fof(f530,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_56),
% 0.22/0.54    inference(avatar_component_clause,[],[f529])).
% 0.22/0.54  fof(f529,plain,(
% 0.22/0.54    spl2_56 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 0.22/0.54  fof(f356,plain,(
% 0.22/0.54    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_41),
% 0.22/0.54    inference(avatar_component_clause,[],[f354])).
% 0.22/0.54  % (23718)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.54  fof(f354,plain,(
% 0.22/0.54    spl2_41 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 0.22/0.54  fof(f716,plain,(
% 0.22/0.54    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_15 | ~spl2_69)),
% 0.22/0.54    inference(superposition,[],[f143,f712])).
% 0.22/0.54  fof(f712,plain,(
% 0.22/0.54    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_69),
% 0.22/0.54    inference(avatar_component_clause,[],[f710])).
% 0.22/0.54  fof(f710,plain,(
% 0.22/0.54    spl2_69 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_15),
% 0.22/0.54    inference(avatar_component_clause,[],[f142])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    spl2_15 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.54  fof(f571,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~spl2_34),
% 0.22/0.54    inference(forward_demodulation,[],[f50,f293])).
% 0.22/0.54  fof(f293,plain,(
% 0.22/0.54    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl2_34),
% 0.22/0.54    inference(avatar_component_clause,[],[f292])).
% 0.22/0.54  fof(f292,plain,(
% 0.22/0.54    spl2_34 <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f21])).
% 0.22/0.54  fof(f21,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.22/0.54  fof(f880,plain,(
% 0.22/0.54    ~spl2_15 | spl2_39 | ~spl2_41 | ~spl2_56 | ~spl2_69),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f879])).
% 0.22/0.54  fof(f879,plain,(
% 0.22/0.54    $false | (~spl2_15 | spl2_39 | ~spl2_41 | ~spl2_56 | ~spl2_69)),
% 0.22/0.54    inference(subsumption_resolution,[],[f722,f334])).
% 0.22/0.54  fof(f334,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | spl2_39),
% 0.22/0.54    inference(avatar_component_clause,[],[f333])).
% 0.22/0.54  fof(f333,plain,(
% 0.22/0.54    spl2_39 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.22/0.54  fof(f875,plain,(
% 0.22/0.54    ~spl2_6 | ~spl2_18 | spl2_31 | ~spl2_59 | ~spl2_80),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f874])).
% 0.22/0.54  fof(f874,plain,(
% 0.22/0.54    $false | (~spl2_6 | ~spl2_18 | spl2_31 | ~spl2_59 | ~spl2_80)),
% 0.22/0.54    inference(subsumption_resolution,[],[f277,f873])).
% 0.22/0.54  fof(f873,plain,(
% 0.22/0.54    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_6 | ~spl2_18 | ~spl2_59 | ~spl2_80)),
% 0.22/0.54    inference(forward_demodulation,[],[f871,f664])).
% 0.22/0.54  fof(f664,plain,(
% 0.22/0.54    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_6 | ~spl2_18 | ~spl2_59)),
% 0.22/0.54    inference(forward_demodulation,[],[f659,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f100])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    spl2_6 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.54  fof(f659,plain,(
% 0.22/0.54    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_xboole_0) | (~spl2_18 | ~spl2_59)),
% 0.22/0.54    inference(superposition,[],[f156,f569])).
% 0.22/0.54  fof(f569,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_59),
% 0.22/0.54    inference(avatar_component_clause,[],[f567])).
% 0.22/0.54  fof(f567,plain,(
% 0.22/0.54    spl2_59 <=> k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) ) | ~spl2_18),
% 0.22/0.54    inference(avatar_component_clause,[],[f155])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    spl2_18 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.54  fof(f871,plain,(
% 0.22/0.54    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_80),
% 0.22/0.54    inference(avatar_component_clause,[],[f869])).
% 0.22/0.54  fof(f869,plain,(
% 0.22/0.54    spl2_80 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).
% 0.22/0.54  fof(f277,plain,(
% 0.22/0.54    sK1 != k2_pre_topc(sK0,sK1) | spl2_31),
% 0.22/0.54    inference(avatar_component_clause,[],[f275])).
% 0.22/0.54  fof(f872,plain,(
% 0.22/0.54    spl2_80 | ~spl2_2 | ~spl2_3 | ~spl2_26 | ~spl2_29 | ~spl2_30),
% 0.22/0.54    inference(avatar_split_clause,[],[f273,f254,f237,f216,f84,f79,f869])).
% 0.22/0.54  fof(f216,plain,(
% 0.22/0.54    spl2_26 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.54  fof(f237,plain,(
% 0.22/0.54    spl2_29 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.22/0.54  fof(f254,plain,(
% 0.22/0.54    spl2_30 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.22/0.54  fof(f273,plain,(
% 0.22/0.54    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_26 | ~spl2_29 | ~spl2_30)),
% 0.22/0.54    inference(forward_demodulation,[],[f263,f248])).
% 0.22/0.54  fof(f248,plain,(
% 0.22/0.54    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_29)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f81,f86,f238])).
% 0.22/0.54  fof(f238,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_29),
% 0.22/0.54    inference(avatar_component_clause,[],[f237])).
% 0.22/0.54  fof(f263,plain,(
% 0.22/0.54    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_26 | ~spl2_30)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f86,f256,f217])).
% 0.22/0.54  fof(f217,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_26),
% 0.22/0.54    inference(avatar_component_clause,[],[f216])).
% 0.22/0.54  fof(f256,plain,(
% 0.22/0.54    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_30),
% 0.22/0.54    inference(avatar_component_clause,[],[f254])).
% 0.22/0.54  fof(f713,plain,(
% 0.22/0.54    spl2_69 | ~spl2_34 | ~spl2_37),
% 0.22/0.54    inference(avatar_split_clause,[],[f319,f315,f292,f710])).
% 0.22/0.54  fof(f315,plain,(
% 0.22/0.54    spl2_37 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.22/0.54  fof(f319,plain,(
% 0.22/0.54    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_34 | ~spl2_37)),
% 0.22/0.54    inference(superposition,[],[f317,f293])).
% 0.22/0.54  fof(f317,plain,(
% 0.22/0.54    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_37),
% 0.22/0.54    inference(avatar_component_clause,[],[f315])).
% 0.22/0.54  fof(f684,plain,(
% 0.22/0.54    spl2_41 | ~spl2_39 | ~spl2_45),
% 0.22/0.54    inference(avatar_split_clause,[],[f588,f396,f333,f354])).
% 0.22/0.54  fof(f396,plain,(
% 0.22/0.54    spl2_45 <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.22/0.54  fof(f588,plain,(
% 0.22/0.54    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl2_39 | ~spl2_45)),
% 0.22/0.54    inference(superposition,[],[f397,f335])).
% 0.22/0.54  fof(f335,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_39),
% 0.22/0.54    inference(avatar_component_clause,[],[f333])).
% 0.22/0.54  fof(f397,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl2_45),
% 0.22/0.54    inference(avatar_component_clause,[],[f396])).
% 0.22/0.54  fof(f609,plain,(
% 0.22/0.54    spl2_40 | ~spl2_8 | ~spl2_39),
% 0.22/0.54    inference(avatar_split_clause,[],[f585,f333,f108,f347])).
% 0.22/0.54  fof(f347,plain,(
% 0.22/0.54    spl2_40 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    spl2_8 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.54  fof(f585,plain,(
% 0.22/0.54    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_8 | ~spl2_39)),
% 0.22/0.54    inference(superposition,[],[f109,f335])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f108])).
% 0.22/0.54  fof(f570,plain,(
% 0.22/0.54    spl2_59 | ~spl2_40 | ~spl2_54),
% 0.22/0.54    inference(avatar_split_clause,[],[f508,f501,f347,f567])).
% 0.22/0.54  fof(f501,plain,(
% 0.22/0.54    spl2_54 <=> ! [X1,X2] : (k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 0.22/0.54  fof(f508,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | (~spl2_40 | ~spl2_54)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f349,f502])).
% 0.22/0.54  fof(f502,plain,(
% 0.22/0.54    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) ) | ~spl2_54),
% 0.22/0.54    inference(avatar_component_clause,[],[f501])).
% 0.22/0.54  fof(f349,plain,(
% 0.22/0.54    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_40),
% 0.22/0.54    inference(avatar_component_clause,[],[f347])).
% 0.22/0.54  fof(f531,plain,(
% 0.22/0.54    spl2_56 | ~spl2_15 | ~spl2_19 | ~spl2_45 | ~spl2_55),
% 0.22/0.54    inference(avatar_split_clause,[],[f527,f524,f396,f173,f142,f529])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    spl2_19 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.54  fof(f524,plain,(
% 0.22/0.54    spl2_55 <=> ! [X1,X0] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 0.22/0.54  fof(f527,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_15 | ~spl2_19 | ~spl2_45 | ~spl2_55)),
% 0.22/0.54    inference(forward_demodulation,[],[f525,f421])).
% 0.22/0.54  fof(f421,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,X1))) ) | (~spl2_15 | ~spl2_19 | ~spl2_45)),
% 0.22/0.54    inference(forward_demodulation,[],[f410,f143])).
% 0.22/0.54  fof(f410,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))) ) | (~spl2_19 | ~spl2_45)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f397,f174])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_19),
% 0.22/0.54    inference(avatar_component_clause,[],[f173])).
% 0.22/0.54  fof(f525,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_55),
% 0.22/0.54    inference(avatar_component_clause,[],[f524])).
% 0.22/0.54  fof(f526,plain,(
% 0.22/0.54    spl2_55 | ~spl2_19 | ~spl2_20),
% 0.22/0.54    inference(avatar_split_clause,[],[f191,f177,f173,f524])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    spl2_20 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_19 | ~spl2_20)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f188])).
% 0.22/0.54  fof(f188,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_19 | ~spl2_20)),
% 0.22/0.54    inference(superposition,[],[f178,f174])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_20),
% 0.22/0.54    inference(avatar_component_clause,[],[f177])).
% 0.22/0.54  fof(f503,plain,(
% 0.22/0.54    spl2_54 | ~spl2_6 | ~spl2_7 | ~spl2_9 | ~spl2_14 | ~spl2_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f167,f146,f132,f112,f104,f100,f501])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    spl2_7 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    spl2_9 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    spl2_14 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    spl2_16 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) ) | (~spl2_6 | ~spl2_7 | ~spl2_9 | ~spl2_14 | ~spl2_16)),
% 0.22/0.54    inference(forward_demodulation,[],[f165,f166])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | (~spl2_6 | ~spl2_7 | ~spl2_9 | ~spl2_16)),
% 0.22/0.54    inference(forward_demodulation,[],[f164,f135])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl2_6 | ~spl2_9)),
% 0.22/0.54    inference(superposition,[],[f113,f101])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl2_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f112])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) ) | (~spl2_7 | ~spl2_16)),
% 0.22/0.54    inference(superposition,[],[f147,f105])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl2_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f104])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f146])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1) | ~r1_tarski(X1,X2)) ) | (~spl2_14 | ~spl2_16)),
% 0.22/0.54    inference(superposition,[],[f147,f133])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f132])).
% 0.22/0.54  fof(f398,plain,(
% 0.22/0.54    spl2_45 | ~spl2_8 | ~spl2_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f139,f124,f108,f396])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    spl2_12 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | (~spl2_8 | ~spl2_12)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f109,f125])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f124])).
% 0.22/0.54  fof(f359,plain,(
% 0.22/0.54    ~spl2_2 | spl2_40 | ~spl2_4 | ~spl2_3 | ~spl2_24),
% 0.22/0.54    inference(avatar_split_clause,[],[f223,f205,f84,f89,f347,f79])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    spl2_24 <=> ! [X1,X0] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.54  fof(f223,plain,(
% 0.22/0.54    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_24)),
% 0.22/0.54    inference(resolution,[],[f206,f86])).
% 0.22/0.54  fof(f206,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) ) | ~spl2_24),
% 0.22/0.54    inference(avatar_component_clause,[],[f205])).
% 0.22/0.54  fof(f357,plain,(
% 0.22/0.54    spl2_41 | ~spl2_12 | ~spl2_40),
% 0.22/0.54    inference(avatar_split_clause,[],[f352,f347,f124,f354])).
% 0.22/0.54  fof(f352,plain,(
% 0.22/0.54    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl2_12 | ~spl2_40)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f349,f125])).
% 0.22/0.54  fof(f336,plain,(
% 0.22/0.54    ~spl2_3 | spl2_39 | ~spl2_5 | ~spl2_21),
% 0.22/0.54    inference(avatar_split_clause,[],[f194,f183,f93,f333,f84])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    spl2_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    spl2_21 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_5 | ~spl2_21)),
% 0.22/0.54    inference(superposition,[],[f184,f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f93])).
% 0.22/0.54  fof(f184,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_21),
% 0.22/0.54    inference(avatar_component_clause,[],[f183])).
% 0.22/0.54  fof(f318,plain,(
% 0.22/0.54    spl2_37 | ~spl2_2 | ~spl2_3 | ~spl2_28),
% 0.22/0.54    inference(avatar_split_clause,[],[f243,f233,f84,f79,f315])).
% 0.22/0.54  fof(f233,plain,(
% 0.22/0.54    spl2_28 <=> ! [X1,X0] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_28)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f81,f86,f234])).
% 0.22/0.54  fof(f234,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_28),
% 0.22/0.54    inference(avatar_component_clause,[],[f233])).
% 0.22/0.54  fof(f294,plain,(
% 0.22/0.54    spl2_34 | ~spl2_3 | ~spl2_21),
% 0.22/0.54    inference(avatar_split_clause,[],[f193,f183,f84,f292])).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | (~spl2_3 | ~spl2_21)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f86,f184])).
% 0.22/0.54  fof(f257,plain,(
% 0.22/0.54    spl2_30 | ~spl2_2 | ~spl2_3 | ~spl2_22),
% 0.22/0.54    inference(avatar_split_clause,[],[f208,f197,f84,f79,f254])).
% 0.22/0.54  fof(f197,plain,(
% 0.22/0.54    spl2_22 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.54  fof(f208,plain,(
% 0.22/0.54    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3 | ~spl2_22)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f81,f86,f198])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_22),
% 0.22/0.54    inference(avatar_component_clause,[],[f197])).
% 0.22/0.54  fof(f239,plain,(
% 0.22/0.54    spl2_29),
% 0.22/0.54    inference(avatar_split_clause,[],[f53,f237])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.22/0.54  fof(f235,plain,(
% 0.22/0.54    spl2_28),
% 0.22/0.54    inference(avatar_split_clause,[],[f52,f233])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 0.22/0.54  fof(f230,plain,(
% 0.22/0.54    spl2_27),
% 0.22/0.54    inference(avatar_split_clause,[],[f55,f228])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.54  fof(f218,plain,(
% 0.22/0.54    spl2_26),
% 0.22/0.54    inference(avatar_split_clause,[],[f72,f216])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(flattening,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.54  fof(f207,plain,(
% 0.22/0.54    spl2_24),
% 0.22/0.54    inference(avatar_split_clause,[],[f56,f205])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    spl2_22),
% 0.22/0.54    inference(avatar_split_clause,[],[f68,f197])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,axiom,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    spl2_21),
% 0.22/0.54    inference(avatar_split_clause,[],[f71,f183])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    spl2_20),
% 0.22/0.54    inference(avatar_split_clause,[],[f67,f177])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    spl2_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f66,f173])).
% 1.42/0.54  fof(f66,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f33])).
% 1.42/0.54  fof(f33,plain,(
% 1.42/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.42/0.54    inference(ennf_transformation,[],[f10])).
% 1.42/0.54  fof(f10,axiom,(
% 1.42/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.42/0.54  fof(f157,plain,(
% 1.42/0.54    spl2_18),
% 1.42/0.54    inference(avatar_split_clause,[],[f64,f155])).
% 1.42/0.54  fof(f64,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f6])).
% 1.42/0.54  fof(f6,axiom,(
% 1.42/0.54    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.42/0.54  fof(f148,plain,(
% 1.42/0.54    spl2_16),
% 1.42/0.54    inference(avatar_split_clause,[],[f63,f146])).
% 1.42/0.54  fof(f63,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f2])).
% 1.42/0.54  fof(f2,axiom,(
% 1.42/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.42/0.54  fof(f144,plain,(
% 1.42/0.54    spl2_15),
% 1.42/0.54    inference(avatar_split_clause,[],[f62,f142])).
% 1.42/0.54  fof(f62,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f8])).
% 1.42/0.54  fof(f8,axiom,(
% 1.42/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.42/0.54  fof(f134,plain,(
% 1.42/0.54    spl2_14),
% 1.42/0.54    inference(avatar_split_clause,[],[f65,f132])).
% 1.42/0.54  fof(f65,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f32])).
% 1.42/0.54  fof(f32,plain,(
% 1.42/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.42/0.54    inference(ennf_transformation,[],[f4])).
% 1.42/0.54  fof(f4,axiom,(
% 1.42/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.42/0.54  fof(f126,plain,(
% 1.42/0.54    spl2_12),
% 1.42/0.54    inference(avatar_split_clause,[],[f70,f124])).
% 1.42/0.54  fof(f70,plain,(
% 1.42/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f45,plain,(
% 1.42/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.42/0.54    inference(nnf_transformation,[],[f15])).
% 1.42/0.54  fof(f15,axiom,(
% 1.42/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.42/0.54  fof(f114,plain,(
% 1.42/0.54    spl2_9),
% 1.42/0.54    inference(avatar_split_clause,[],[f59,f112])).
% 1.42/0.54  fof(f59,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f7])).
% 1.42/0.54  fof(f7,axiom,(
% 1.42/0.54    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.42/0.54  fof(f110,plain,(
% 1.42/0.54    spl2_8),
% 1.42/0.54    inference(avatar_split_clause,[],[f58,f108])).
% 1.42/0.54  fof(f58,plain,(
% 1.42/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f5])).
% 1.42/0.54  fof(f5,axiom,(
% 1.42/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.42/0.54  fof(f106,plain,(
% 1.42/0.54    spl2_7),
% 1.42/0.54    inference(avatar_split_clause,[],[f57,f104])).
% 1.42/0.54  fof(f57,plain,(
% 1.42/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.42/0.54    inference(cnf_transformation,[],[f23])).
% 1.42/0.54  fof(f23,plain,(
% 1.42/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.42/0.54    inference(rectify,[],[f1])).
% 1.42/0.54  fof(f1,axiom,(
% 1.42/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.42/0.54  fof(f102,plain,(
% 1.42/0.54    spl2_6),
% 1.42/0.54    inference(avatar_split_clause,[],[f51,f100])).
% 1.42/0.54  fof(f51,plain,(
% 1.42/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.42/0.54    inference(cnf_transformation,[],[f3])).
% 1.42/0.54  fof(f3,axiom,(
% 1.42/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.42/0.54  fof(f96,plain,(
% 1.42/0.54    spl2_4 | spl2_5),
% 1.42/0.54    inference(avatar_split_clause,[],[f49,f93,f89])).
% 1.42/0.54  fof(f49,plain,(
% 1.42/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.42/0.54    inference(cnf_transformation,[],[f44])).
% 1.42/0.54  fof(f87,plain,(
% 1.42/0.54    spl2_3),
% 1.42/0.54    inference(avatar_split_clause,[],[f48,f84])).
% 1.42/0.54  fof(f48,plain,(
% 1.42/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.42/0.54    inference(cnf_transformation,[],[f44])).
% 1.42/0.54  fof(f82,plain,(
% 1.42/0.54    spl2_2),
% 1.42/0.54    inference(avatar_split_clause,[],[f47,f79])).
% 1.42/0.54  fof(f47,plain,(
% 1.42/0.54    l1_pre_topc(sK0)),
% 1.42/0.54    inference(cnf_transformation,[],[f44])).
% 1.42/0.54  fof(f77,plain,(
% 1.42/0.54    spl2_1),
% 1.42/0.54    inference(avatar_split_clause,[],[f46,f74])).
% 1.42/0.54  fof(f46,plain,(
% 1.42/0.54    v2_pre_topc(sK0)),
% 1.42/0.54    inference(cnf_transformation,[],[f44])).
% 1.42/0.54  % SZS output end Proof for theBenchmark
% 1.42/0.54  % (23708)------------------------------
% 1.42/0.54  % (23708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (23708)Termination reason: Refutation
% 1.42/0.54  
% 1.42/0.54  % (23708)Memory used [KB]: 6780
% 1.42/0.54  % (23708)Time elapsed: 0.090 s
% 1.42/0.54  % (23708)------------------------------
% 1.42/0.54  % (23708)------------------------------
% 1.42/0.54  % (23702)Success in time 0.171 s
%------------------------------------------------------------------------------
